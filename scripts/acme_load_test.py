from __future__ import annotations

import asyncio
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from scripts import acme_load


class FixedRandom:
    def __init__(self, pick: int) -> None:
        self.pick = pick

    def randrange(self, stop: int) -> int:
        assert stop == 100
        return self.pick


class PeerRecordingWidgetService(acme_load.service_pb2_grpc.WidgetServiceServicer):
    def __init__(self) -> None:
        self.peers: set[str] = set()

    async def GetWidget(self, request, context):  # noqa: N802
        self.peers.add(context.peer())
        return acme_load.widgets_pb2.WidgetResponse()


class AcmeLoadTest(unittest.TestCase):
    def test_operation_weight_boundaries_are_unchanged(self) -> None:
        cases = {
            0: "get",
            54: "get",
            55: "list",
            74: "list",
            75: "update",
            89: "update",
            90: "create",
            97: "create",
            98: "delete",
            99: "delete",
        }
        for pick, expected in cases.items():
            with self.subTest(pick=pick):
                self.assertEqual(acme_load.choose_operation(FixedRandom(pick)), expected)

    def test_histogram_bucket_is_a_tight_upper_bound(self) -> None:
        for latency_ns in [0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 999, 10**9]:
            with self.subTest(latency_ns=latency_ns):
                index = acme_load.latency_bucket_index(latency_ns)
                upper = acme_load.latency_bucket_upper_bound(index)
                self.assertGreaterEqual(upper, latency_ns)
                self.assertLessEqual(upper, max(31, latency_ns * 1.03125))

    def test_histogram_quantiles_use_nearest_rank(self) -> None:
        histogram = acme_load.LatencyHistogram()
        for latency_ns in range(1, 101):
            histogram.record(latency_ns)
        self.assertGreaterEqual(histogram.quantile_ns(0.95), 95)
        self.assertLessEqual(histogram.quantile_ns(0.95), 98)
        self.assertGreaterEqual(histogram.quantile_ns(0.99), 99)
        self.assertLessEqual(histogram.quantile_ns(0.99), 102)

    def test_multi_channel_options_force_distinct_subchannel_pools(self) -> None:
        self.assertEqual(acme_load.channel_options(1), ())
        with mock.patch.object(
            acme_load.grpc.aio,
            "insecure_channel",
        ) as insecure_channel:
            acme_load.make_channels("localhost:50062", 1)
        insecure_channel.assert_called_once_with("localhost:50062")

        options = dict(acme_load.channel_options(2))
        self.assertEqual(options["grpc.use_local_subchannel_pool"], 1)
        with mock.patch.object(
            acme_load.grpc.aio,
            "insecure_channel",
        ) as insecure_channel:
            acme_load.make_channels("localhost:50062", 2)
        self.assertEqual(insecure_channel.call_count, 2)
        for call in insecure_channel.call_args_list:
            self.assertEqual(
                dict(call.kwargs["options"])["grpc.use_local_subchannel_pool"],
                1,
            )
        self.assertEqual(
            [acme_load.worker_channel_index(worker, 3) for worker in range(8)],
            [0, 1, 2, 0, 1, 2, 0, 1],
        )

    def test_multi_channel_mode_uses_distinct_tcp_peers(self) -> None:
        async def exercise_channels() -> set[str]:
            service = PeerRecordingWidgetService()
            server = acme_load.grpc.aio.server()
            acme_load.service_pb2_grpc.add_WidgetServiceServicer_to_server(
                service,
                server,
            )
            port = server.add_insecure_port("127.0.0.1:0")
            await server.start()
            channels = acme_load.make_channels(f"127.0.0.1:{port}", 2)
            try:
                await asyncio.gather(*(channel.channel_ready() for channel in channels))
                stubs = [
                    acme_load.service_pb2_grpc.WidgetServiceStub(channel)
                    for channel in channels
                ]
                await asyncio.gather(*(
                    stub.GetWidget(acme_load.authz_pb2.CheckedGetWidgetRequest())
                    for stub in stubs
                ))
            finally:
                await asyncio.gather(*(channel.close() for channel in channels))
                await server.stop(0)
            return service.peers

        peers = asyncio.run(exercise_channels())
        self.assertEqual(len(peers), 2, peers)

    def test_channel_sweep_and_warmup_parse(self) -> None:
        args = acme_load.parse_args([
            "--no-manage-stack",
            "--duration", "1",
            "--warmup", "0.25",
            "--concurrency", "8",
            "--channels", "1,2,4,8",
            "--random-seed", "17",
        ])
        self.assertEqual(args.channels, (1, 2, 4, 8))
        self.assertEqual(args.warmup, 0.25)

    def test_server_binary_override_is_resolved_and_fingerprinted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory, "server")
            binary.write_bytes(b"candidate-server")
            binary.chmod(0o755)
            args = acme_load.parse_args([
                "--duration", "1",
                "--warmup", "0",
                "--concurrency", "1",
                "--random-seed", "17",
                "--server-binary", str(binary),
            ])
            self.assertEqual(args.server_binary, str(binary.resolve()))
            args.resolved_server_binary = args.server_binary
            metadata = acme_load.result_document(args, [])["server_binary"]
        self.assertEqual(metadata["size_bytes"], len(b"candidate-server"))
        self.assertEqual(
            metadata["sha256"],
            "c19a2d92eedae6fd582d76eaf4e0af30af5f0e7d7e4b0b4cbc8a2d47f0fca86b",
        )

    def test_phase_document_separates_attempts_and_successes(self) -> None:
        results = acme_load.Results()
        results.attempted["get"] = 2
        results.successful["get"] = 1
        results.failures["DEADLINE_EXCEEDED"] = 1
        results.latency["get"].record(1_000_000)
        results.latency["get"].record(2_000_000)
        document = acme_load.phase_document(
            acme_load.PhaseResult(2.0, 0.5, results),
        )
        self.assertEqual(document["counts"]["attempted"], 2)
        self.assertEqual(document["counts"]["successful"], 1)
        self.assertEqual(document["counts"]["failed"], 1)
        self.assertEqual(document["client_cpu_utilization_percent"], 25.0)

    def test_machine_result_is_valid_json(self) -> None:
        args = acme_load.parse_args([
            "--no-manage-stack",
            "--duration", "1",
            "--warmup", "0",
            "--concurrency", "1",
            "--random-seed", "17",
        ])
        document = acme_load.result_document(args, [])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory, "result.json")
            acme_load.write_json_result(str(output), document)
            decoded = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(decoded["schema_version"], 1)
        self.assertEqual(decoded["configuration"]["operation_weights_percent"], {
            "create": 8,
            "delete": 2,
            "get": 55,
            "list": 20,
            "update": 15,
        })


if __name__ == "__main__":
    unittest.main()
