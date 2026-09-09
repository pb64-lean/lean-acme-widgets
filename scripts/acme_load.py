#!/usr/bin/env python3
"""Persistent-channel randomized CRUD benchmark for Acme Widgets."""

from __future__ import annotations

import argparse
import asyncio
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import socket
import subprocess
import sys
import tempfile
import time
from typing import Any, Sequence

import grpc
from proto import service_pb2_grpc
from proto import widgets_pb2
from python.runfiles import runfiles


AUTH_METADATA = (("authorization", "Bearer acme-editor-7"),)
OPERATIONS = ("get", "list", "update", "create", "delete")
OPERATION_WEIGHTS = {
    "get": 55,
    "list": 20,
    "update": 15,
    "create": 8,
    "delete": 2,
}
LOCAL_SOURCE_REPOSITORIES = (
    "lean-acme-widgets",
    "rules_lean",
    "grpc-lean",
    "protovalidate-lean",
    "tls13-lean",
    "pg-lean",
    "lean-pgx",
)

# The histogram keeps 32 buckets per power of two after exact 0--31 ns
# buckets. Recording is one bit_length, shift, and list increment; quantiles
# are computed only after a phase. The upper-bound estimate is within one
# bucket (at most 3.125%) of the recorded latency.
HISTOGRAM_SUB_BUCKET_BITS = 5
HISTOGRAM_SUB_BUCKETS = 1 << HISTOGRAM_SUB_BUCKET_BITS
HISTOGRAM_BUCKET_COUNT = 2048


def latency_bucket_index(latency_ns: int) -> int:
    if latency_ns < HISTOGRAM_SUB_BUCKETS:
        return max(latency_ns, 0)
    magnitude = latency_ns.bit_length() - 1
    shift = magnitude - HISTOGRAM_SUB_BUCKET_BITS
    return (
        HISTOGRAM_SUB_BUCKETS
        + shift * HISTOGRAM_SUB_BUCKETS
        + (latency_ns >> shift)
        - HISTOGRAM_SUB_BUCKETS
    )


def latency_bucket_upper_bound(index: int) -> int:
    if index < HISTOGRAM_SUB_BUCKETS:
        return index
    offset = index - HISTOGRAM_SUB_BUCKETS
    shift, sub_bucket_offset = divmod(offset, HISTOGRAM_SUB_BUCKETS)
    sub_bucket = HISTOGRAM_SUB_BUCKETS + sub_bucket_offset
    return ((sub_bucket + 1) << shift) - 1


@dataclass
class LatencyHistogram:
    buckets: list[int] = field(
        default_factory=lambda: [0] * HISTOGRAM_BUCKET_COUNT,
    )
    count: int = 0
    total_ns: int = 0
    maximum_ns: int = 0

    def record(self, latency_ns: int) -> None:
        index = latency_bucket_index(latency_ns)
        if index >= len(self.buckets):
            self.buckets.extend([0] * (index + 1 - len(self.buckets)))
        self.buckets[index] += 1
        self.count += 1
        self.total_ns += latency_ns
        self.maximum_ns = max(self.maximum_ns, latency_ns)

    def merge(self, other: "LatencyHistogram") -> None:
        if len(other.buckets) > len(self.buckets):
            self.buckets.extend([0] * (len(other.buckets) - len(self.buckets)))
        for index, count in enumerate(other.buckets):
            self.buckets[index] += count
        self.count += other.count
        self.total_ns += other.total_ns
        self.maximum_ns = max(self.maximum_ns, other.maximum_ns)

    def quantile_ns(self, quantile: float) -> int:
        if self.count == 0:
            return 0
        rank = max(1, math.ceil(quantile * self.count))
        seen = 0
        for index, count in enumerate(self.buckets):
            seen += count
            if seen >= rank:
                return latency_bucket_upper_bound(index)
        raise AssertionError("latency histogram count does not match its buckets")

    def as_milliseconds(self) -> dict[str, float | str]:
        return {
            "scope": "all_attempts",
            "mean": self.total_ns / self.count / 1_000_000 if self.count else 0.0,
            "p95": self.quantile_ns(0.95) / 1_000_000,
            "p99": self.quantile_ns(0.99) / 1_000_000,
            "max": self.maximum_ns / 1_000_000,
        }


@dataclass
class Results:
    attempted: Counter[str] = field(default_factory=Counter)
    successful: Counter[str] = field(default_factory=Counter)
    failures: Counter[str] = field(default_factory=Counter)
    latency: dict[str, LatencyHistogram] = field(
        default_factory=lambda: {name: LatencyHistogram() for name in OPERATIONS},
    )

    def record(self, operation: str, started_ns: int, failure: str | None) -> None:
        self.attempted[operation] += 1
        self.latency[operation].record(time.monotonic_ns() - started_ns)
        if failure is None:
            self.successful[operation] += 1
        else:
            self.failures[failure] += 1

    @property
    def total_attempted(self) -> int:
        return sum(self.attempted.values())

    @property
    def total_successful(self) -> int:
        return sum(self.successful.values())

    @property
    def total_failed(self) -> int:
        return self.total_attempted - self.total_successful

    def combined_latency(self) -> LatencyHistogram:
        combined = LatencyHistogram()
        for histogram in self.latency.values():
            combined.merge(histogram)
        return combined


@dataclass(frozen=True)
class PhaseResult:
    elapsed_seconds: float
    client_cpu_seconds: float
    results: Results


@dataclass
class WorkerState:
    worker_id: int
    stub: service_pb2_grpc.WidgetServiceStub
    rng: random.Random
    sequence: int = 0


def env_int(name: str, default: int) -> int:
    value = os.environ.get(name)
    return default if value is None else int(value)


def env_float(name: str, default: float) -> float:
    value = os.environ.get(name)
    return default if value is None else float(value)


def parse_channel_counts(value: str) -> tuple[int, ...]:
    try:
        counts = tuple(int(item.strip()) for item in value.split(","))
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "channel counts must be comma-separated positive integers",
        ) from error
    if not counts or any(count <= 0 for count in counts):
        raise argparse.ArgumentTypeError(
            "channel counts must be comma-separated positive integers",
        )
    if len(set(counts)) != len(counts):
        raise argparse.ArgumentTypeError("channel counts must not repeat")
    return counts


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    port = env_int("ACME_PORT", 50062)
    parser = argparse.ArgumentParser(
        description="Run an eight-second randomized Acme gRPC CRUD load test.",
    )
    parser.add_argument("--address", default=f"127.0.0.1:{port}")
    parser.add_argument("--port", type=int, default=port,
                        help="managed server port (default: %(default)s)")
    parser.add_argument(
        "--server-binary",
        metavar="PATH",
        help=(
            "managed server executable override; useful for interleaved "
            "baseline/candidate runs (default: the Bazel runfile)"
        ),
    )
    parser.add_argument("--duration", type=float,
                        default=env_float("ACME_LOAD_DURATION_SECONDS", 8.0))
    parser.add_argument(
        "--warmup",
        type=float,
        default=env_float("ACME_LOAD_WARMUP_SECONDS", 2.0),
        help="excluded warmup duration in seconds (default: %(default)s)",
    )
    parser.add_argument("--concurrency", type=int,
                        default=env_int("ACME_LOAD_WORKERS", 48))
    parser.add_argument(
        "--channels",
        type=parse_channel_counts,
        default=parse_channel_counts(os.environ.get("ACME_LOAD_CHANNELS", "1")),
        metavar="COUNT[,COUNT...]",
        help=(
            "persistent channel count or ordered topology sweep; workers are "
            "assigned by worker id modulo channel count (default: 1)"
        ),
    )
    parser.add_argument("--seed-count", type=int, default=64)
    parser.add_argument("--random-seed", type=int,
                        default=env_int("ACME_LOAD_RANDOM_SEED", time.time_ns()))
    parser.add_argument(
        "--rpc-timeout",
        type=float,
        default=env_float("ACME_LOAD_RPC_TIMEOUT_SECONDS", 0.0),
        help="per-RPC deadline in seconds; 0 disables it (default: %(default)s)",
    )
    parser.add_argument(
        "--json-output",
        default=os.environ.get("ACME_LOAD_JSON_OUTPUT"),
        metavar="PATH",
        help="write the complete versioned result document as JSON",
    )
    parser.add_argument(
        "--manage-stack",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="start/stop Compose PostgreSQL and the Bazel-built Lean server",
    )
    args = parser.parse_args(argv)
    if args.duration <= 0:
        parser.error("--duration must be positive")
    if args.warmup < 0:
        parser.error("--warmup cannot be negative")
    if args.concurrency <= 0:
        parser.error("--concurrency must be positive")
    if any(count > args.concurrency for count in args.channels):
        parser.error("--channels counts cannot exceed --concurrency")
    if args.seed_count <= 0:
        parser.error("--seed-count must be positive")
    if args.rpc_timeout < 0:
        parser.error("--rpc-timeout cannot be negative")
    if args.manage_stack and args.address not in {
        f"127.0.0.1:{args.port}", f"localhost:{args.port}"
    }:
        parser.error("managed mode requires --address to use --port on localhost")
    if args.server_binary is not None:
        if not args.manage_stack:
            parser.error("--server-binary requires managed mode")
        server_binary = Path(args.server_binary).expanduser().resolve()
        if not server_binary.is_file():
            parser.error(f"--server-binary is not a file: {server_binary}")
        if not os.access(server_binary, os.X_OK):
            parser.error(f"--server-binary is not executable: {server_binary}")
        args.server_binary = str(server_binary)
    args.resolved_server_binary = None
    return args


def runfile(logical_path: str) -> Path:
    resolver = runfiles.Create()
    if resolver is None:
        raise RuntimeError("Bazel runfiles are unavailable; use bazel run //scripts:acme_load")
    resolved = resolver.Rlocation(logical_path)
    if resolved is None:
        raise RuntimeError(f"missing Bazel runfile: {logical_path}")
    return Path(resolved)


class ManagedStack:
    """Owns a uniquely named Compose project and the runfile server process."""

    def __init__(self, port: int, server_binary: str | None = None) -> None:
        self.port = port
        self.project = f"acme-load-{os.getpid()}"
        workspace = os.environ.get("BUILD_WORKSPACE_DIRECTORY")
        workspace_compose = Path(workspace, "docker-compose.yml") if workspace else None
        if workspace_compose is not None and workspace_compose.is_file():
            self.compose_file = workspace_compose
        else:
            self.compose_file = runfile("_main/docker-compose.yml")
        self.server_binary = (
            Path(server_binary)
            if server_binary is not None
            else runfile("_main/lean/Acme/acme_server")
        )
        self.compose = [
            "docker", "compose", "-f", str(self.compose_file),
            "-p", self.project,
        ]
        self.server: subprocess.Popen[bytes] | None = None
        self.server_log = tempfile.TemporaryFile(mode="w+b")
        self.compose_started = False

    def start(self) -> None:
        subprocess.run(
            [*self.compose, "up", "-d", "postgres"],
            check=True,
            stdout=subprocess.DEVNULL,
        )
        self.compose_started = True
        for _ in range(120):
            ready = subprocess.run(
                [*self.compose, "exec", "-T", "postgres", "pg_isready",
                 "-h", "127.0.0.1", "-U", "acme"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            if ready.returncode == 0:
                break
            time.sleep(0.5)
        else:
            raise RuntimeError("PostgreSQL did not become ready")

        environment = os.environ.copy()
        postgres_port = environment.get("ACME_POSTGRES_PORT", "54398")
        environment.setdefault(
            "ACME_DATABASE_URL",
            f"postgres://acme@localhost:{postgres_port}/acme",
        )
        environment["ACME_LISTEN_PORT"] = str(self.port)
        self.server = subprocess.Popen(
            [str(self.server_binary)],
            stdin=subprocess.DEVNULL,
            stdout=self.server_log,
            stderr=subprocess.STDOUT,
            env=environment,
        )

    def server_output(self) -> str:
        self.server_log.flush()
        self.server_log.seek(0)
        return self.server_log.read().decode(errors="replace")

    def close(self) -> None:
        if self.server is not None and self.server.poll() is None:
            try:
                self.server.terminate()
                self.server.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.server.terminate()
                try:
                    self.server.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    self.server.kill()
                    self.server.wait()
        if self.compose_started:
            subprocess.run(
                [*self.compose, "down", "-v"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        self.server_log.close()


def widget(name: str, sku: int, quantity: int, widget_id: int = 0) -> widgets_pb2.Widget:
    return widgets_pb2.Widget(
        id=widget_id,
        owner_id=7,
        name=name,
        sku=f"wgt-{sku}",
        quantity=quantity,
    )


def rpc_timeout(value: float) -> float | None:
    return None if value == 0 else value


async def seed_widgets(
    stub: service_pb2_grpc.WidgetServiceStub,
    count: int,
    timeout: float | None,
) -> tuple[int, ...]:
    ids: list[int] = []
    for number in range(1, count + 1):
        response = await stub.CreateWidget(
            widgets_pb2.CreateWidgetRequest(
                user_id=7,
                widget=widget(f"Seed widget {number}", 1000 + number, 10),
            ),
            metadata=AUTH_METADATA,
            timeout=timeout,
        )
        if not response.HasField("widget") or response.widget.id == 0:
            raise RuntimeError("seed CreateWidget returned no assigned widget id")
        ids.append(response.widget.id)
    return tuple(ids)


async def one_operation(
    stub: service_pb2_grpc.WidgetServiceStub,
    operation: str,
    rng: random.Random,
    worker_id: int,
    sequence: int,
    hot_ids: tuple[int, ...],
    timeout: float | None,
) -> None:
    widget_id = rng.choice(hot_ids)
    if operation == "get":
        await stub.GetWidget(
            widgets_pb2.GetWidgetRequest(widget_id=widget_id),
            metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "list":
        await stub.ListWidgets(
            widgets_pb2.ListWidgetsRequest(
                user_id=7, page_size=rng.randint(10, 100),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "update":
        await stub.UpdateWidget(
            widgets_pb2.UpdateWidgetRequest(
                user_id=7,
                widget=widget(
                    f"Updated widget {worker_id}-{sequence}",
                    rng.randint(1000, 9999),
                    rng.randint(0, 1000),
                    widget_id,
                ),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "create":
        await stub.CreateWidget(
            widgets_pb2.CreateWidgetRequest(
                user_id=7,
                widget=widget(
                    f"Created widget {worker_id}-{sequence}",
                    rng.randint(1000, 9999),
                    rng.randint(0, 1000),
                ),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    else:
        await stub.DeleteWidget(
            widgets_pb2.DeleteWidgetRequest(
                user_id=7, widget_id=rng.randint(1_000_000, 2_000_000),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )


def choose_operation(rng: random.Random) -> str:
    pick = rng.randrange(100)
    if pick < 55:
        return "get"
    if pick < 75:
        return "list"
    if pick < 90:
        return "update"
    if pick < 98:
        return "create"
    return "delete"


async def load_worker(
    state: WorkerState,
    end: float,
    hot_ids: tuple[int, ...],
    timeout: float | None,
    results: Results,
) -> None:
    while time.monotonic() < end:
        operation = choose_operation(state.rng)
        started_ns = time.monotonic_ns()
        failure: str | None = None
        try:
            await one_operation(
                state.stub,
                operation,
                state.rng,
                state.worker_id,
                state.sequence,
                hot_ids,
                timeout,
            )
        except grpc.aio.AioRpcError as error:
            failure = error.code().name
        except Exception as error:  # Preserve unexpected client failures in the report.
            failure = type(error).__name__
        results.record(operation, started_ns, failure)
        state.sequence += 1


def channel_options(channel_count: int) -> tuple[tuple[str, int], ...]:
    if channel_count == 1:
        # Keep the original one-channel construction and C-core defaults intact.
        return ()
    return (
        # Without a local pool, separately constructed Python channels may share
        # one C-core subchannel (and therefore one HTTP/2/TCP connection).
        ("grpc.use_local_subchannel_pool", 1),
    )


def worker_channel_index(worker_id: int, channel_count: int) -> int:
    return worker_id % channel_count


def make_channels(address: str, channel_count: int) -> list[grpc.aio.Channel]:
    if channel_count == 1:
        return [grpc.aio.insecure_channel(address)]
    return [
        grpc.aio.insecure_channel(
            address,
            options=channel_options(channel_count),
        )
        for _ in range(channel_count)
    ]


async def run_phase(
    workers: Sequence[WorkerState],
    duration: float,
    hot_ids: tuple[int, ...],
    timeout: float | None,
) -> PhaseResult:
    results = Results()
    started = time.monotonic()
    cpu_started_ns = time.process_time_ns()
    end = started + duration
    if duration > 0:
        await asyncio.gather(*(
            load_worker(worker, end, hot_ids, timeout, results)
            for worker in workers
        ))
    elapsed = time.monotonic() - started
    client_cpu_seconds = (time.process_time_ns() - cpu_started_ns) / 1_000_000_000
    return PhaseResult(elapsed, client_cpu_seconds, results)


def phase_document(phase: PhaseResult) -> dict[str, Any]:
    results = phase.results
    attempted = results.total_attempted
    successful = results.total_successful
    combined_latency = results.combined_latency()
    by_operation: dict[str, Any] = {}
    for operation in OPERATIONS:
        operation_attempted = results.attempted[operation]
        operation_successful = results.successful[operation]
        by_operation[operation] = {
            "attempted": operation_attempted,
            "successful": operation_successful,
            "failed": operation_attempted - operation_successful,
            "latency_ms": results.latency[operation].as_milliseconds(),
        }
    return {
        "elapsed_seconds": phase.elapsed_seconds,
        "client_cpu_seconds": phase.client_cpu_seconds,
        "client_cpu_utilization_percent": (
            100.0 * phase.client_cpu_seconds / phase.elapsed_seconds
            if phase.elapsed_seconds
            else 0.0
        ),
        "counts": {
            "attempted": attempted,
            "successful": successful,
            "failed": attempted - successful,
            "by_operation": by_operation,
            "failures_by_status": dict(sorted(results.failures.items())),
        },
        "throughput_iops": {
            "attempted": attempted / phase.elapsed_seconds if phase.elapsed_seconds else 0.0,
            "successful": successful / phase.elapsed_seconds if phase.elapsed_seconds else 0.0,
        },
        "latency_ms": combined_latency.as_milliseconds(),
    }


def topology_document(
    channel_count: int,
    concurrency: int,
    warmup: PhaseResult,
    measurement: PhaseResult,
) -> dict[str, Any]:
    workers_per_channel = [0] * channel_count
    for worker_id in range(concurrency):
        workers_per_channel[worker_channel_index(worker_id, channel_count)] += 1
    return {
        "channels": channel_count,
        "connection_topology": {
            "persistent_during_warmup_and_measurement": True,
            "ready_channels": channel_count,
            "subchannel_pool": (
                "grpc_default_shared" if channel_count == 1 else "local_per_channel"
            ),
            "connection_isolation_option": (
                None if channel_count == 1 else "grpc.use_local_subchannel_pool=1"
            ),
            "worker_assignment": "worker_id_modulo_channel_count",
            "workers_per_channel": workers_per_channel,
        },
        "warmup_excluded": phase_document(warmup),
        "measurement": phase_document(measurement),
    }


def print_topology_result(
    args: argparse.Namespace,
    channel_count: int,
    warmup: PhaseResult,
    measurement: PhaseResult,
) -> None:
    results = measurement.results
    attempted = results.total_attempted
    successful = results.total_successful
    failed = results.total_failed
    latency = results.combined_latency().as_milliseconds()
    operations = ", ".join(
        f"{name}={results.successful[name]}/{results.attempted[name]}"
        for name in OPERATIONS
    )
    print(
        f"Excluded warmup (channels={channel_count}): "
        f"{warmup.results.total_attempted} attempts in "
        f"{warmup.elapsed_seconds:.3f}s, {warmup.results.total_failed} failures"
    )
    print(
        f"ACME mixed load (channels={channel_count}): {attempted} attempts, "
        f"{successful} successful in {measurement.elapsed_seconds:.3f}s = "
        f"{attempted / measurement.elapsed_seconds:.1f} attempted IOPS, "
        f"{successful / measurement.elapsed_seconds:.1f} successful IOPS"
    )
    print(f"Successful/attempted by operation: {operations}")
    print(
        "RPC latency (all attempts): "
        f"mean={latency['mean']:.3f} ms, p95={latency['p95']:.3f} ms, "
        f"p99={latency['p99']:.3f} ms, max={latency['max']:.3f} ms"
    )
    print(
        f"Client process CPU: {measurement.client_cpu_seconds:.3f}s = "
        f"{100.0 * measurement.client_cpu_seconds / measurement.elapsed_seconds:.1f}% "
        "(100%=one logical core)"
    )
    print(
        f"RPC failures: {failed} "
        f"({100.0 * failed / attempted if attempted else 0.0:.3f}%)"
    )
    if failed:
        print("Failure statuses: " + ", ".join(
            f"{status}={count}" for status, count in sorted(results.failures.items())
        ))
    topology = (
        "one shared persistent HTTP/2 channel"
        if channel_count == 1
        else (
            f"{channel_count} persistent HTTP/2 channels with isolated local "
            "subchannel pools"
        )
    )
    print(
        f"Configuration: warmup={args.warmup:g}s (excluded), "
        f"duration={args.duration:g}s, concurrency={args.concurrency}, {topology}, "
        f"rpc_timeout={args.rpc_timeout:g}s, random_seed={args.random_seed}"
    )


def git_repository_metadata(repository: Path) -> dict[str, Any]:
    if not Path(repository, ".git").exists():
        return {"path": str(repository), "revision": None, "dirty": None}
    try:
        revision = subprocess.run(
            ["git", "-C", str(repository), "rev-parse", "HEAD"],
            check=True,
            capture_output=True,
            text=True,
            timeout=5,
        ).stdout.strip()
        dirty = bool(subprocess.run(
            ["git", "-C", str(repository), "status", "--porcelain"],
            check=True,
            capture_output=True,
            text=True,
            timeout=5,
        ).stdout)
        return {"path": str(repository), "revision": revision, "dirty": dirty}
    except (OSError, subprocess.SubprocessError):
        return {"path": str(repository), "revision": None, "dirty": None}


def file_sha256(path: Path) -> str | None:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def server_binary_metadata(path: str | None) -> dict[str, Any] | None:
    if path is None:
        return None
    binary = Path(path)
    try:
        stat = binary.stat()
    except OSError:
        return {"path": str(binary), "size_bytes": None, "sha256": None}
    return {
        "path": str(binary),
        "size_bytes": stat.st_size,
        "sha256": file_sha256(binary),
    }


def source_metadata() -> dict[str, Any]:
    workspace = Path(os.environ.get("BUILD_WORKSPACE_DIRECTORY", Path.cwd())).resolve()
    repositories = {
        name: git_repository_metadata(
            workspace if name == "lean-acme-widgets" else Path(workspace.parent, name),
        )
        for name in LOCAL_SOURCE_REPOSITORIES
    }
    return {
        "repositories": repositories,
        "bazel_module_sha256": file_sha256(Path(workspace, "MODULE.bazel")),
        "bazel_module_lock_sha256": file_sha256(Path(workspace, "MODULE.bazel.lock")),
    }


def result_document(args: argparse.Namespace, runs: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": "pb64-lean.acme-load-result",
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "benchmark": "acme_widgets_weighted_crud",
        "configuration": {
            "address": args.address,
            "manage_stack": args.manage_stack,
            "warmup_seconds": args.warmup,
            "measurement_seconds": args.duration,
            "concurrency": args.concurrency,
            "channel_sweep": list(args.channels),
            "seed_count": args.seed_count,
            "random_seed": args.random_seed,
            "rpc_timeout_seconds": args.rpc_timeout,
            "operation_weights_percent": OPERATION_WEIGHTS,
            "latency_quantiles": {
                "scope": "all_attempts",
                "method": "log_histogram_upper_bound",
                "sub_buckets_per_power_of_two": HISTOGRAM_SUB_BUCKETS,
                "maximum_relative_bucket_width": 1 / HISTOGRAM_SUB_BUCKETS,
            },
        },
        "client_machine": {
            "hostname": socket.gethostname(),
            "platform": platform.platform(),
            "machine": platform.machine(),
            "processor": platform.processor(),
            "logical_cpu_count": os.cpu_count(),
            "python_version": platform.python_version(),
            "grpcio_version": grpc.__version__,
        },
        "source": source_metadata(),
        "server_binary": server_binary_metadata(args.resolved_server_binary),
        "runs": runs,
    }


def write_json_result(path: str, document: dict[str, Any]) -> None:
    destination = Path(path)
    try:
        destination.write_text(
            json.dumps(document, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except OSError as error:
        raise RuntimeError(f"cannot write JSON result {destination}: {error}") from error


async def run_load(args: argparse.Namespace) -> int:
    timeout = rpc_timeout(args.rpc_timeout)
    hot_ids: tuple[int, ...] | None = None
    run_documents: list[dict[str, Any]] = []
    failed = False

    for channel_count in args.channels:
        channels = make_channels(args.address, channel_count)
        try:
            await asyncio.gather(*(
                asyncio.wait_for(channel.channel_ready(), timeout=30)
                for channel in channels
            ))
            stubs = [service_pb2_grpc.WidgetServiceStub(channel) for channel in channels]
            if hot_ids is None:
                hot_ids = await seed_widgets(stubs[0], args.seed_count, timeout)
            workers = [
                WorkerState(
                    worker_id=worker_id,
                    stub=stubs[worker_channel_index(worker_id, channel_count)],
                    rng=random.Random(args.random_seed + worker_id),
                )
                for worker_id in range(args.concurrency)
            ]
            warmup = await run_phase(workers, args.warmup, hot_ids, timeout)
            measurement = await run_phase(workers, args.duration, hot_ids, timeout)
            print_topology_result(args, channel_count, warmup, measurement)
            run_documents.append(topology_document(
                channel_count,
                args.concurrency,
                warmup,
                measurement,
            ))
            failed = failed or warmup.results.total_failed > 0
            failed = failed or measurement.results.total_failed > 0
        finally:
            await asyncio.gather(*(channel.close() for channel in channels))

    if args.json_output is not None:
        write_json_result(args.json_output, result_document(args, run_documents))
        print(f"Machine-readable result: {args.json_output}")
    return 1 if failed else 0


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    stack: ManagedStack | None = None
    try:
        if args.manage_stack:
            stack = ManagedStack(args.port, args.server_binary)
            args.resolved_server_binary = str(stack.server_binary.resolve())
            stack.start()
        return asyncio.run(run_load(args))
    except (RuntimeError, subprocess.CalledProcessError, asyncio.TimeoutError) as error:
        print(f"error: {error}", file=sys.stderr)
        if stack is not None:
            output = stack.server_output().strip()
            if output:
                print("server log:", file=sys.stderr)
                for line in output.splitlines():
                    print(f"  | {line}", file=sys.stderr)
        return 1
    finally:
        if stack is not None:
            stack.close()


if __name__ == "__main__":
    raise SystemExit(main())
