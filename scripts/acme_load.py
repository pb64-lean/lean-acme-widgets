#!/usr/bin/env python3
"""Persistent-channel randomized CRUD load test for Acme Widgets."""

from __future__ import annotations

import argparse
import asyncio
from collections import Counter
from dataclasses import dataclass, field
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time
from typing import Sequence

import grpc
from proto import authz_pb2
from proto import service_pb2_grpc
from proto import widgets_pb2
from python.runfiles import runfiles


AUTH_METADATA = (("authorization", "Bearer acme-editor-7"),)
PRINCIPAL = authz_pb2.Principal(id=7, role_level=2)
OPERATIONS = ("get", "list", "update", "create", "delete")


@dataclass
class Results:
    completed: Counter[str] = field(default_factory=Counter)
    failures: Counter[str] = field(default_factory=Counter)
    latency_ns: Counter[str] = field(default_factory=Counter)

    def record(self, operation: str, started_ns: int, failure: str | None) -> None:
        self.completed[operation] += 1
        self.latency_ns[operation] += time.monotonic_ns() - started_ns
        if failure is not None:
            self.failures[failure] += 1


def env_int(name: str, default: int) -> int:
    value = os.environ.get(name)
    return default if value is None else int(value)


def env_float(name: str, default: float) -> float:
    value = os.environ.get(name)
    return default if value is None else float(value)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    port = env_int("ACME_PORT", 50062)
    parser = argparse.ArgumentParser(
        description="Run an eight-second randomized Acme gRPC CRUD load test.",
    )
    parser.add_argument("--address", default=f"127.0.0.1:{port}")
    parser.add_argument("--port", type=int, default=port,
                        help="managed server port (default: %(default)s)")
    parser.add_argument("--duration", type=float,
                        default=env_float("ACME_LOAD_DURATION_SECONDS", 8.0))
    parser.add_argument("--concurrency", type=int,
                        default=env_int("ACME_LOAD_WORKERS", 48))
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
        "--manage-stack",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="start/stop Compose PostgreSQL and the Bazel-built Lean server",
    )
    args = parser.parse_args(argv)
    if args.duration <= 0:
        parser.error("--duration must be positive")
    if args.concurrency <= 0:
        parser.error("--concurrency must be positive")
    if args.seed_count <= 0:
        parser.error("--seed-count must be positive")
    if args.rpc_timeout < 0:
        parser.error("--rpc-timeout cannot be negative")
    if args.manage_stack and args.address not in {
        f"127.0.0.1:{args.port}", f"localhost:{args.port}"
    }:
        parser.error("managed mode requires --address to use --port on localhost")
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

    def __init__(self, port: int) -> None:
        self.port = port
        self.project = f"acme-load-{os.getpid()}"
        workspace = os.environ.get("BUILD_WORKSPACE_DIRECTORY")
        workspace_compose = Path(workspace, "docker-compose.yml") if workspace else None
        if workspace_compose is not None and workspace_compose.is_file():
            self.compose_file = workspace_compose
        else:
            self.compose_file = runfile("_main/docker-compose.yml")
        self.server_binary = runfile("_main/lean/Acme/acme_server")
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
        environment.setdefault("ACME_DATABASE_URL", "postgres://acme@localhost:54398/acme")
        environment["ACME_LISTEN_PORT"] = str(self.port)
        self.server = subprocess.Popen(
            [str(self.server_binary)],
            stdin=subprocess.PIPE,
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
            assert self.server.stdin is not None
            try:
                self.server.stdin.write(b"quit\n")
                self.server.stdin.flush()
                self.server.stdin.close()
                self.server.wait(timeout=10)
            except (BrokenPipeError, subprocess.TimeoutExpired):
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
            authz_pb2.CheckedCreateWidgetRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.CreateWidgetRequest(
                    user_id=7,
                    widget=widget(f"Seed widget {number}", 1000 + number, 10),
                ),
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
            authz_pb2.CheckedGetWidgetRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.GetWidgetRequest(widget_id=widget_id),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "list":
        await stub.ListWidgets(
            authz_pb2.CheckedListWidgetsRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.ListWidgetsRequest(
                    user_id=7, page_size=rng.randint(10, 100),
                ),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "update":
        await stub.UpdateWidget(
            authz_pb2.CheckedUpdateWidgetRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.UpdateWidgetRequest(
                    user_id=7,
                    widget=widget(
                        f"Updated widget {worker_id}-{sequence}",
                        rng.randint(1000, 9999),
                        rng.randint(0, 1000),
                        widget_id,
                    ),
                ),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    elif operation == "create":
        await stub.CreateWidget(
            authz_pb2.CheckedCreateWidgetRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.CreateWidgetRequest(
                    user_id=7,
                    widget=widget(
                        f"Created widget {worker_id}-{sequence}",
                        rng.randint(1000, 9999),
                        rng.randint(0, 1000),
                    ),
                ),
            ), metadata=AUTH_METADATA, timeout=timeout,
        )
    else:
        await stub.DeleteWidget(
            authz_pb2.CheckedDeleteWidgetRequest(
                principal=PRINCIPAL,
                request=widgets_pb2.DeleteWidgetRequest(
                    user_id=7, widget_id=rng.randint(1_000_000, 2_000_000),
                ),
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
    stub: service_pb2_grpc.WidgetServiceStub,
    worker_id: int,
    end: float,
    hot_ids: tuple[int, ...],
    timeout: float | None,
    random_seed: int,
    results: Results,
) -> None:
    rng = random.Random(random_seed + worker_id)
    sequence = 0
    while time.monotonic() < end:
        operation = choose_operation(rng)
        started_ns = time.monotonic_ns()
        failure: str | None = None
        try:
            await one_operation(
                stub, operation, rng, worker_id, sequence, hot_ids, timeout,
            )
        except grpc.aio.AioRpcError as error:
            failure = error.code().name
        except Exception as error:  # Preserve unexpected client failures in the report.
            failure = type(error).__name__
        results.record(operation, started_ns, failure)
        sequence += 1


async def run_load(args: argparse.Namespace) -> int:
    channel = grpc.aio.insecure_channel(args.address)
    try:
        await asyncio.wait_for(channel.channel_ready(), timeout=30)
        stub = service_pb2_grpc.WidgetServiceStub(channel)
        timeout = rpc_timeout(args.rpc_timeout)
        hot_ids = await seed_widgets(stub, args.seed_count, timeout)

        results = Results()
        started = time.monotonic()
        end = started + args.duration
        await asyncio.gather(*(
            load_worker(
                stub, worker, end, hot_ids, timeout, args.random_seed, results,
            )
            for worker in range(args.concurrency)
        ))
        elapsed = time.monotonic() - started

        total = sum(results.completed.values())
        failures = sum(results.failures.values())
        operations = ", ".join(
            f"{name}={results.completed[name]}" for name in OPERATIONS
        )
        mean_ms = (
            sum(results.latency_ns.values()) / total / 1_000_000 if total else 0.0
        )
        print(
            f"ACME mixed load: {total} requests in {elapsed:.3f}s = "
            f"{total / elapsed:.1f} request IOPS"
        )
        print(f"Completed by operation: {operations}")
        print(f"Mean RPC latency: {mean_ms:.3f} ms")
        print(
            f"RPC failures: {failures} "
            f"({100.0 * failures / total if total else 0.0:.3f}%)"
        )
        if failures:
            print("Failure statuses: " + ", ".join(
                f"{status}={count}" for status, count in sorted(results.failures.items())
            ))
        print(
            f"Configuration: duration={args.duration:g}s, "
            f"concurrency={args.concurrency}, one persistent HTTP/2 channel, "
            f"rpc_timeout={args.rpc_timeout:g}s, random_seed={args.random_seed}"
        )
        return 1 if failures else 0
    finally:
        await channel.close()


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    stack: ManagedStack | None = None
    try:
        if args.manage_stack:
            stack = ManagedStack(args.port)
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
