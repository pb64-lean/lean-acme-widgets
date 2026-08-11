"""Hermetic entry point for grpcio-tools' protoc wrapper."""

from pathlib import Path
import sys

import grpc_tools
from grpc_tools import protoc


def main() -> int:
    # grpcio-tools bundles the well-known Google protos, but its Python API
    # expects callers to add that directory to protoc's include path.
    well_known_protos = Path(grpc_tools.__file__).with_name("_proto")
    return protoc.main([
        sys.argv[0],
        f"-I{well_known_protos}",
        *sys.argv[1:],
    ])


if __name__ == "__main__":
    raise SystemExit(main())
