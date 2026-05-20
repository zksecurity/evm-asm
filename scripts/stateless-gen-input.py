#!/usr/bin/env python3
"""Generate a `ziskemu -i` input file containing a length-prefixed,
SSZ-encoded `SszStatelessInput` with a caller-specified `chain_id`.

Invocation (from the repo root):

    uv run --directory execution-specs --quiet python3 \
        ../scripts/stateless-gen-input.py CHAIN_ID OUT_FILE

CHAIN_ID is parsed as a Python integer literal (`int(..., 0)`), so
`1`, `0x1234567890ABCDEF`, and `1311768467294899695` are all valid.

The generated file is laid out as ziskemu expects:

    bytes [0..8)    : u64 LE length of the SSZ blob
    bytes [8..)     : SSZ-encoded SszStatelessInput

ziskemu places this verbatim at INPUT_ADDR + 8.. on guest start, after
its own 8 metadata bytes (zeroed). See `EvmAsm/Codegen/Programs.lean`
for the host-IO layout and `EvmAsm/Stateless/SSZ/Decode/Program.lean`
for the guest's reader.
"""
from __future__ import annotations

import argparse
import struct
import sys
from pathlib import Path


def build_ssz_blob(chain_id: int, with_empty_header: bool) -> bytes:
    """SSZ-encode an `SszStatelessInput`.

    `chain_config.chain_id` is set from `chain_id`. Other fields are
    empty defaults, except when `with_empty_header` is `True`: then
    `witness.headers` carries one zero-length entry, growing the
    witness body from 12 bytes (the offsets table alone) to 16 bytes
    (offsets + a 4-byte inner offsets entry for the single empty
    header). This is the fixture the guest's
    `decode_validation_bit` uses to flip its bool to `0`."""
    from ethereum.forks.amsterdam.stateless_ssz import (
        MAX_BYTES_PER_HEADER,
        MAX_WITNESS_HEADERS,
        SszChainConfig,
        SszExecutionWitness,
        SszNewPayloadRequest,
        SszStatelessInput,
    )
    from remerkleable.byte_arrays import ByteList
    from remerkleable.complex import List as SszList

    if with_empty_header:
        headers = SszList[ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS](
            ByteList[MAX_BYTES_PER_HEADER]()
        )
        witness = SszExecutionWitness(headers=headers)
    else:
        witness = SszExecutionWitness()

    ssz_input = SszStatelessInput(
        new_payload_request=SszNewPayloadRequest(),
        witness=witness,
        chain_config=SszChainConfig(chain_id=chain_id),
        public_keys=(),
    )
    return ssz_input.encode_bytes()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "chain_id",
        help="Python integer literal (e.g. 1, 0x1234567890ABCDEF).",
    )
    parser.add_argument("out_file", type=Path)
    parser.add_argument(
        "--with-empty-header",
        action="store_true",
        help=(
            "Inject one zero-length entry into `witness.headers` so the "
            "guest's decode_validation_bit yields 0 (non-empty witness)."
        ),
    )
    args = parser.parse_args()

    chain_id = int(args.chain_id, 0)
    blob = build_ssz_blob(chain_id, args.with_empty_header)

    # ziskemu reads the input file in u64 chunks and rejects sizes that
    # aren't a multiple of 8 ("EmuContext::new() input size must be a
    # multiple of 8"). Pad with zeros after the SSZ blob. The length
    # prefix still names the true blob size, so the guest reads the
    # correct number of SSZ bytes; padding sits past the SSZ tail.
    total = 8 + len(blob)
    pad = (-total) % 8

    args.out_file.parent.mkdir(parents=True, exist_ok=True)
    with args.out_file.open("wb") as fh:
        fh.write(struct.pack("<Q", len(blob)))
        fh.write(blob)
        if pad:
            fh.write(b"\x00" * pad)

    print(
        f"wrote {args.out_file}: 8 B length prefix + {len(blob)} B SSZ blob "
        f"+ {pad} B pad = {total + pad} B total",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
