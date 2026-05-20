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


def build_ssz_blob(
    chain_id: int,
    with_empty_header: bool,
    with_empty_state_node: bool,
    with_two_empty_headers: bool,
) -> bytes:
    """SSZ-encode an `SszStatelessInput`.

    `chain_config.chain_id` is set from `chain_id`. Other fields are
    empty defaults, with optional witness mutations:

    - `with_empty_header=True` puts one zero-length entry in
      `witness.headers`. The witness body grows from 12 bytes
      (offsets only) to 16 bytes (offsets + a 4-byte inner offsets
      entry for the empty header).
    - `with_two_empty_headers=True` puts two zero-length entries in
      `witness.headers`. Witness body grows to 20 bytes
      (12 offsets + 8 inner offsets); the first inner u32 = 8, so
      the guest's PR6 `decode_header_count` yields 2.
    - `with_empty_state_node=True` puts one zero-length entry in
      `witness.state`. The witness body grows the same way as
      `with_empty_header`, but the mutation lives in `state` --
      `witness.headers` stays empty.

    The combinations let the test harness distinguish:
      (A) empty witness                 -> headers empty,  count=0
      (B) one empty header              -> headers !empty, count=1
      (C) two empty headers             -> headers !empty, count=2
      (D) one empty state node          -> headers empty,  count=0
                                           (state non-empty, but the
                                            guest's PR5 bool only
                                            tracks headers and PR6
                                            count only tracks headers)
    """
    from ethereum.forks.amsterdam.stateless_ssz import (
        MAX_BYTES_PER_HEADER,
        MAX_BYTES_PER_WITNESS_NODE,
        MAX_WITNESS_HEADERS,
        MAX_WITNESS_NODES,
        SszChainConfig,
        SszExecutionWitness,
        SszNewPayloadRequest,
        SszStatelessInput,
    )
    from remerkleable.byte_arrays import ByteList
    from remerkleable.complex import List as SszList

    witness_kwargs = {}
    if with_empty_header:
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](ByteList[MAX_BYTES_PER_HEADER]())
    if with_two_empty_headers:
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](
            ByteList[MAX_BYTES_PER_HEADER](),
            ByteList[MAX_BYTES_PER_HEADER](),
        )
    if with_empty_state_node:
        witness_kwargs["state"] = SszList[
            ByteList[MAX_BYTES_PER_WITNESS_NODE], MAX_WITNESS_NODES
        ](ByteList[MAX_BYTES_PER_WITNESS_NODE]())
    witness = SszExecutionWitness(**witness_kwargs)

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
            "Inject one zero-length entry into `witness.headers` so "
            "the guest's PR5 decode_validation_bit yields 0 "
            "(headers list non-empty)."
        ),
    )
    parser.add_argument(
        "--with-empty-state-node",
        action="store_true",
        help=(
            "Inject one zero-length entry into `witness.state`. PR5's "
            "bool tracks headers only, so this fixture stays at 1 "
            "(differentiates PR5 logic from PR4 logic)."
        ),
    )
    parser.add_argument(
        "--with-two-empty-headers",
        action="store_true",
        help=(
            "Inject two zero-length entries into `witness.headers`. "
            "PR6's decode_header_count should yield 2."
        ),
    )
    args = parser.parse_args()

    chain_id = int(args.chain_id, 0)
    blob = build_ssz_blob(
        chain_id,
        args.with_empty_header,
        args.with_empty_state_node,
        args.with_two_empty_headers,
    )

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
