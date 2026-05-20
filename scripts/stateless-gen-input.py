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


def _rlp_encoded_test_header() -> bytes:
    """Construct + RLP-encode an amsterdam Block Header with fixed
    test field values. Used by `--with-one-real-header` so the
    fixture's `witness.headers[0]` is a real (~660-byte) header."""
    from ethereum.crypto.hash import Hash32
    from ethereum_rlp import rlp
    from ethereum_types.bytes import Bytes, Bytes8, Bytes32
    from ethereum_types.numeric import U64, U256, Uint

    from ethereum.forks.amsterdam.blocks import Header
    from ethereum.forks.amsterdam.fork_types import Bloom

    h = Header(
        parent_hash=Hash32(b"\x11" * 32),
        ommers_hash=Hash32(b"\x22" * 32),
        coinbase=Bytes(b"\x33" * 20),
        state_root=Hash32(b"\x44" * 32),
        transactions_root=Hash32(b"\x55" * 32),
        receipt_root=Hash32(b"\x66" * 32),
        bloom=Bloom(b"\x00" * 256),
        difficulty=Uint(0),
        number=Uint(0x1234),
        gas_limit=Uint(0x1c9c380),
        gas_used=Uint(0x100),
        timestamp=U256(0x6566778899),
        extra_data=Bytes(b"evm-asm2 PR-K7"),
        prev_randao=Bytes32(b"\x77" * 32),
        nonce=Bytes8(b"\x00" * 8),
        base_fee_per_gas=Uint(0x07),
        withdrawals_root=Hash32(b"\x88" * 32),
        blob_gas_used=U64(0),
        excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(b"\x99" * 32),
        requests_hash=Hash32(b"\xaa" * 32),
        block_access_list_hash=Hash32(b"\xbb" * 32),
    )
    return rlp.encode(h)


def build_ssz_blob(
    chain_id: int,
    with_empty_header: bool,
    with_empty_state_node: bool,
    with_two_empty_headers: bool,
    with_one_real_header: bool,
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
    if with_one_real_header:
        header_bytes = _rlp_encoded_test_header()
        witness_kwargs["headers"] = SszList[
            ByteList[MAX_BYTES_PER_HEADER], MAX_WITNESS_HEADERS
        ](ByteList[MAX_BYTES_PER_HEADER](header_bytes))
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
    parser.add_argument(
        "--with-one-real-header",
        action="store_true",
        help=(
            "Inject a single RLP-encoded amsterdam Header into "
            "`witness.headers[0]`. Used by PR-K7 to test per-element "
            "extraction: the guest hashes element 0 (the header "
            "bytes), not the whole section."
        ),
    )
    parser.add_argument(
        "--hash-out",
        type=Path,
        default=None,
        help=(
            "Optionally write the SSZ `hash_tree_root` of "
            "`witness.headers[0]` (as a `ByteList[1024]`) as a "
            "64-hex-char string. PR-S10's stateless_guest stamps "
            "this into the output's `new_payload_request_root` "
            "field (replacing PR-K7's keccak stub). When "
            "`witness.headers` is empty, hashes an empty "
            "`ByteList[1024]()`."
        ),
    )
    args = parser.parse_args()

    chain_id = int(args.chain_id, 0)
    blob = build_ssz_blob(
        chain_id,
        args.with_empty_header,
        args.with_empty_state_node,
        args.with_two_empty_headers,
        args.with_one_real_header,
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

    if args.hash_out is not None:
        # PR-S10: the guest computes SSZ `hash_tree_root` of
        # `witness.headers[0]` -- element 0 of the SSZ list -- as a
        # `ByteList[MAX_BYTES_PER_HEADER = 1024]`. When the list is
        # empty, hashes an empty `ByteList[1024]()`. We extract
        # element 0 from the SSZ blob and feed it through the same
        # consensus-specs SSZ library the guest's contract is
        # checked against (remerkleable, via execution-specs).
        import struct as _struct
        from ethereum.forks.amsterdam.stateless_ssz import (
            MAX_BYTES_PER_HEADER,
        )
        from remerkleable.byte_arrays import ByteList

        offset_1 = _struct.unpack_from("<I", blob, 4)[0]
        offset_3 = _struct.unpack_from("<I", blob, 16)[0]
        witness_start = offset_1
        witness_end = offset_3
        inner_off2 = _struct.unpack_from("<I", blob, witness_start + 8)[0]
        headers_start = witness_start + inner_off2
        headers_end = witness_end

        headers_len = headers_end - headers_start
        if headers_len == 0:
            element_0 = b""
            why = "headers empty"
        else:
            first_inner = _struct.unpack_from(
                "<I", blob, headers_start)[0]
            el0_start = headers_start + first_inner
            n_elements = first_inner // 4
            if n_elements == 1:
                el0_end = headers_end
            else:
                second_inner = _struct.unpack_from(
                    "<I", blob, headers_start + 4)[0]
                el0_end = headers_start + second_inner
            element_0 = blob[el0_start:el0_end]
            why = f"N={n_elements}, el0 {len(element_0)}B"

        root = ByteList[MAX_BYTES_PER_HEADER](element_0).hash_tree_root()
        digest = root.hex() if isinstance(root, bytes) else bytes(root).hex()
        args.hash_out.parent.mkdir(parents=True, exist_ok=True)
        with args.hash_out.open("w") as fh:
            fh.write(digest)
        print(
            f"wrote {args.hash_out}: "
            f"ssz_hash_tree_root(ByteList[{MAX_BYTES_PER_HEADER}], "
            f"witness.headers[0], {why}) = {digest}",
            file=sys.stderr,
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
