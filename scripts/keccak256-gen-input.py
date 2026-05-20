#!/usr/bin/env python3
"""Emit a `ziskemu -i` input file containing length-prefixed bytes
to be hashed by the guest's `zkvm_keccak256(data, len, output)`
wrapper. Defaults to an RLP-encoded Ethereum block header
constructed via `execution-specs`; can also accept arbitrary
hex/utf-8 input via flags.

Companion to `scripts/codegen-zisk-keccak256-from-input-check.sh`.

Invocation (from the repo root):

    uv run --directory execution-specs --quiet python3 \
        ../scripts/keccak256-gen-input.py [--shape <preset>] \
        OUT_FILE_DATA OUT_FILE_HASH

OUT_FILE_DATA  -- ziskemu-format input file
                  (8B u64 length || data || 0..7B zero padding to
                  multiple of 8 -- ziskemu requires that).
OUT_FILE_HASH  -- 32-byte expected keccak256 digest, hex-encoded.

--shape options:
  header (default)  -- RLP-encoded amsterdam Block Header with
                       fixed test field values. Mirrors what
                       `Stateless/Headers/Validate.lean` will hash.
  long              -- 1024 bytes of 0x55 (forces 7 full-block
                       absorbs + final padded block).
"""
from __future__ import annotations

import argparse
import struct
import sys
from pathlib import Path


def shape_header() -> bytes:
    """Construct an RLP-encoded amsterdam Header with fixed test
    values, returning the wire bytes.

    Field choices are deterministic and unambiguous; the specific
    values don't matter as long as Python and the guest both hash
    exactly the same bytes."""
    from ethereum.crypto.hash import Hash32
    from ethereum.exceptions import InvalidBlock
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
        extra_data=Bytes(b"evm-asm2 PR-K4"),
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


def shape_long() -> bytes:
    """1024 bytes of 0x55 -- forces 7 full-block absorbs + final."""
    return b"\x55" * 1024


SHAPES = {
    "header": shape_header,
    "long": shape_long,
}


def keccak256(data: bytes) -> bytes:
    """Compute keccak-256 (Ethereum/legacy padding, not NIST SHA3)."""
    from Crypto.Hash import keccak
    h = keccak.new(digest_bits=256)
    h.update(data)
    return h.digest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--shape", choices=list(SHAPES), default="header",
        help="Input shape (default: header).",
    )
    parser.add_argument("out_file_data", type=Path)
    parser.add_argument("out_file_hash", type=Path)
    args = parser.parse_args()

    data = SHAPES[args.shape]()
    digest = keccak256(data)

    # Pad file to multiple of 8 bytes (ziskemu requirement).
    total = 8 + len(data)
    pad = (-total) % 8

    args.out_file_data.parent.mkdir(parents=True, exist_ok=True)
    with args.out_file_data.open("wb") as fh:
        fh.write(struct.pack("<Q", len(data)))
        fh.write(data)
        if pad:
            fh.write(b"\x00" * pad)

    args.out_file_hash.parent.mkdir(parents=True, exist_ok=True)
    with args.out_file_hash.open("w") as fh:
        fh.write(digest.hex())

    print(
        f"shape={args.shape}: 8B prefix + {len(data)}B data + {pad}B pad "
        f"= {total + pad}B input, expected digest = {digest.hex()}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
