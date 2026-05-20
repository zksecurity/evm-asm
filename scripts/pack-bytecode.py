#!/usr/bin/env python3
"""
pack-bytecode.py — pack a comma-separated `0xNN` byte list into a
ziskemu `-i <file>` payload (8-byte LE length prefix + raw bytes).

Used by M8.5's `scripts/codegen-opcodes-runtime-check.sh` to turn
the bytecode column of `lake exe codegen --list-test-cases` (which
mirrors `EvmAsm/Codegen/Tests/Cases.lean`'s `bytecode` field, e.g.
`"0x60, 0x02, 0x60, 0x0a, 0x04, 0x00"`) into a binary file the
runtime-bytecode dispatcher reads at `INPUT_ADDR + INPUT_DATA_OFFSET`.

Usage:
    pack-bytecode.py "0x60, 0x02, 0x60, 0x0a, 0x04, 0x00" output.bin
    echo "0x60, 0x00" | pack-bytecode.py - output.bin

Output layout (matches ziskemu's record-with-length-prefix shape; see
`EvmAsm/Codegen/Programs.lean`'s `INPUT_DATA_OFFSET = 16` derivation):

    bytes 0..8   <8-byte LE u64 length of the bytecode>
    bytes 8..    <bytecode bytes>

ziskemu prepends 8 more bytes of its own metadata when loading,
landing the length prefix at INPUT_ADDR+8 and the bytecode at
INPUT_ADDR+16 — which is where the runtime-bytecode dispatcher's
`li x10, 0x40000010` points.
"""
import argparse
import re
import struct
import sys


def parse_csv(csv: str) -> bytes:
    """Parse a `0xNN, 0xMM, ...` string into raw bytes."""
    tokens = re.findall(r"0[xX][0-9a-fA-F]+", csv)
    if not tokens:
        raise ValueError(f"no `0xNN` tokens in input: {csv!r}")
    return bytes(int(t, 16) for t in tokens)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pack a comma-separated 0xNN byte list into a "
                    "ziskemu input file (8-byte LE length prefix + bytes)."
    )
    parser.add_argument(
        "bytecode",
        help="Comma-separated bytecode (e.g. '0x60, 0x02, 0x00'). "
             "Use '-' to read from stdin.",
    )
    parser.add_argument(
        "output",
        help="Path to write the packed binary. Use '-' for stdout.",
    )
    args = parser.parse_args()

    csv = sys.stdin.read() if args.bytecode == "-" else args.bytecode
    payload = parse_csv(csv)
    packed = struct.pack("<Q", len(payload)) + payload
    # ziskemu requires the input file size to be a multiple of 8.
    # Pad with zero bytes; the dispatcher only reads up to STOP so
    # trailing zeros are harmless (0x00 = STOP opcode anyway, but
    # the dispatcher will hit the bytecode's own STOP first).
    pad = (-len(packed)) % 8
    if pad:
        packed += b"\x00" * pad

    if args.output == "-":
        sys.stdout.buffer.write(packed)
    else:
        with open(args.output, "wb") as f:
            f.write(packed)

    return 0


if __name__ == "__main__":
    sys.exit(main())
