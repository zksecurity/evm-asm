/-
  EvmAsm.Stateless.SSZ.Encode.Program

  Serializer for `SszStatelessValidationResult` -- 41 bytes of fixed-size
  SSZ Container.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessValidationResult(Container)`,
   `class SszChainConfig(Container)`).

  ## SSZ wire layout (all fixed-size, plain concatenation)

  | Offset  | Size | Field                       | Type       |
  |---------|------|-----------------------------|------------|
  |  0..32  |   32 | `new_payload_request_root`  | `Bytes32`  |
  |     32  |    1 | `successful_validation`     | `boolean`  |
  | 33..41  |    8 | `chain_config.chain_id`     | `uint64`   |

  Total: 41 bytes.

  ## Caller contract (PR4)

  Caller places both fields the encoder writes in registers:

      x10 : chain_id              (u64, LE-encoded at output bytes 33..41)
      x11 : successful_validation (low byte only; 0 or 1 in practice)

  The encoder must only see `0` or `1` in `x11`'s low byte; higher
  bits are ignored by the SSZ wire (byte 32 is the bool), but a
  non-bool low byte would corrupt the encoding. PR4's
  `Stateless.SSZ.Decode.decode_validation_bit` is the source of the
  bit and guarantees `x11 ∈ {0, 1}`.

  Hash field is still stubbed:

      new_payload_request_root = 0x00...00  (32 zero bytes)
      successful_validation    = x11        (one byte at offset 32)
      chain_id                 = x10        (LE bytes at offset 33..41)

  Later PRs replace the zero `root` (PR5: SSZ `hash_tree_root`).

  ## Memory layout

  - **Preconditions**:
    - `OUTPUT_BASE = 0xa0010000` is ziskemu's public-output region
      (mirrors `EvmAsm.Codegen.OUTPUT_ADDR`).
    - `[OUTPUT_BASE, OUTPUT_BASE + 41)` lies inside the RAM zone
      (`RAM_MEM_START..RAM_MEM_END`) and is accepted by
      `isValidMemAddr` per issue #5164.
    - `x10` holds the u64 `chain_id` to encode.
  - **Postconditions**: 41 bytes at `OUTPUT_BASE` carry the SSZ
    encoding of `StatelessValidationResult(root = 0, valid = false,
    chain_id = x10)`.
  - **Clobbers**: `x6` (base pointer), `x7` (shifted chain_id work).
  - **Exit**: falls through to the caller's halt stub.

  ## Frame

  10 instructions: 1 LI (base) + 4 SD (zero hash) + 1 SLLI + 1 OR
  (mix in bool) + 1 SD (packed bool || low-7 chain bytes) + 1 SRLI +
  1 SB (high chain byte).

  ## Encoding math

  Let `c = chain_id` (u64) and `b = bool` (low byte of x11, 0 or 1).
  LE encoding writes bytes
  `c & 0xff`, `(c >> 8) & 0xff`, ..., `(c >> 56) & 0xff`
  at positions 33, 34, ..., 40 respectively, and `b` at position 32.

  The packed u64 stored LE at offset 32 is `(c << 8) | b`:

      (((c << 8) | b) >> ( 0 * 8)) & 0xff = b            (byte 32, bool)
      (((c << 8) | b) >> ( 1 * 8)) & 0xff = c & 0xff     (byte 33)
      (((c << 8) | b) >> ( 2 * 8)) & 0xff = (c >> 8) & 0xff
      ...
      (((c << 8) | b) >> ( 7 * 8)) & 0xff = (c >> 48) & 0xff (byte 39)

  Byte 40 is then `c >> 56` (the high LE byte), emitted with a
  separate `SB`. The OR with `b` is safe because `c << 8` always has
  byte 0 = 0, so OR with `b ∈ {0,1}` just sets the low bit.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Encode

open EvmAsm.Rv64

/-- Output region base address. Duplicated from
    `EvmAsm.Codegen.Programs.OUTPUT_ADDR` so `EvmAsm/Stateless/` stays
    free of the codegen umbrella. -/
def OUTPUT_BASE : Word := 0xa0010000

/-- Parameterized serializer Program.

    Caller contract:
      - `x10` holds the u64 `chain_id` to encode.
      - `x11` holds `successful_validation` (low byte = 0 or 1).

    The body writes the 41-byte SSZ encoding of
    `StatelessValidationResult` at `OUTPUT_BASE` and falls through to
    the caller's halt stub. -/
def serialize_stateless_output : Program :=
  LI .x6 OUTPUT_BASE ;;
  SD .x6 .x0 0  ;;
  SD .x6 .x0 8  ;;
  SD .x6 .x0 16 ;;
  SD .x6 .x0 24 ;;
  SLLI .x7 .x10 8 ;;
  OR' .x7 .x7 .x11 ;;
  SD .x6 .x7 32 ;;
  SRLI .x7 .x10 56 ;;
  SB .x6 .x7 40

end EvmAsm.Stateless.SSZ.Encode
