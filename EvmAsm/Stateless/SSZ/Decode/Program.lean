/-
  EvmAsm.Stateless.SSZ.Decode.Program

  Minimal SSZ decoder slice (PR3): read `chain_config.chain_id` from a
  host-supplied `SszStatelessInput` blob on `INPUT_ADDR`.

  Reference: `execution-specs/src/ethereum/forks/amsterdam/stateless_ssz.py`
  (`class SszStatelessInput(Container)`,
   `class SszChainConfig(Container)`).

  ## SSZ wire layout of `SszStatelessInput`

  Container fixed-header section (20 bytes):

  | Offset | Size | Field                              | Wire form     |
  |--------|------|------------------------------------|---------------|
  |  0..4  |    4 | `new_payload_request` offset       | uint32 LE     |
  |  4..8  |    4 | `witness` offset                   | uint32 LE     |
  |  8..16 |    8 | `chain_config.chain_id` (inline)   | uint64 LE     |
  | 16..20 |    4 | `public_keys` offset               | uint32 LE     |

  The variable-size body follows the header. PR3 only reads
  `chain_id`; the offsets / variable body are ignored for now.

  ## ziskemu input-buffer layout

  Per `EvmAsm/Codegen/Programs.lean`:

      INPUT_ADDR +  0..8   : ziskemu metadata (zero)
      INPUT_ADDR +  8..16  : LE u64 length of the SSZ blob
      INPUT_ADDR + 16..    : SSZ-encoded SszStatelessInput

  So `chain_id` lives at `INPUT_ADDR + 16 + 8 = INPUT_ADDR + 24`. The
  base address is 8-byte aligned (`INPUT_ADDR = 0x40000000`), and
  `24 mod 8 = 0`, so an `LD` at offset 24 satisfies
  `isValidDwordAccess`.

  ## Memory layout (preconditions)
  - `INPUT_BASE = 0x40000000` (matches `EvmAsm.Codegen.INPUT_ADDR`).
  - `[INPUT_BASE + 16, INPUT_BASE + 36)` lies inside the input zone
    (`INPUT_MEM_START..INPUT_MEM_END`, see issue #5164).
  - The host writes a length-prefixed SSZ blob of at least 20 data
    bytes (the full SszStatelessInput fixed header).

  ## Side effects
  - `read_chain_id` loads `chain_id` (u64 LE) into `x10`; clobbers
    `x11`.
  - `decode_validation_bit` reads offset_1 and offset_3 from the
    fixed header (u32 LE each), computes
    `witness_body_length = offset_3 - offset_1`, and writes
    `1` into `x11` iff that length equals `12` (the size of an empty
    `SszExecutionWitness`, which is just its 3-entry offsets table).
    Clobbers `x12..x14`.

  ## PR4 framing of the bool

  An empty witness body (state = codes = headers = empty lists) has
  exactly 12 bytes on the wire: the three u32 offsets, each pointing
  at byte 12 (= end of the offsets table, start of the empty body).
  PR4 surfaces "witness is empty" as the `successful_validation`
  flag in the output. Future PRs replace this with the real STF
  verdict.

  ## Frame
  - `read_chain_id`: 2 instructions (1 LI + 1 LD).
  - `decode_validation_bit`: 6 instructions
    (1 LI + 2 LWU + 1 SUB + 1 XORI + 1 SLTIU).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout

namespace EvmAsm.Stateless.SSZ.Decode

open EvmAsm.Rv64

/-- ziskemu private-input region base. Mirrors
    `EvmAsm.Codegen.Programs.INPUT_ADDR`. -/
def INPUT_BASE : Word := 0x40000000

/-- Byte offset (from `INPUT_BASE`) of `chain_config.chain_id` in the
    SSZ-encoded `SszStatelessInput`:

        INPUT_DATA_OFFSET (16, see Codegen) + SSZ header offset (8) = 24
-/
def CHAIN_ID_BYTE_OFFSET : BitVec 12 := 24

/-- Byte offset (from `INPUT_BASE`) of `offset_1` (the SSZ header
    pointer to the `witness` field): `16 + 4 = 20`. -/
def WITNESS_OFFSET_BYTE : BitVec 12 := 20

/-- Byte offset (from `INPUT_BASE`) of `offset_3` (the SSZ header
    pointer to the `public_keys` field, == the end of `witness`):
    `16 + 16 = 32`. -/
def PUBLIC_KEYS_OFFSET_BYTE : BitVec 12 := 32

/-- Size in bytes of an empty `SszExecutionWitness` body (just the
    three u32 offsets for `state`, `codes`, `headers`). -/
def EMPTY_WITNESS_BODY_LEN : BitVec 12 := 12

/-- Read `chain_config.chain_id` from `INPUT_BASE` into `x10`.

    Postcondition: `x10` holds the host-supplied `chain_id` as a u64.
    Clobbers `x11`. -/
def read_chain_id : Program :=
  LI .x11 INPUT_BASE ;;
  LD .x10 .x11 CHAIN_ID_BYTE_OFFSET

/-- Compute the PR4 `successful_validation` bit by reading the outer
    `SszStatelessInput` offsets table and checking whether the
    `witness` body is empty (length 12).

    Postcondition: `x11` holds `1` if `offset_3 - offset_1 == 12`,
    otherwise `0`. Clobbers `x12`, `x13`, `x14`. -/
def decode_validation_bit : Program :=
  LI .x12 INPUT_BASE ;;
  LWU .x13 .x12 WITNESS_OFFSET_BYTE ;;
  LWU .x14 .x12 PUBLIC_KEYS_OFFSET_BYTE ;;
  SUB .x14 .x14 .x13 ;;
  XORI .x14 .x14 EMPTY_WITNESS_BODY_LEN ;;
  SLTIU .x11 .x14 1

end EvmAsm.Stateless.SSZ.Decode
