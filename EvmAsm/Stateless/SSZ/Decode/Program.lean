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
  - `[INPUT_BASE + 16, INPUT_BASE + 16 + N)` is host-supplied SSZ
    data; PR5 reads bytes 0..4 (offset_1), 16..20 (offset_3), and
    inside the witness section at byte 8..12 (offset_headers).
  - The input zone (`INPUT_MEM_START..INPUT_MEM_END`, see #5164)
    admits all of these.
  - All reads are 4-byte aligned: the SSZ blob starts at the
    8-byte-aligned `INPUT_BASE + 16`, every nested container's
    fixed header begins on a 4-byte boundary in our fixtures, and
    the offsets we read all target 4-byte-aligned positions.

  ## Side effects
  - `read_chain_id` loads `chain_id` (u64 LE) into `x10`; clobbers
    `x11`.
  - `decode_validation_bit` chases offset_1 (outer SSZ →
    witness_addr), the witness section's third inner u32
    (witness_addr → headers_addr), and offset_3 (outer SSZ →
    public_keys_addr = headers_end_addr). It then writes `1` into
    `x11` iff `headers_end_addr - headers_addr == 0`, i.e. the
    `witness.headers` SSZ list section is empty. The helper also
    **leaves** `headers_addr` in `x17` and
    `headers_byte_length` in `x14`, so the PR6
    `decode_header_count` follow-up can reuse both without
    redoing the offset walk. Clobbers `x12..x15`, `x17`.
  - `decode_header_count` (PR6) reads the first u32 of the
    `witness.headers` list (= `4 * header_count` for a non-empty
    list, or out-of-bounds memory for an empty list -- which we
    avoid via a BEQ guard), divides by 4, and leaves
    `header_count` in `x16`. Sets `x16 = 0` when the headers list
    is empty. Clobbers `x16`.

  ## PR5/PR6 framing

  PR4 set the bool from whether the **whole** `SszExecutionWitness`
  body was empty (length 12). PR5 narrows this: the bool reflects
  whether `witness.headers` specifically is empty, regardless of
  what's in `state` or `codes`. PR6 adds `header_count` as a
  diagnostic u64 written past the 41-byte SSZ result -- the encoder
  surfaces it at `OUTPUT_ADDR + 48`. This is the first guest-side
  observable derived from the **content** of the headers list,
  not just its length.

  Future PRs replace the validation bool with the real STF verdict
  and iterate over headers via the same `headers_addr` / count.

  ## Frame
  - `read_chain_id`: 2 instructions (1 LI + 1 LD).
  - `decode_validation_bit`: 10 instructions.
  - `decode_header_count`: 4 instructions
    (1 ADDI + 1 BEQ guard + 1 LWU + 1 SRLI).
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

/-- ziskemu's 16-byte preamble at `INPUT_ADDR`: 8 bytes of zero
    metadata + 8 bytes of u64 length prefix. The SSZ blob proper
    starts at `INPUT_BASE + INPUT_DATA_OFFSET`. -/
def INPUT_DATA_OFFSET : BitVec 12 := 16

/-- SSZ byte offset of `offset_1` (the outer-container pointer to
    the `witness` field). Relative to the SSZ blob start. -/
def OUTER_WITNESS_OFFSET_SSZ : BitVec 12 := 4

/-- SSZ byte offset of `offset_3` (the outer-container pointer to
    the `public_keys` field, == end of the `witness` section).
    Relative to the SSZ blob start. -/
def OUTER_PUBLIC_KEYS_OFFSET_SSZ : BitVec 12 := 16

/-- Byte offset within an `SszExecutionWitness` section of its
    third u32 (`offset_2` = `headers` offset). The witness's fixed
    header is three u32s: `state`, `codes`, `headers`. -/
def WITNESS_HEADERS_INNER_OFFSET : BitVec 12 := 8

/-- Read `chain_config.chain_id` from `INPUT_BASE` into `x10`.

    Postcondition: `x10` holds the host-supplied `chain_id` as a u64.
    Clobbers `x11`. -/
def read_chain_id : Program :=
  LI .x11 INPUT_BASE ;;
  LD .x10 .x11 CHAIN_ID_BYTE_OFFSET

/-- Compute the PR5 `successful_validation` bit by chasing the outer
    SszStatelessInput → witness → headers offset chain and checking
    whether the `witness.headers` list section is empty.

    Register usage:
      x12 : INPUT_BASE, then INPUT_BASE + INPUT_DATA_OFFSET
            (start of the SSZ blob in memory)
      x13 : offset_1, then witness_addr
      x14 : (scratch) inner offset_headers, then
            (output, preserved) headers_byte_length
      x15 : offset_3, then headers_end_addr
      x17 : (output, preserved) headers_addr

    Postcondition:
      x11 = 1 iff headers_byte_length == 0, else 0.
      x14 = headers_byte_length.
      x17 = headers_addr.
    Clobbers `x12..x15`, `x17`. -/
def decode_validation_bit : Program :=
  LI .x12 INPUT_BASE ;;
  LWU .x13 .x12 (INPUT_DATA_OFFSET + OUTER_WITNESS_OFFSET_SSZ) ;;
  ADDI .x12 .x12 INPUT_DATA_OFFSET ;;
  ADD .x13 .x12 .x13 ;;
  LWU .x14 .x13 WITNESS_HEADERS_INNER_OFFSET ;;
  ADD .x17 .x13 .x14 ;;
  LWU .x15 .x12 OUTER_PUBLIC_KEYS_OFFSET_SSZ ;;
  ADD .x15 .x12 .x15 ;;
  SUB .x14 .x15 .x17 ;;
  SLTIU .x11 .x14 1

/-- Compute `header_count` for the diagnostic field at
    `OUTPUT_ADDR + 48`. Reads the first u32 of the headers list
    (= `4 * count` for non-empty lists) and divides by 4. When the
    headers list is empty, skips the load (so we don't read past
    the SSZ blob into ziskemu padding) and leaves `x16 = 0`.

    Precondition (left by `decode_validation_bit`):
      x14 = headers_byte_length, x17 = headers_addr.
    Postcondition: x16 = header_count.
    Clobbers `x16`. -/
def decode_header_count : Program :=
  ADDI .x16 .x0 0 ;;
  -- skip the next 2 instructions if x14 == 0 (empty headers list)
  BEQ .x14 .x0 12 ;;
  LWU .x16 .x17 0 ;;
  SRLI .x16 .x16 2

end EvmAsm.Stateless.SSZ.Decode
