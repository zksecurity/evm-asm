/-
  EvmAsm.Evm64.Calldata.LoadProgram

  Straight-line byte-window core for the EVM `CALLDATALOAD` opcode
  (GH #104).  This program shape handles the in-bounds 32-byte read:
  pop the calldata offset from the EVM stack, add it to the environment's
  `callDataPtr`, pack four big-endian 8-byte limbs with LBU/SLLI/OR, and
  store the resulting 256-bit word back to the same EVM stack slot.

  The full opcode spec still needs the bounds-check/zero-padding wrapper
  around this core.  Keeping the byte-window core separate gives that
  later proof a compact block to compose.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64
namespace Calldata

open EvmAsm.Rv64

/-- Pack `k + 1` calldata bytes, starting at `addrReg + limbStart`, into
    `accReg` in big-endian order.  The first byte seeds the accumulator;
    each later byte shifts the accumulator left by 8 and ORs in the next
    zero-extended LBU result. -/
private def calldataload_byte_pack
    (addrReg byteReg accReg : Reg) (limbStart : Nat) : Nat → Program
  | 0 =>
      LBU accReg addrReg (BitVec.ofNat 12 limbStart)
  | k + 1 =>
      calldataload_byte_pack addrReg byteReg accReg limbStart k ;;
      LBU byteReg addrReg (BitVec.ofNat 12 (limbStart + (k + 1))) ;;
      SLLI accReg accReg (BitVec.ofNat 6 8) ;;
      OR' accReg accReg byteReg

/-- Pack one output limb of the 32-byte CALLDATALOAD window and store it
    at the canonical EVM-stack limb offset.  Limb `0` is the low 64 bits,
    so it consumes calldata bytes 24..31; limb `3` consumes bytes 0..7. -/
private def calldataload_one_limb
    (addrReg byteReg accReg : Reg) (j : Nat) : Program :=
  calldataload_byte_pack addrReg byteReg accReg (8 * (3 - j)) 7 ;;
  SD .x12 accReg (BitVec.ofNat 12 (8 * j))

/-- Straight-line in-bounds CALLDATALOAD byte-window core.

    `envPtrReg` is expected to hold `env.callDataPtr`.  The program pops
    the low 64-bit offset limb from the EVM stack at `x12`, computes the
    source byte pointer, packs the 32-byte calldata window, and stores
    the result back to the same stack slot.  The stack pointer is
    unchanged because CALLDATALOAD pops one word and pushes one word. -/
def evm_calldataload_window
    (offReg byteReg accReg addrReg envPtrReg : Reg) : Program :=
  LD offReg .x12 0 ;;
  ADD addrReg envPtrReg offReg ;;
  calldataload_one_limb addrReg byteReg accReg 0 ;;
  calldataload_one_limb addrReg byteReg accReg 1 ;;
  calldataload_one_limb addrReg byteReg accReg 2 ;;
  calldataload_one_limb addrReg byteReg accReg 3

/-- Code requirement for `evm_calldataload_window` placed at `base`. -/
abbrev evm_calldataload_window_code
    (offReg byteReg accReg addrReg envPtrReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg)

/-- Instruction length of the byte-pack block: one seed `LBU`, then
    `k` repetitions of `LBU; SLLI; OR`. -/
theorem calldataload_byte_pack_length
    (addrReg byteReg accReg : Reg) (limbStart k : Nat) :
    (calldataload_byte_pack addrReg byteReg accReg limbStart k).length =
      1 + 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [calldataload_byte_pack, LBU, SLLI, OR', single, seq,
        Program.length_append, ih, Nat.mul_succ]
      omega

/-- One packed output limb is 23 instructions. -/
theorem calldataload_one_limb_length
    (addrReg byteReg accReg : Reg) (j : Nat) :
    (calldataload_one_limb addrReg byteReg accReg j).length = 23 := by
  simp [calldataload_one_limb, SD, single, seq, Program.length_append,
    calldataload_byte_pack_length]

/-- `evm_calldataload_window` is 94 RISC-V instructions. -/
theorem evm_calldataload_window_program_length
    (offReg byteReg accReg addrReg envPtrReg : Reg) :
    (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg).length =
      94 := by
  simp [evm_calldataload_window, LD, ADD, single, seq, Program.length_append,
    calldataload_one_limb_length]

/-- `evm_calldataload_window` occupies 376 bytes in RV64 code memory. -/
theorem evm_calldataload_window_byte_length
    (offReg byteReg accReg addrReg envPtrReg : Reg) :
    4 * (evm_calldataload_window offReg byteReg accReg addrReg envPtrReg).length =
      376 := by
  rw [evm_calldataload_window_program_length]

/-- Byte offset of the offset-load instruction. -/
theorem evm_calldataload_window_offset_load_byte_off : 4 * 0 = 0 := by
  rfl

/-- Byte offset of the source-address ADD instruction. -/
theorem evm_calldataload_window_addr_add_byte_off : 4 * 1 = 4 := by
  rfl

/-- Byte offset of the seed LBU inside a byte-pack block. -/
theorem calldataload_byte_pack_seed_byte_off : 4 * 0 = 0 := by
  rfl

/-- Byte offset of repeated LBU instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_lbu_byte_off (i : Nat) :
    4 * (1 + 3 * i) = 4 + 12 * i := by
  omega

/-- Byte offset of repeated SLLI instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_slli_byte_off (i : Nat) :
    4 * (1 + 3 * i + 1) = 8 + 12 * i := by
  omega

/-- Byte offset of repeated OR instruction `i` inside a byte-pack block. -/
theorem calldataload_byte_pack_or_byte_off (i : Nat) :
    4 * (1 + 3 * i + 2) = 12 + 12 * i := by
  omega

/-- Byte offset of the final stack-store inside one output-limb block. -/
theorem calldataload_one_limb_store_byte_off : 4 * 22 = 88 := by
  rfl

/-- Byte offset of CALLDATALOAD output-limb block `j` within the window core. -/
theorem evm_calldataload_window_limb_block_byte_off (j : Nat) :
    4 * (2 + 23 * j) = 8 + 92 * j := by
  omega

/-- Byte offset of the final stack-store in output-limb block `j`. -/
theorem evm_calldataload_window_limb_store_byte_off (j : Nat) :
    4 * (2 + 23 * j + 22) = 96 + 92 * j := by
  omega

end Calldata
end EvmAsm.Evm64
