/-
  EvmAsm.Evm64.SDiv.Program

  Signed division opcode SDIV (`SDIV(a, b)` = signed-quotient under EVM
  rules) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6).

  The actual `evm_sdiv : Program` will be defined in slice
  evm-asm-01uh. Per `docs/sdiv-smod-design.md` the algorithm is

      1. extract sign of each operand (top bit of limb 3)
      2. conditionally two's-complement negate operands so both are
         non-negative; remember the sign-pair
      3. JAL to an `evm_div_callable` shim (LP64) for unsigned division
      4. conditionally negate the quotient based on `sign(a) XOR sign(b)`
      5. apply the SDIV(-2^255, -1) = -2^255 fast-path overflow rule

  This file currently has no `evm_sdiv` definition; later slices will
  add it without breaking the umbrella import graph.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Load the top limb of a 256-bit word and extract its sign bit.

    On entry, `addrReg + topLimbOff` points at limb 3 of the word.
    On exit, `signReg` is `0` for non-negative inputs and `1` for
    negative inputs. The block is intentionally register-parametric so
    the SDIV and SMOD callers can reuse it for dividend/divisor sign
    probes before normalizing operands in place.

    2 instructions: `LD; SRLI 63`. -/
def evm_sdiv_sign_bit_block
    (addrReg signReg : Reg) (topLimbOff : BitVec 12) : Program :=
  LD signReg addrReg topLimbOff ;;
  SRLI signReg signReg 63

theorem evm_sdiv_sign_bit_block_length
    (addrReg signReg : Reg) (topLimbOff : BitVec 12) :
    (evm_sdiv_sign_bit_block addrReg signReg topLimbOff).length = 2 := by
  unfold evm_sdiv_sign_bit_block LD SRLI single seq Program
  rfl

theorem evm_sdiv_sign_bit_block_byte_length
    (addrReg signReg : Reg) (topLimbOff : BitVec 12) :
    4 * (evm_sdiv_sign_bit_block addrReg signReg topLimbOff).length = 8 := by
  rw [evm_sdiv_sign_bit_block_length]

/-- Conditionally negate a 256-bit word in place.

    `signReg` must hold `0` or `1`. The block computes
    `maskReg := 0 - signReg`, xors all four limbs with that mask, and
    then adds the incoming carry (`signReg` for limb 0, propagated
    through `carryReg` for limbs 1..3). When `signReg = 0` this is the
    identity; when `signReg = 1` it is two's-complement negation.

    The limb offsets are parameters so callers can use the same block
    for the dividend, divisor, and quotient/result windows. The scratch
    registers `maskReg`, `valueReg`, and `carryReg` are clobbered.

    21 instructions: one `SUB` mask setup plus four 5-instruction limb
    steps (`LD; XOR; ADD; SLTU; SD`). -/
def evm_sdiv_cond_negate_256_block
    (addrReg signReg maskReg valueReg carryReg : Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) : Program :=
  SUB maskReg .x0 signReg ;;
  LD valueReg addrReg limb0Off ;;
  XOR' valueReg valueReg maskReg ;;
  ADD valueReg valueReg signReg ;;
  SLTU carryReg valueReg signReg ;;
  SD addrReg valueReg limb0Off ;;
  LD valueReg addrReg limb1Off ;;
  XOR' valueReg valueReg maskReg ;;
  ADD valueReg valueReg carryReg ;;
  SLTU carryReg valueReg carryReg ;;
  SD addrReg valueReg limb1Off ;;
  LD valueReg addrReg limb2Off ;;
  XOR' valueReg valueReg maskReg ;;
  ADD valueReg valueReg carryReg ;;
  SLTU carryReg valueReg carryReg ;;
  SD addrReg valueReg limb2Off ;;
  LD valueReg addrReg limb3Off ;;
  XOR' valueReg valueReg maskReg ;;
  ADD valueReg valueReg carryReg ;;
  SLTU carryReg valueReg carryReg ;;
  SD addrReg valueReg limb3Off

theorem evm_sdiv_cond_negate_256_block_length
    (addrReg signReg maskReg valueReg carryReg : Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) :
    (evm_sdiv_cond_negate_256_block addrReg signReg maskReg valueReg carryReg
      limb0Off limb1Off limb2Off limb3Off).length = 21 := by
  unfold evm_sdiv_cond_negate_256_block SUB LD XOR' ADD SLTU SD single seq Program
  rfl

theorem evm_sdiv_cond_negate_256_block_byte_length
    (addrReg signReg maskReg valueReg carryReg : Reg)
    (limb0Off limb1Off limb2Off limb3Off : BitVec 12) :
    4 * (evm_sdiv_cond_negate_256_block addrReg signReg maskReg valueReg carryReg
      limb0Off limb1Off limb2Off limb3Off).length = 84 := by
  rw [evm_sdiv_cond_negate_256_block_length]

/-- Near-call block from SDIV into the unsigned `evm_div_callable` body.
    The concrete signed 21-bit offset is pinned by the eventual top-level
    `evm_sdiv` layout. -/
def evm_sdiv_div_call_block (divOff : BitVec 21) : Program :=
  JAL .x1 divOff

theorem evm_sdiv_div_call_block_length (divOff : BitVec 21) :
    (evm_sdiv_div_call_block divOff).length = 1 := rfl

theorem evm_sdiv_div_call_block_byte_length (divOff : BitVec 21) :
    4 * (evm_sdiv_div_call_block divOff).length = 4 := by
  rw [evm_sdiv_div_call_block_length]

example :
    (evm_sdiv_sign_bit_block .x12 .x5 24).length +
      (evm_sdiv_cond_negate_256_block .x12 .x5 .x6 .x7 .x11 0 8 16 24).length +
      (evm_sdiv_div_call_block 0).length = 24 := by
  native_decide

end EvmAsm.Evm64
