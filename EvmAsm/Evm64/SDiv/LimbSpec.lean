/-
  EvmAsm.Evm64.SDiv.LimbSpec

  Per-block / per-limb cpsTriple specs for SDIV sub-blocks (sign
  extraction, abs negation, callable-divide JAL, sign-correction).

  Per `OPCODE_TEMPLATE.md`, each sub-block gets exactly one cpsTriple
  lemma; later Compose slices chain them.
-/

import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- CodeReq for `evm_sdiv_sign_bit_block` at byte offset `base`. -/
abbrev evm_sdiv_sign_bit_block_code
    (addrReg signReg : Reg) (topLimbOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_sign_bit_block addrReg signReg topLimbOff)

/-- 2-instruction leaf spec: load `topLimbOff(addrReg)` into `signReg`,
    then shift right logically by 63 to expose the top bit. The
    post-state's `signReg` holds `topLimbVal >>> 63` (i.e. `0` for
    non-negative inputs and `1` for negative inputs).

    Requires `signReg ≠ x0`; separation of `(addrReg ↦ᵣ _)` and
    `(signReg ↦ᵣ _)` in the precondition implicitly forces
    `addrReg ≠ signReg`. -/
theorem evm_sdiv_sign_bit_block_spec_within
    (addrReg signReg : Reg) (topLimbOff : BitVec 12)
    (vAddr sOld topLimbVal : Word) (base : Word)
    (hsign_ne_x0 : signReg ≠ .x0) :
    let code := evm_sdiv_sign_bit_block_code addrReg signReg topLimbOff base
    cpsTripleWithin 2 base (base + 8) code
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ sOld) **
       ((vAddr + signExtend12 topLimbOff) ↦ₘ topLimbVal))
      ((addrReg ↦ᵣ vAddr) ** (signReg ↦ᵣ (topLimbVal >>> (63 : BitVec 6).toNat)) **
       ((vAddr + signExtend12 topLimbOff) ↦ₘ topLimbVal)) := by
  have L := ld_spec_gen_within signReg addrReg vAddr sOld topLimbVal
              topLimbOff base hsign_ne_x0
  have S := srli_spec_gen_same_within signReg topLimbVal (63 : BitVec 6)
              (base + 4) hsign_ne_x0
  runBlock L S

/-- CodeReq for one conditional-negation limb step at byte offset `base`. -/
abbrev evm_sdiv_cond_negate_limb_step_code
    (addrReg carryInReg maskReg valueReg carryReg : Reg)
    (limbOff : BitVec 12) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (evm_sdiv_cond_negate_limb_step addrReg carryInReg maskReg valueReg carryReg
      limbOff)

/-- 5-instruction conditional-negation limb step with the incoming carry
    held in a separate register: `LD; XOR; ADD; SLTU; SD`. This is the
    leaf used for limb 0 of the 256-bit SDIV conditional-negation block,
    where `carryInReg` is the sign register. -/
theorem evm_sdiv_cond_negate_limb_step_spec_within
    (addrReg carryInReg maskReg valueReg carryReg : Reg)
    (limbOff : BitVec 12)
    (vAddr carryIn mask valueOld carryOld limbVal : Word) (base : Word)
    (hvalue_ne_x0 : valueReg ≠ .x0) (hcarry_ne_x0 : carryReg ≠ .x0) :
    let mem := vAddr + signExtend12 limbOff
    let xored := limbVal ^^^ mask
    let sum := xored + carryIn
    let carryOut := if BitVec.ult sum carryIn then (1 : Word) else 0
    let code :=
      evm_sdiv_cond_negate_limb_step_code addrReg carryInReg maskReg valueReg
        carryReg limbOff base
    cpsTripleWithin 5 base (base + 20) code
      ((addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
       (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ valueOld) **
       (carryReg ↦ᵣ carryOld) ** (mem ↦ₘ limbVal))
      ((addrReg ↦ᵣ vAddr) ** (carryInReg ↦ᵣ carryIn) **
       (maskReg ↦ᵣ mask) ** (valueReg ↦ᵣ sum) **
       (carryReg ↦ᵣ carryOut) ** (mem ↦ₘ sum)) := by
  intro mem xored sum carryOut code
  have L := ld_spec_gen_within valueReg addrReg vAddr valueOld limbVal
    limbOff base hvalue_ne_x0
  have X := xor_spec_gen_rd_eq_rs1_within valueReg maskReg limbVal mask
    (base + 4) hvalue_ne_x0
  have A := add_spec_gen_rd_eq_rs1_within valueReg carryInReg xored carryIn
    (base + 8) hvalue_ne_x0
  have C := sltu_spec_gen_within carryReg valueReg carryInReg carryOld sum carryIn
    (base + 12) hcarry_ne_x0
  have S := sd_spec_gen_within addrReg valueReg vAddr sum limbVal limbOff
    (base + 16)
  runBlock L X A C S

/-- CodeReq for `evm_sdiv_save_ra_block` at byte offset `base`. -/
abbrev evm_sdiv_save_ra_block_code (savedRaReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg)

/-- 1-instruction leaf spec: `ADDI savedRaReg, x1, 0` copies the current
    `x1` (return address) into a preserved scratch register. The block is
    used to save `ra` across a nested `JAL` to `evm_div_callable` (which
    clobbers `x1`). Mirrors `evm_sdiv_div_call_block_spec_within`. -/
theorem evm_sdiv_save_ra_block_spec_within
    (savedRaReg : Reg) (vRa vSavedOld : Word) (base : Word)
    (hsaved_ne_x0 : savedRaReg ≠ .x0) :
    let code := evm_sdiv_save_ra_block_code savedRaReg base
    cpsTripleWithin 1 base (base + 4) code
      ((.x1 ↦ᵣ vRa) ** (savedRaReg ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) ** (savedRaReg ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  show cpsTripleWithin 1 base (base + 4)
    (CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg)) _ _
  rw [show CodeReq.ofProg base (evm_sdiv_save_ra_block savedRaReg) =
      CodeReq.singleton base (.ADDI savedRaReg .x1 0) from CodeReq.ofProg_singleton]
  exact addi_spec_within savedRaReg .x1 vRa vSavedOld 0 base hsaved_ne_x0

/-- CodeReq for `evm_sdiv_saved_ra_ret_block` at byte offset `base`. -/
abbrev evm_sdiv_saved_ra_ret_block_code (savedRaReg : Reg) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg)

/-- 1-instruction leaf spec: `JALR x0, savedRaReg, 0` returns to the
    address saved by `evm_sdiv_save_ra_block`. Exit pc is
    `(vSavedRa + 0) &&& ~~~1` per the standard `JALR x0` semantics. The
    `savedRaReg` value is preserved. Mirrors `ret_spec_within`. -/
theorem evm_sdiv_saved_ra_ret_block_spec_within
    (savedRaReg : Reg) (vSavedRa : Word) (base : Word) :
    let code := evm_sdiv_saved_ra_ret_block_code savedRaReg base
    cpsTripleWithin 1 base
        ((vSavedRa + signExtend12 (0 : BitVec 12)) &&& ~~~1) code
      (savedRaReg ↦ᵣ vSavedRa)
      (savedRaReg ↦ᵣ vSavedRa) := by
  show cpsTripleWithin 1 base _
    (CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg)) _ _
  rw [show CodeReq.ofProg base (evm_sdiv_saved_ra_ret_block savedRaReg) =
      CodeReq.singleton base (.JALR .x0 savedRaReg 0) from CodeReq.ofProg_singleton]
  exact jalr_x0_spec_gen_within savedRaReg vSavedRa 0 base

/-- CodeReq for `evm_sdiv_div_call_block` at byte offset `base`. -/
abbrev evm_sdiv_div_call_block_code (divOff : BitVec 21) (base : Word) : CodeReq :=
  CodeReq.ofProg base (evm_sdiv_div_call_block divOff)

/-- 1-instruction leaf spec: near-`JAL` from SDIV into the unsigned
    `evm_div_callable` shim. Control transfers to
    `base + signExtend21 divOff` and `.x1` is updated with the return
    address `base + 4`. Argument-marshalling (placing both operands in
    the LP64 a-slots) is handled by the surrounding scaffold and is not
    part of this leaf cpsTriple. Mirrors `exp_square_block_spec_within`
    (`Evm64/Exp/LimbSpec.lean`). -/
theorem evm_sdiv_div_call_block_spec_within
    (divOff : BitVec 21) (vOld : Word) (base : Word) :
    let code := evm_sdiv_div_call_block_code divOff base
    cpsTripleWithin 1 base (base + signExtend21 divOff) code
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ (base + 4)) := by
  show cpsTripleWithin 1 base (base + signExtend21 divOff)
    (CodeReq.ofProg base (evm_sdiv_div_call_block divOff)) _ _
  rw [show CodeReq.ofProg base (evm_sdiv_div_call_block divOff) =
      CodeReq.singleton base (.JAL .x1 divOff) from CodeReq.ofProg_singleton]
  exact jal_spec_within .x1 vOld divOff base (by nofun)

end EvmAsm.Evm64
