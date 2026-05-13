/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

  Small top-level EXP code-bundle specs split out of `Compose/Base.lean` to
  keep the base composition module under the Compose file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBase
import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks
import EvmAsm.Evm64.Exp.Compose.TopIterSubs
import EvmAsm.Evm64.Exp.Compose.TopLoopControl
import EvmAsm.Evm64.Exp.Compose.TopCallSubs
import EvmAsm.Evm64.Exp.Compose.TopJalBlocks
import EvmAsm.Evm64.Exp.Compose.TopSquaringMarshalBlocks
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.SquaringCallSeq

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Conditional-multiply factor-1 marshal spec lifted to the top-level EXP
    code bundle: at offset `base + 148`, copies result limbs from scratch to
    factor1, exits at `base + 180`. -/
theorem exp_cond_mul_marshal_factor1_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 148) (base + 180)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_factor1_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 148)
  have hexit : ((base + 148 : Word) + 32) = base + 180 := by bv_omega
  rw [hexit] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_marshal_factor1_sub)

/-- Conditional-multiply factor-2 marshal (from EVM-stack base slot) spec
    lifted to the top-level EXP code bundle: at offset `base + 180`, copies
    base limbs `a` from the EVM-stack window at `evmSp + -64..-40` into the
    factor2 slot, exits at `base + 212`. -/
theorem exp_cond_mul_marshal_a_to_factor2_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 8 (base + 180) (base + 212)
      (evmExpCode base mulOff skipOff backOff)
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3)) := by
  have h := EvmAsm.Evm64.exp_loop_marshal_a_to_factor2_ofProg_spec_within
    evmSp tOld a0 a1 a2 a3 d0 d1 d2 d3 (base + 180)
  have hexit : ((base + 180 : Word) + 32) = base + 212 := by bv_omega
  rw [hexit] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_marshal_a_to_factor2_sub)

/-- Conditional-multiply un-marshal-and-restore spec lifted to the top-level
    EXP code bundle: at offset `base + 216`, copies factor1 limbs back to
    scratch and decrements `x12` by 32, exits at `base + 252`. -/
theorem exp_cond_mul_un_marshal_and_restore_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word) (base : Word) :
    cpsTripleWithin 9 (base + 216) (base + 252)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (-32 : BitVec 12))) **
       (.x5 ↦ᵣ d3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3)) := by
  have h := EvmAsm.Evm64.exp_loop_un_marshal_and_restore_ofProg_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 216)
  have hexit : ((base + 216 : Word) + 36) = base + 252 := by bv_omega
  rw [hexit] at h
  exact cpsTripleWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_un_marshal_and_restore_sub)

/-- Conditional-multiply BEQ skip-gate spec lifted to the top-level EXP code
    bundle: at offset `base + 144`, branches on `x10 == 0` to the cond-mul
    skip target `(base + 144) + signExtend13 skipOff`, otherwise falls
    through to `base + 148` (the cond-mul JAL). -/
theorem exp_cond_mul_beq_evm_exp_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v10 : Word) (base target : Word)
    (htarget : (base + 144 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 144)
      (evmExpCode base mulOff skipOff backOff)
      ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝)
      (base + 148) ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x10 .x0 skipOff v10 (0 : Word)
    (base + 144)
  rw [htarget] at h
  have hnext : ((base + 144 : Word) + 4) = base + 148 := by bv_omega
  rw [hnext] at h
  exact cpsBranchWithin_extend_code (h := h)
    (hmono := evmExpCode_cond_mul_beq_sub)

/-- Saved-bit conditional-multiply BEQ skip-gate spec lifted to the corrected
    saved-bit top-level EXP code bundle: at offset `base + 148`, branches on
    `x18 == 0` to the cond-mul skip target, otherwise falls through to
    `base + 152` (the cond-mul taken block). -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) := by
  have h := EvmAsm.Rv64.beq_spec_within .x18 .x0 skipOff v18 (0 : Word)
    (base + 148)
  rw [htarget] at h
  have hnext : ((base + 148 : Word) + 4) = base + 152 := by bv_omega
  rw [hnext] at h
  exact cpsBranchWithin_extend_code (h := h)
    (hmono := evmExpMsbSavedBitCode_cond_mul_beq_sub)


/-- Squaring-call marshal prefix and JAL lifted to the top-level EXP code bundle. -/
theorem exp_squaring_marshal_pair_then_square_evm_exp_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word)
    (hmul : ((base + 104) + signExtend21 mulOff : Word) = mulTarget) :
    cpsTripleWithin 17 (base + 40) mulTarget
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ r3) **
       (.x1 ↦ᵣ (base + 108))) := by
  have h := EvmAsm.Evm64.exp_loop_squaring_marshal_pair_then_square_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 mulOff (base + 40)
  have htarget : (((base + 40) + 64 : Word) + signExtend21 mulOff) = mulTarget := by
    rw [show ((base + 40 : Word) + 64) = base + 104 by bv_omega]
    exact hmul
  rw [htarget] at h
  have hret : ((base + 40 : Word) + 68) = base + 108 := by bv_omega
  rw [hret] at h
  exact cpsTripleWithin_extend_code (h := h) (hmono := evmExpCode_iter_squaring_sub)

/-- Conditional-multiply marshal pair lifted to the top-level EXP code bundle. -/
theorem exp_cond_mul_marshal_pair_evm_exp_spec_within
    (sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 16 (base + 148) (base + 212)
      (evmExpCode base mulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ a3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ a3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  have h := EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_spec_within
    sp evmSp tOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3 (base + 148)
  have hnext : ((base + 148 : Word) + 64) = base + 212 := by bv_omega
  rw [hnext] at h
  have hmono :
      ∀ addr instr, EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code
          (base + 148) addr = some instr →
        (evmExpCode base mulOff skipOff backOff) addr = some instr := by
    intro addr instr hcode
    unfold EvmAsm.Evm64.exp_loop_cond_mul_marshal_pair_code at hcode
    exact CodeReq.union_sub
      (evmExpCode_cond_mul_marshal_factor1_sub (base := base)
        (mulOff := mulOff) (skipOff := skipOff) (backOff := backOff))
      (fun a i hfactor2 => by
        have haddr : ((base + 148 : Word) + 32) = base + 180 := by bv_omega
        rw [haddr] at hfactor2
        exact evmExpCode_cond_mul_marshal_a_to_factor2_sub
          (base := base) (mulOff := mulOff) (skipOff := skipOff)
          (backOff := backOff) a i hfactor2)
      addr instr hcode
  exact cpsTripleWithin_extend_code (h := h) (hmono := hmono)

end EvmAsm.Evm64.Exp.Compose
