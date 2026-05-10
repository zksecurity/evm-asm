/-
  EvmAsm.Evm64.Exp.Compose.CondMulSkip

  Small EXP full-loop building blocks around the conditional-multiply skip gate.
-/

import EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Conditional-multiply BEQ skip gate lifted to the top-level EXP code bundle
    unioned with the shared `mul_callable` code.  Full-loop composition uses
    this code shape when the nonzero branch continues into the callable path. -/
theorem exp_cond_mul_beq_evm_exp_union_spec_within
    (frame : Assertion) (hframe : frame.pcFree)
    (v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base skipTarget mulTarget : Word)
    (hskip : ((base + 144) + signExtend13 skipOff : Word) = skipTarget) :
    cpsBranchWithin 1 (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))) ** frame)
      skipTarget
        (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝) ** frame)
      (base + 148)
        (((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) ** frame) := by
  have hbeq := beq_spec_within .x10 .x0 skipOff v10 (0 : Word) (base + 144)
  rw [hskip] at hbeq
  have hnext : ((base + 144 : Word) + 4) = base + 148 := by bv_omega
  rw [hnext] at hbeq
  have hframed := cpsBranchWithin_frameR frame hframe hbeq
  exact cpsBranchWithin_extend_code (h := hframed) (hmono := by
    intro a i hcode
    exact CodeReq.union_mono_left a i
      (evmExpCode_cond_mul_beq_sub
        (base := base) (mulOff := mulOff) (skipOff := skipOff)
        (backOff := backOff) a i hcode))

/-- Permuted-frame variant of `exp_cond_mul_beq_evm_exp_union_spec_within`,
    matching the frame-first shape used by the following callable composition. -/
theorem exp_cond_mul_beq_evm_exp_union_spec_within_frameL
    (frame : Assertion) (hframe : frame.pcFree)
    (v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base skipTarget mulTarget : Word)
    (hskip : ((base + 144) + signExtend13 skipOff : Word) = skipTarget) :
    cpsBranchWithin 1 (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))))
      skipTarget
        (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝))
      (base + 148)
        (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝)) := by
  have h := exp_cond_mul_beq_evm_exp_union_spec_within
    frame hframe v10 mulOff skipOff backOff base skipTarget mulTarget hskip
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    h

/-- Compose the lifted EXP conditional-multiply skip gate with an arbitrary
    false-branch continuation over the same top-level/callable code region. -/
theorem exp_cond_mul_skip_then_triple_evm_exp_union_spec_within
    {nSteps : Nat} {frame postFalse : Assertion} (hframe : frame.pcFree)
    (v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base skipTarget mulTarget exitFalse : Word)
    (hskip : ((base + 144) + signExtend13 skipOff : Word) = skipTarget)
    (hfalse :
      cpsTripleWithin nSteps (base + 148) exitFalse
        ((evmExpCode base mulOff skipOff backOff).union
          (mul_callable_code mulTarget))
        (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝))
        postFalse) :
    cpsBranchWithin (1 + nSteps) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word))))
      skipTarget
        (frame ** ((.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v10 = 0⌝))
      exitFalse postFalse := by
  have hbeq := exp_cond_mul_beq_evm_exp_union_spec_within_frameL
    frame hframe v10 mulOff skipOff backOff base skipTarget mulTarget hskip
  exact cpsBranchWithin_seq_cpsTripleWithin_same_cr hbeq hfalse (fun _ hp => hp)

/-- Existing conditional-MUL callable path framed with the false-branch facts
    produced by the preceding BEQ skip gate. -/
theorem exp_cond_mul_marshal_pair_then_mul_call_false_branch_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hmt : mulTarget = (base + 212) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let callPre :=
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
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
    let callPost :=
      ((.x2 ↦ᵣ sp) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmMulStackPost evmSp (expResultWord r0 r1 r2 r3)
                              (expResultWord a0 a1 a2 a3) **
       (.x1 ↦ᵣ (base + 216)))
    cpsTripleWithin (17 + 64) (base + 148) ((base + 216) &&& ~~~1)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      (callPre ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝))
      (callPost ** ((.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝)) := by
  intro callPre callPost
  have hcall := exp_cond_mul_marshal_pair_then_mul_call_evm_exp_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff skipOff backOff base hmt hd
  have hframed :=
    cpsTripleWithin_frameR ((.x0 ↦ᵣ (0 : Word)) ** ⌜v10 ≠ 0⌝) (by pcFree) hcall
  simpa [callPre, callPost] using hframed

end EvmAsm.Evm64.Exp.Compose
