/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop

  Full-loop code-bundle helpers for the corrected MSB-first saved-bit EXP
  layout.  These mirror the `FullLoop.lean` EXP+MUL lifts, but target
  `evmExpMsbSavedBitCode` so the single-iteration composition can keep the
  tested bit live in `x18` across the unconditional squaring call.
-/

import EvmAsm.Evm64.Exp.Compose.FullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Code required by the corrected saved-bit EXP program plus the external
    `mul_callable` body reached by the squaring and conditional-multiply JALs. -/
abbrev evmExpMsbSavedBitWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitCode base mulOff skipOff backOff).union
    (mul_callable_code mulTarget)

theorem evmExpMsbSavedBitWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitWithMulCode_mul_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Lift a corrected saved-bit top-level EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- Lift a corrected saved-bit top-level EXP branch spec into the combined
    EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode {nSteps : Nat}
    {entry base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word}
    {Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitCode base mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitWithMulCode_exp_sub) h

/-- MSB bit-test block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 3 (base + 28) (base + 40)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ (e >>> (63 : BitVec 6).toNat))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_msb_bit_test_evm_exp_msb_saved_bit_spec_within
      e c v10 mulOff skipOff backOff base)

/-- Save-bit block lifted to the corrected saved-bit EXP+MUL code bundle. -/
theorem exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (bit v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 40) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ v18))
      ((.x10 ↦ᵣ bit) ** (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_save_bit_evm_exp_msb_saved_bit_spec_within
      bit v18 mulOff skipOff backOff base)

/-- Saved-bit conditional-multiply BEQ skip-gate lifted to the corrected
    saved-bit EXP+MUL code bundle. -/
theorem exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (v18 : Word) (base mulTarget target : Word)
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    cpsBranchWithin 1 (base + 148)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 = 0⌝)
      (base + 152) ((.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜v18 ≠ 0⌝) :=
  cpsBranchWithin_extend_evmExpMsbSavedBitWithMulCode
    (exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_spec_within
      mulOff skipOff backOff v18 base target htarget)

/-- Saved-bit loop-back block lifted directly to the corrected EXP+MUL code
    bundle. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within (c : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 256) + 4 : Word) + signExtend13 backOff = target) :
    let cNew := c + signExtend12 ((-1 : BitVec 12))
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew ≠ 0⌝)
      (base + 264) ((.x9 ↦ᵣ cNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜cNew = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 256)
    target htarget
  have hnext : ((base + 256 : Word) + 8) = base + 264 := by bv_omega
  rw [hnext] at h
  exact cpsBranchWithin_extend_code (h := h)
    (hmono := fun a i hi =>
      evmExpMsbSavedBitWithMulCode_exp_sub a i
        (evmExpMsbSavedBitCode_iter_loop_back_sub a i hi))

/-- Squaring-side full call-block lifted to the corrected saved-bit EXP+MUL
    code bundle.  The block starts after the saved-bit instruction, at
    `base + 44`, and exits at the saved-bit BEQ site `base + 148`. -/
theorem exp_squaring_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let w := expResultWord r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 44) ((base + 44) + 104)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
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
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (.x1 ↦ᵣ vOld))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (w * w).getLimbN 3) **
       evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro w
  have hbase' : (base + 44 : Word) &&& 1 = 0 := by bv_decide
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 44) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 44) mulOff a with
      | none => rfl
      | some i =>
        have hev := evmExpMsbSavedBitCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 44) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitWithMulCode_exp_sub a i
        (evmExpMsbSavedBitCode_iter_squaring_sub
          (base := base) (mulOff := mulOff)
          (skipOff := skipOff) (backOff := backOff) a i h))
      (fun a i h => evmExpMsbSavedBitWithMulCode_mul_sub hd a i h))
    hbase_spec

/-- Conditional-multiply taken call-block lifted to the corrected saved-bit
    EXP+MUL code bundle.  The leading BEQ is handled separately; this theorem
    starts at the taken block `base + 152` and exits at `base + 256`. -/
theorem exp_cond_mul_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 152) ((base + 152) + 104)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
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
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (r * aw).getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp (r * aw) ** evmWordIs (evmSp + 32) (r * aw) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  intro r aw
  have hbase' : (base + 152 : Word) &&& 1 = 0 := by bv_decide
  have hCondSub : ∀ a i,
      exp_cond_mul_call_block_code (base + 152) mulOff a = some i →
      evmExpMsbSavedBitCode base mulOff skipOff backOff a = some i := by
    intro a i h
    have hskip : (base + 152 : Word) = base + 148 + 4 := by bv_omega
    rw [hskip] at h
    exact evmExpMsbSavedBitCode_iter_cond_mul_sub a i
      (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
        (base + 148) mulOff skipOff a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 152) mulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 152) mulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget mulOff (base + 152) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitWithMulCode_exp_sub a i (hCondSub a i h))
      (fun a i h => evmExpMsbSavedBitWithMulCode_mul_sub hd a i h))
    hbase_spec

end EvmAsm.Evm64.Exp.Compose
