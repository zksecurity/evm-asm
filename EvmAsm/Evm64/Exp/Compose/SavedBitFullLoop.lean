/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop

  Full-loop code-bundle helpers for the corrected MSB-first saved-bit EXP
  layout.  These mirror the `FullLoop.lean` EXP+MUL lifts, but target
  `evmExpMsbSavedBitCode` so the single-iteration composition can keep the
  tested bit live in `x18` across the unconditional squaring call.
-/

import EvmAsm.Evm64.Exp.Compose.FullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Code required by the corrected saved-bit EXP program plus the external
    `mul_callable` body reached by the squaring and conditional-multiply JALs. -/
abbrev evmExpMsbSavedBitWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitCode base mulOff skipOff backOff).union
    (mul_callable_code mulTarget)

/-- Corrected saved-bit EXP program with independent JAL offsets for the
    squaring and conditional-multiply call sites, plus the external
    `mul_callable` body both sites target. -/
abbrev evmExpMsbSavedBitTwoMulWithMulCode (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpMsbSavedBitTwoMulCode
    base squaringMulOff condMulOff skipOff backOff).union
    (mul_callable_code mulTarget)

theorem evmExpMsbSavedBitWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        a = some i := by
  unfold evmExpMsbSavedBitWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulWithMulCode_exp_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i,
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
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

theorem evmExpMsbSavedBitTwoMulWithMulCode_mul_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulWithMulCode
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

/-- Lift a two-offset corrected saved-bit EXP spec into the combined EXP+MUL
    code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulWithMulCode_exp_sub) h

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

/-- Prefix of one corrected EXP iteration: extract the current MSB into `x10`
    and save the same bit in callee-saved `x18` before the squaring call. -/
theorem exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 : Word) (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let bit := e >>> (63 : BitVec 6).toNat
    cpsTripleWithin (3 + 1) (base + 28) (base + 44)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18))
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))) **
       (.x10 ↦ᵣ bit) **
       (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))) := by
  intro bit
  have hBit := exp_msb_bit_test_evm_exp_msb_saved_bit_with_mul_spec_within
    e c v10 mulOff skipOff backOff base mulTarget
  have hBitFramed :=
    cpsTripleWithin_frameR (.x18 ↦ᵣ v18) (by pcFree) hBit
  have hSave := exp_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    bit v18 mulOff skipOff backOff base mulTarget
  have hSaveFramed :=
    cpsTripleWithin_frameL
      ((.x5 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
       (.x6 ↦ᵣ (c + signExtend12 ((-1) : BitVec 12))))
      (by pcFree) hSave
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hBitFramed hSaveFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

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

/-- Squaring-side call-block lifted to the two-MUL-offset saved-bit EXP+MUL
    code bundle.  This uses the squaring JAL offset only; the conditional
    multiply offset is independent. -/
theorem exp_squaring_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let w := expResultWord r0 r1 r2 r3
    cpsTripleWithin (17 + 64 + 9) (base + 44) ((base + 44) + 104)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
  have hSquareSub : ∀ a i,
      exp_squaring_call_block_code (base + 44) squaringMulOff a = some i →
      evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff a = some i := by
    intro a i h
    have hiter : (base + 44 : Word) = (base + 28) + 16 := by bv_omega
    rw [hiter] at h
    exact evmExpMsbSavedBitTwoMulCode_iter_body_sub
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
      a i (expIterBodyFullMsbSavedBitTwoMulCode_squaring_sub a i h)
  have hd_inner : CodeReq.Disjoint
      (exp_squaring_call_block_code (base + 44) squaringMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_squaring_call_block_code (base + 44) squaringMulOff a with
      | none => rfl
      | some i =>
        have hev := hSquareSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_squaring_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget squaringMulOff (base + 44)
    hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (hSquareSub a i h))
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd a i h))
    hbase_spec

/-- Prefix plus squaring side of one corrected EXP iteration.  This carries
    the saved bit in `x18` across the full `mul_callable` round-trip, landing
    at the saved-bit conditional-multiply BEQ site. -/
theorem exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) (base + 148)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld))
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (w * w).getLimbN 3) **
       evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit w
  have hPrefix := exp_msb_bit_test_then_save_bit_evm_exp_msb_saved_bit_with_mul_spec_within
    e c v10 v18 mulOff skipOff backOff base mulTarget
  have hPrefixFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)
      ) (by pcFree) hPrefix
  have hSquare := exp_squaring_call_block_evm_exp_msb_saved_bit_with_mul_spec_within
    sp evmSp (e <<< (1 : BitVec 6).toNat) vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    (c + signExtend12 ((-1) : BitVec 12)) v7 bit v11 mulTarget
    mulOff skipOff backOff base hbase hmt hd
  have hSquareFramed :=
    cpsTripleWithin_frameL (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12)))
      (by pcFree) hSquare
  have hSeq :
      cpsTripleWithin (3 + 1 + (17 + 64 + 9)) (base + 28) ((base + 44) + 104)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ _ :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp only [bit] at hp ⊢
        xperm_hyp hp)
      hPrefixFramed hSquareFramed
  have hexit : ((base + 44 : Word) + 104) = base + 148 := by bv_omega
  rw [hexit] at hSeq
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Prefix plus squaring side followed by the saved-bit BEQ.  This is the
    branch handoff immediately before the optional conditional multiply. -/
theorem exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) (base target : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (htarget : (base + 148 : Word) + signExtend13 skipOff = target) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68)))
      (base + 152)
        ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
         (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
         (.x5 ↦ᵣ (w * w).getLimbN 3) **
         evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
         regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
         memOwn evmSp ** memOwn (evmSp + 8) **
         memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
         (.x1 ↦ᵣ ((base + 44) + 68))) := by
  intro bit w
  let rest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ (w * w).getLimbN 3) **
    evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ ((base + 44) + 68))
  have hPrefixSquare :=
    exp_msb_saved_bit_prefix_then_squaring_call_evm_exp_msb_saved_bit_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget mulOff skipOff backOff base hbase hmt hd
  have hPrefixSquareFramed :=
    cpsTripleWithin_frameR (.x0 ↦ᵣ (0 : Word)) (by pcFree) hPrefixSquare
  have hBeq := exp_cond_mul_saved_bit_beq_evm_exp_msb_saved_bit_with_mul_spec_within
    mulOff skipOff backOff (bit + signExtend12 (0 : BitVec 12))
    base mulTarget target htarget
  have hBeqFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hBeq
  have hSeq :
      cpsBranchWithin (3 + 1 + (17 + 64 + 9) + 1) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ target _ (base + 152) _ :=
    cpsTripleWithin_seq_cpsBranchWithin_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit] at hp ⊢
        xperm_hyp hp)
      hPrefixSquareFramed hBeqFramed
  exact cpsBranchWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [rest] at hp ⊢
      xperm_hyp hp)
    hSeq

/-- Zero-bit path through the saved-bit BEQ, followed by the loop-back
    counter update.  The nonzero conditional-multiply path is left as the
    first exit for the next composition slice. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    let iterCountNew := iterCount + signExtend12 ((-1 : BitVec 12))
    let rest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ (w * w).getLimbN 3) **
      evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
       (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
       (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
      [((base + 152),
          ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ (w * w).getLimbN 3) **
           evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)),
        (loopTarget,
          (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew ≠ 0⌝) ** rest)),
        (base + 264,
          (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew = 0⌝) ** rest))] := by
  intro bit w iterCountNew rest
  have hBranch :=
    exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget mulOff skipOff backOff base (base + 256)
      hbase hmt hd hskip
  have hBranchFramed :=
    cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
    iterCount mulOff skipOff backOff base mulTarget loopTarget hback
  have hLoopFramed := cpsBranchWithin_frameR rest (by
    dsimp [rest]
    pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        dsimp [rest, bit] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  have hSeqPre :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
        ((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
         (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
         (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
         (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount))
        _ :=
    cpsNBranchWithin_weaken_pre
      (fun _ hp => by xperm_hyp hp) hSeq
  exact hSeqPre

/-- Frame-preserving variant of the zero-bit skip path that carries the saved
    base operand window needed by the conditional-multiply handoff. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 mulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitCode base mulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    let iterCountNew := iterCount + signExtend12 ((-1 : BitVec 12))
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let rest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ (w * w).getLimbN 3) **
      evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitWithMulCode base mulTarget mulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) ** (.x18 ↦ᵣ v18) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame)
      [((base + 152),
          (((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ (w * w).getLimbN 3) **
           evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)) ** baseFrame),
        (loopTarget,
          ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew ≠ 0⌝) ** rest) ** baseFrame)),
        (base + 264,
          ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜iterCountNew = 0⌝) ** rest) ** baseFrame))] := by
  intro bit w iterCountNew baseFrame rest
  have h :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget mulOff skipOff backOff base loopTarget
      hbase hmt hd hskip hback
  have hBaseFramePcFree : baseFrame.pcFree := by
    dsimp only [baseFrame]
    exact pcFree_sepConj pcFree_memIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_memIs pcFree_memIs))
  have hf := cpsNBranchWithin_frameR hBaseFramePcFree h
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by xperm_hyp hp) hf

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

/-- Conditional-multiply taken call-block lifted to the two-MUL-offset
    saved-bit EXP+MUL code bundle.  This uses the conditional-multiply JAL
    offset only; the squaring offset is independent. -/
theorem exp_cond_mul_call_block_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
      v6 v7 v10 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget)) :
    let r := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    cpsTripleWithin (17 + 64 + 9) (base + 152) ((base + 152) + 104)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
      exp_cond_mul_call_block_code (base + 152) condMulOff a = some i →
      evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff a = some i := by
    intro a i h
    have hskip : (base + 152 : Word) = (base + 28) + 120 + 4 := by bv_omega
    rw [hskip] at h
    exact evmExpMsbSavedBitTwoMulCode_iter_body_sub
      (base := base) (squaringMulOff := squaringMulOff)
      (condMulOff := condMulOff) (skipOff := skipOff) (backOff := backOff)
      a i (expIterBodyFullMsbSavedBitTwoMulCode_cond_mul_sub a i
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_call_sub
          ((base + 28) + 120) condMulOff skipOff a i h))
  have hd_inner : CodeReq.Disjoint
      (exp_cond_mul_call_block_code (base + 152) condMulOff)
      (mul_callable_code mulTarget) := by
    intro a
    rcases hd a with hExp | hMul
    · left
      cases hsub : exp_cond_mul_call_block_code (base + 152) condMulOff a with
      | none => rfl
      | some i =>
        have hev := hCondSub a i hsub
        exact absurd (hev.symm.trans hExp) (by simp)
    · right; exact hMul
  have hbase_spec := EvmAsm.Evm64.exp_cond_mul_call_block_spec_within
    sp evmSp tOld vOld r0 r1 r2 r3 a0 a1 a2 a3 d0 d1 d2 d3 e0 e1 e2 e3
    v6 v7 v10 v11 mulTarget condMulOff (base + 152) hbase' hmt hd_inner
  exact cpsTripleWithin_extend_code
    (hmono := CodeReq.union_sub
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
        (hCondSub a i h))
      (fun a i h => evmExpMsbSavedBitTwoMulWithMulCode_mul_sub hd a i h))
    hbase_spec

end EvmAsm.Evm64.Exp.Compose
