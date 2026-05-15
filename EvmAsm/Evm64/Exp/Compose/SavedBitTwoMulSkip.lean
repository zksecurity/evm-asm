/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkip

  Two-MUL-offset saved-bit EXP skip-path composition.  This is split out of
  `SavedBitFullLoop.lean` to keep the compose files under the size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Bundles `expTwoMulSkipLoopRest` with the `bit` and `squareW` computations
    so the skip specs need only two statement lets instead of three. -/
@[irreducible]
def expTwoMulSkipIterRest
    (e sp evmSp base r0 r1 r2 r3 : Word) : Assertion :=
  expTwoMulSkipLoopRest
    (expTwoMulIterBit e) sp evmSp base (expTwoMulSquareW r0 r1 r2 r3)

theorem expTwoMulSkipIterRest_unfold
    {e sp evmSp base r0 r1 r2 r3 : Word} :
    expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3 =
      expTwoMulSkipLoopRest
        (expTwoMulIterBit e) sp evmSp base (expTwoMulSquareW r0 r1 r2 r3) := by
  delta expTwoMulSkipIterRest; rfl

/-- Saved-bit loop-back block lifted to the two-MUL-offset EXP+MUL code
    bundle. -/
theorem exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (c : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget target : Word)
    (htarget : ((base + 256) + 4 : Word) + signExtend13 backOff = target) :
    cpsBranchWithin 2 (base + 256)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x9 ↦ᵣ c) ** (.x0 ↦ᵣ (0 : Word)))
      target
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c ≠ 0⌝)
      (base + 264)
        ((.x9 ↦ᵣ expTwoMulIterCountNew c) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew c = 0⌝) := by
  have h := EvmAsm.Evm64.exp_loop_back_spec_within c backOff (base + 256)
    target htarget
  have hnext : ((base + 256 : Word) + 8) = base + 264 := by bv_omega
  rw [hnext] at h
  simpa [expTwoMulIterCountNew] using
    (cpsBranchWithin_extend_code (h := h)
      (hmono := fun a i hi =>
        evmExpMsbSavedBitTwoMulWithMulCode_exp_sub a i
          (evmExpMsbSavedBitTwoMulCode_iter_loop_back_sub a i hi)))

/-- Zero-bit path through the two-MUL-offset saved-bit BEQ, followed by the
    loop-back counter update.  The nonzero conditional-multiply path is left
    as the first exit for the next composition slice. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)),
        (loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3)),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) **
            expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3))] := by
  intro bit squareW
  have hBranch :=
    exp_msb_saved_bit_prefix_squaring_then_beq_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      v7 v11 mulTarget squaringMulOff condMulOff skipOff backOff base
      (base + 256) hbase hmt hd hskip
  have hBranchFramed :=
    cpsBranchWithin_frameR (.x9 ↦ᵣ iterCount) (by pcFree) hBranch
  have hBranchSwapped := cpsBranchWithin_swap hBranchFramed
  have hLoop := exp_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    iterCount squaringMulOff condMulOff skipOff backOff base mulTarget
    loopTarget hback
  have hLoopFramed := cpsBranchWithin_frameR
    (expTwoMulSkipIterRest e sp evmSp base r0 r1 r2 r3) (by
      rw [expTwoMulSkipIterRest_unfold]
      exact expTwoMulSkipLoopRest_pcFree) hLoop
  have hLoopN := cpsBranchWithin_as_cpsNBranchWithin hLoopFramed
  have hSeq :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        _ _ :=
    cpsBranchWithin_cons_cpsNBranchWithin_with_perm_same_cr
      (fun _ hp => by
        simp [expTwoMulSkipIterRest_unfold, expTwoMulSkipLoopRest_unfold] at hp ⊢
        xperm_hyp hp)
      hBranchSwapped hLoopN
  have hSeqPre :
      cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
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

/-- Frame-preserving two-MUL-offset variant of the zero-bit skip path that
    carries the saved base operand window needed by the conditional-multiply
    handoff. -/
theorem exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let rest : Assertion :=
      expTwoMulSkipLoopRest bit sp evmSp base squareW
    cpsNBranchWithin ((3 + 1 + (17 + 64 + 9) + 1) + 2) (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
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
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)) ** baseFrame),
        (loopTarget,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** rest) ** baseFrame)),
        (base + 264,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** rest) ** baseFrame))] := by
  intro bit squareW baseFrame rest
  have h :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 v7 v11 mulTarget squaringMulOff condMulOff skipOff
      backOff base loopTarget hbase hmt hd hskip hback
  have hBaseFramePcFree : baseFrame.pcFree := by
    dsimp only [baseFrame]
    exact pcFree_sepConj pcFree_memIs
      (pcFree_sepConj pcFree_memIs
        (pcFree_sepConj pcFree_memIs pcFree_memIs))
  have hf := cpsNBranchWithin_frameR hBaseFramePcFree h
  simpa [rest, expTwoMulSkipLoopRest_unfold, expTwoMulSkipIterRest_unfold] using
    (cpsNBranchWithin_weaken_pre
      (fun _ hp => by simpa using hp) hf)

end EvmAsm.Evm64.Exp.Compose
