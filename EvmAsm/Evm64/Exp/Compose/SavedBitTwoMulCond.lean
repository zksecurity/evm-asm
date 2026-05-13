/-
  EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond

  Two-MUL-offset saved-bit EXP conditional-multiply path composition.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCondCall

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- One two-MUL-offset saved-bit EXP iteration with both conditional-multiply
    outcomes and both zero-bit skip outcomes exposed as separate exits. This
    composes the skip/loop-back path with the folded-word conditional-multiply
    path at the nonzero saved-bit head exit; a later slice can merge the equal
    loop/exit PCs under disjunctive postconditions. -/
theorem exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let skipRest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    let condRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let condFrame : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
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
      [(loopTarget,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
        (base + 264,
          (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame),
        (loopTarget,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame)),
        (base + 264,
          ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
           ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame))] := by
  intro bit squareW rw baseFrame skipRest condRest condFrame
  have hSkip :=
    exp_msb_saved_bit_prefix_squaring_beq_skip_then_loop_back_with_base_frame_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hd hskip hback
  have hCond :=
    exp_cond_mul_call_then_loop_back_evm_exp_msb_saved_bit_two_mul_with_mul_folded_owned_spec_within
      iterCount sp evmSp ((base + 44) + 68) a0 a1 a2 a3 mulTarget squareW
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hcondmt hd hback
  have hCondFramed := cpsNBranchWithin_frameR (F := condFrame) (by
    dsimp [condFrame]
    pcFree) hCond
  have hCondHead :
      cpsNBranchWithin ((17 + 64 + 9) + 2) (base + 152)
        (evmExpMsbSavedBitTwoMulWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        ((((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
           (.x0 ↦ᵣ (0 : Word)) ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
           (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
           (.x5 ↦ᵣ squareW.getLimbN 3) **
           evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
           regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
           memOwn evmSp ** memOwn (evmSp + 8) **
           memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
           (.x1 ↦ᵣ ((base + 44) + 68))) ** (.x9 ↦ᵣ iterCount)) ** baseFrame)
        [(loopTarget,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame),
          (base + 264,
            (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
             ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame)] := by
    exact cpsNBranchWithin_weaken_pre
      (fun _ hp => by
        dsimp [condRest, condFrame, baseFrame] at hp ⊢
        xperm_hyp hp) hCondFramed
  have hFull :=
    cpsNBranchWithin_extend_head_nbranch hSkip hCondHead
  exact hFull

/-- Two-exit view of
    `exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within`, merging the
    conditional-multiply and zero-bit skip outcomes that land at the same
    loop/exit PCs. The postconditions are intentionally assertion-level
    disjunctions; later semantic slices can consume either side separately. -/
theorem exp_msb_saved_bit_two_mul_full_iter_merged_exit_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let skipRest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    let condRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let condFrame : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let condLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame
    let condExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame
    let skipLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
    let skipExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
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
      [(loopTarget, fun h => condLoop h ∨ skipLoop h),
        (base + 264, fun h => condExit h ∨ skipExit h)] := by
  intro bit squareW rw baseFrame skipRest condRest condFrame
    condLoop condExit skipLoop skipExit
  have hFour :=
    exp_msb_saved_bit_two_mul_full_iter_four_exit_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback
  refine cpsNBranchWithin_weaken_posts hFour ?_
  intro ex hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · subst ex
    refine ⟨(loopTarget, fun h => condLoop h ∨ skipLoop h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      simpa [condLoop, condRest, condFrame] using hp
  · subst ex
    refine ⟨(base + 264, fun h => condExit h ∨ skipExit h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      left
      simpa [condExit, condRest, condFrame] using hp
  · subst ex
    refine ⟨(loopTarget, fun h => condLoop h ∨ skipLoop h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      simpa [skipLoop, skipRest, baseFrame] using hp
  · subst ex
    refine ⟨(base + 264, fun h => condExit h ∨ skipExit h), ?_, rfl, ?_⟩
    · simp
    · intro h hp
      right
      simpa [skipExit, skipRest, baseFrame] using hp

/-- Branch-shaped view of the merged two-MUL saved-bit one-iteration theorem.
    This is just `cpsNBranchWithin_as_cpsBranchWithin` applied to the merged
    two-exit N-branch, keeping downstream composition code on the ordinary
    branch interface. -/
theorem exp_msb_saved_bit_two_mul_full_iter_branch_spec_within
    (e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let skipRest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    let condRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let condFrame : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let condLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame
    let condExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame
    let skipLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
    let skipExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
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
      loopTarget (fun h => condLoop h ∨ skipLoop h)
      (base + 264) (fun h => condExit h ∨ skipExit h) := by
  intro bit squareW rw baseFrame skipRest condRest condFrame
    condLoop condExit skipLoop skipExit
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_saved_bit_two_mul_full_iter_merged_exit_spec_within
      e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

/-- Owned-scratch variant of the two-MUL saved-bit one-iteration branch.
    This keeps the branch exits unchanged while exposing `x6`, `x7`, `x10`,
    and `x11` as owned caller scratch in the precondition, matching the
    boundary-frame shape produced by the prologue/pointer sequence. -/
theorem exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let skipRest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    let condRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let condFrame : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let condLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame
    let condExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame
    let skipLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
    let skipExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
    cpsNBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame)
      [(loopTarget, fun h => condLoop h ∨ skipLoop h),
       (base + 264, fun h => condExit h ∨ skipExit h)] := by
  intro bit squareW rw baseFrame skipRest condRest condFrame
    condLoop condExit skipLoop skipExit
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x6)
    (P :=
      (((.x5 ↦ᵣ e) ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp) ?_
  intro c
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x10)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp) ?_
  intro v10
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x7)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
        regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp) ?_
  intro v7
  refine cpsNBranchWithin_of_forall_regIs_to_regOwn_perm
    (r := .x11)
    (P :=
      (((.x5 ↦ᵣ e) ** (.x6 ↦ᵣ c) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
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
        (.x7 ↦ᵣ v7) ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame))
    (hpre := fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp) ?_
  intro v11
  exact cpsNBranchWithin_weaken_pre
    (fun _ hp => by
      dsimp [baseFrame] at hp ⊢
      xperm_hyp hp)
    (cpsBranchWithin_as_cpsNBranchWithin
      (exp_msb_saved_bit_two_mul_full_iter_branch_spec_within
        e c iterCount v10 v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 mulTarget
        squaringMulOff condMulOff skipOff backOff base loopTarget
        hbase hsqmt hcondmt hd hskip hback))

/-- Branch-interface view of
    `exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within`.
    This keeps downstream full-loop composition on the ordinary two-exit
    `cpsBranchWithin` API after the scratch-register ownership lift. -/
theorem exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := expTwoMulIterBit e
    let squareW := expTwoMulSquareW r0 r1 r2 r3
    let rw := expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let skipRest : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 44) + 68))
    let condRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ ((base + 152) + 68))
    let condFrame : Assertion :=
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let condLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** condRest) ** condFrame
    let condExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** condRest) ** condFrame
    let skipLoop : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame
    let skipExit : Assertion :=
      (((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
       ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
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
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) ** baseFrame)
      loopTarget (fun h => condLoop h ∨ skipLoop h)
      (base + 264) (fun h => condExit h ∨ skipExit h) := by
  intro bit squareW rw baseFrame skipRest condRest condFrame
    condLoop condExit skipLoop skipExit
  exact cpsNBranchWithin_as_cpsBranchWithin
    (exp_msb_saved_bit_two_mul_full_iter_branch_owned_scratch_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

end EvmAsm.Evm64.Exp.Compose
