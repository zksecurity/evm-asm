/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterPreNPost

  Adapters from fixed iteration post cases to the semantic/cursor/control
  carrying `expTwoMulFixedIterPreN` family.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariantWithControl

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem pure_assertion_eq_emp_of_true {p : Prop} (hp : p) :
    (⌜p⌝ : Assertion) = empAssertion := by
  rw [← pure_true_eq_emp]
  funext ps
  apply propext
  constructor
  · intro h
    exact ⟨h.1, trivial⟩
  · intro h
    exact ⟨h.1, hp⟩

theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPreN_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6Reg : v6 = c6 + signExtend12 (-1 : BitVec 12))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithFrame (k + 1) baseWord exponentWord
      (e <<< (1 : BitVec 6).toNat)
      v6
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (rw.getLimbN 3)
      (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro rw
  obtain ⟨_hExit, hC6, hBitNe⟩ :=
    expTwoMulFixedIterSkipCondScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = rw := by
    dsimp [rw]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_condRw_of_ne_zero
      hBitNe
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        v6 ptr nextLimb evmSp := by
    rw [hC6Reg]
    exact hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps := by
    simpa [rw] using
      (expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithFrame_unfold,
    expTwoMulFixedIterPreN_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipScratchFrame_to_iterPreN_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6Reg : v6 = c6 + signExtend12 (-1 : BitVec 12))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithFrame (k + 1) baseWord exponentWord
      (e <<< (1 : BitVec 6).toNat)
      v6
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (squareW.getLimbN 3)
      (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro squareW
  obtain ⟨_hExit, hC6, hBitZero⟩ :=
    expTwoMulFixedIterSkipScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = squareW := by
    dsimp [squareW]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_squareW_of_zero
      hBitZero
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        v6 ptr nextLimb evmSp := by
    rw [hC6Reg]
    exact hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps := by
    simpa [squareW] using
      (expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithFrame_unfold,
    expTwoMulFixedIterPreN_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPreNWithControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
      (c6 + signExtend12 (-1 : BitVec 12))
      (e <<< (1 : BitVec 6).toNat)
      v6
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (rw.getLimbN 3)
      (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro rw
  obtain ⟨_hExit, hC6, hBitNe⟩ :=
    expTwoMulFixedIterSkipCondScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = rw := by
    dsimp [rw]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_condRw_of_ne_zero
      hBitNe
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp :=
    hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps := by
    simpa [rw] using
      (expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipScratchFrame_to_iterPreNWithControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
      (c6 + signExtend12 (-1 : BitVec 12))
      (e <<< (1 : BitVec 6).toNat)
      v6
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (squareW.getLimbN 3)
      (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro squareW
  obtain ⟨_hExit, hC6, hBitZero⟩ :=
    expTwoMulFixedIterSkipScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = squareW := by
    dsimp [squareW]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_squareW_of_zero
      hBitZero
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp :=
    hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps := by
    simpa [squareW] using
      (expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

end EvmAsm.Evm64.Exp.Compose
