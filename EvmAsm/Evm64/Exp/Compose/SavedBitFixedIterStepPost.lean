/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepPost

  Named post target for one semantic fixed-loop induction step.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterPreNPost

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedIterStepPostNWithControlFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (frame : Assertion) : Assertion :=
  fun ps =>
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (outW.getLimbN 3)
        (expTwoMulFixedBranchReturnPc bit base)
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        d0 d1 d2 d3
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps)

theorem expTwoMulFixedIterStepPostNWithControlFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame =
    (fun ps =>
      (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
        let outW := expTwoMulFixedBranchResult bit
          a0 a1 a2 a3 r0 r1 r2 r3
        expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
          (c6 + signExtend12 (-1 : BitVec 12))
          (e <<< (1 : BitVec 6).toNat)
          v6
          (expTwoMulIterCountNew iterCount)
          v10
          ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
          ptr nextLimb sp evmSp
          (outW.getLimbN 3)
          (expTwoMulFixedBranchReturnPc bit base)
          (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
          (outW.getLimbN 3)
          d0 d1 d2 d3
          (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
          (outW.getLimbN 3)
          a0 a1 a2 a3 v7 v11
          frame ps) ∨
      (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
        expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
          baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
          v6 v7 v10 v11 d0 d1 d2 d3 frame ps)) := by
  delta expTwoMulFixedIterStepPostNWithControlFrame
  rfl

theorem expTwoMulFixedIterStepPostNWithControlFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} [Assertion.PCFree frame] :
    (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame).pcFree := by
  intro ps hps
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold] at hps
  rcases hps with hPre | hReload
  · rcases hPre with ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    exact
      (inferInstance :
        Assertion.PCFree
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
            (c6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6
            (expTwoMulIterCountNew iterCount)
            v10
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0 d1 d2 d3
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7 v11
            frame)).proof ps hPre
  · rcases hReload with ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hReload⟩
    cases bit
    · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at hReload
      have hPc :
          (let squareW := expSquaringCallSquareW r0 r1 r2 r3
          (((((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
            r0 r1 r2 r3
            (expTwoMulIterCountNew iterCount ≠ 0) **
            expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
            expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
              e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
            expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
              (squareW.getLimbN 0) (squareW.getLimbN 1)
              (squareW.getLimbN 2) (squareW.getLimbN 3)) **
            expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
            expTwoMulFixedControlAssertion exponentWord (k + 1)
              64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
            frame)).pcFree := by
        dsimp
        pcFree
      exact hPc ps hReload
    · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at hReload
      have hPc :
          (let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3
          (((((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            (expTwoMulIterCountNew iterCount ≠ 0) **
            expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
            expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
              e c6 ptr nextLimb base) **
            expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
              (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
              (rw.getLimbN 3)) **
            expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
            expTwoMulFixedControlAssertion exponentWord (k + 1)
              64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
            frame)).pcFree := by
        dsimp
        pcFree
      exact hPc ps hReload

instance pcFreeInst_expTwoMulFixedIterStepPostNWithControlFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (frame : Assertion) [Assertion.PCFree frame] :
    Assertion.PCFree
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  ⟨expTwoMulFixedIterStepPostNWithControlFrame_pcFree⟩

theorem expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold]
  exact
    expTwoMulFixedIterCaseLoopPost_branchPreNWithControl_or_branchReloadWithControlFrame
      hk hBase hCursor hControl hNextNext hInv h

theorem expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion ps := by
  apply
    expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
      (frame := empAssertion) hk hBase hCursor hControl hNextNext hInv
  simpa [sepConj_emp_right'] using h

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
    (addr : Word)
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    cpsTripleWithin 0 addr addr CodeReq.empty
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
  cpsTripleWithin_refl
    (fun _hp h =>
      expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
        hk hBase hCursor hControl hNextNext hInv h)

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
    (addr : Word)
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (frame : Assertion)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    cpsTripleWithin 0 addr addr CodeReq.empty
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_refl
    (fun _hp h =>
      expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        hk hBase hCursor hControl hNextNext hInv h)

end EvmAsm.Evm64.Exp.Compose
