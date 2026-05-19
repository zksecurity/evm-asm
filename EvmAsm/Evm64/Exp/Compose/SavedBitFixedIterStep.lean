/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStep

  One physical fixed-loop iteration into the semantic step-post target.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepPost

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem cpsTripleWithin_expTwoMulFixedIterCaseExitPost_nonzero_vacuous
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    {nSteps : Nat} {entry exit : Word} {code : CodeReq} {Q : Assertion} :
    cpsTripleWithin nSteps entry exit code
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      Q := by
  intro R _hR s _hcr hExitR _hpc
  exfalso
  obtain ⟨hp, _hcompat, hExit⟩ := holdsFor_sepConj_elim_left hExitR
  exact
    expTwoMulFixedIterCaseExitPost_nonzero_count_false
      (iterCount := iterCount) (e := e) (c6 := c6) (ptr := ptr)
      (nextLimb := nextLimb) (sp := sp) (evmSp := evmSp)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
      (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
      (base := base) hne
      hExit

theorem cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
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
    cpsTripleWithin 193 (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) := by
  have hBranch :=
    exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
  have hLoop :
      cpsTripleWithin 0 (base + 44) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
    cpsTripleWithin_extend_code
      (fun _a _i h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
        (base + 44) hk hBase hCursor hControl hNextNext hInv)
  have hExit :
      cpsTripleWithin 0 (base + 296) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
    cpsTripleWithin_expTwoMulFixedIterCaseExitPost_nonzero_vacuous hne
  have hMerged :=
    cpsNBranchWithin_merge hBranch (fun exit hmem => by
      simp [expTwoMulFixedIterCaseExits] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        exact hLoop
      · cases hmem
        exact hExit)
  simpa [Nat.add_zero] using hMerged

theorem cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
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
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion)
        Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControl
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hbase hne hk hBase hCursor hControl
      hNextNext hInv)
    hStepPost

end EvmAsm.Evm64.Exp.Compose
