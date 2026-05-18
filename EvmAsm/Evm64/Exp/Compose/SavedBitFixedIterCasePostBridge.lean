/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge

  Bridges between the historical fixed merged postconditions and the named
  case-post presentation used by fixed loop-back bridge proofs.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePosts
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base =
    expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base := by
  rfl

theorem expTwoMulFixedIterMergedExitPost_eq_caseExitPost
    {e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} :
    expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base =
    expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base := by
  rfl

/-- Branch view of one fixed x19 merged iteration, stated directly with the
    named case-post loop and exit assertions. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost,
    ← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
  exact
    exp_msb_bit_test_fixed_full_iter_merged_named_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase

/-- Closed-form bound variant of the fixed x19 case-post branch spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsBranchWithin
      193
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  rw [← expTwoMulFixedReloadIterStepBound_eq]
  exact
    exp_msb_bit_test_fixed_full_iter_case_posts_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase

/-- Bounded variant of the fixed x19 case-post branch spec. -/
theorem exp_msb_bit_test_fixed_full_iter_case_posts_branch_bounded_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    {nBound : Nat} (hBound : 193 ≤ nBound) :
    cpsBranchWithin
      nBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) :=
  cpsBranchWithin_mono_nSteps hBound
    (exp_msb_bit_test_fixed_full_iter_case_posts_branch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)

/-- Fixed merged-loop induction step using the named case-post loop and exit
    assertions. -/
theorem exp_fixed_loop_body_succ_step_case_posts
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  exact
    exp_fixed_loop_body_succ_step n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase
      (fun ps h => hExit ps (by
        rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
        exact h))
      hLoop

/-- Non-final fixed loop-body succ step using named case-post assertions. -/
theorem exp_fixed_loop_body_nonfinal_succ_step_case_posts
    (n : Nat)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hLoop :
      cpsTripleWithin (n * 193) (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        R) :
    cpsTripleWithin ((n + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  rw [← expTwoMulFixedIterMergedLoopPost_eq_caseLoopPost] at hLoop
  exact
    exp_fixed_loop_body_nonfinal_succ_step n
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hne hLoop

/-- Final fixed loop-body succ step using named case-post assertions. -/
theorem exp_fixed_loop_body_final_succ_step_case_posts
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word) (R : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hzero : expTwoMulIterCountNew iterCount = 0)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        R ps) :
    cpsTripleWithin ((0 + 1) * 193) (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      R := by
  exact
    exp_fixed_loop_body_final_succ_step
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base R hbase hzero
      (fun ps h => hExit ps (by
        rw [← expTwoMulFixedIterMergedExitPost_eq_caseExitPost]
        exact h))

end EvmAsm.Evm64.Exp.Compose
