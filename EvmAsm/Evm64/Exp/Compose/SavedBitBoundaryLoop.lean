/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop

  Generic composition scaffold for the two-MUL saved-bit EXP boundary:
  prologue/pointer-advance, an externally supplied loop proof, and
  pointer-restore/epilogue.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Compose the named prologue boundary, any loop proof over the named
    loop-entry/loop-exit surface, and the named epilogue boundary. The future
    256-iteration proof can instantiate `hLoop`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_spec_within
    {nSteps : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin (expTwoMulBoundaryLoopBound nSteps) base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  have hBoundary :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base
  have hPrefix :=
    cpsTripleWithin_seq_same_cr hBoundary hLoop
  exact
    cpsTripleWithin_seq_same_cr hPrefix
      (exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_spec_within
        sp evmSp iterCountNew tOld r0 r1 r2 r3 baseWord rest exitCond base)

/-- Bounded variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_spec_within`. This packages
    the prologue/loop/epilogue boundary into a caller-chosen closed-form bound
    for the later full-loop theorem. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : expTwoMulBoundaryLoopBound nSteps ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_boundary_loop_epilogue_of_loop_spec_within
        sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
        r0 r1 r2 r3 baseWord exponentWord rest exitCond base hLoop)

/-- Closed-form bound variant of
    `exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within`, using
    the normalized boundary cost `nSteps + 17`. -/
theorem exp_two_mul_boundary_loop_epilogue_of_loop_closed_bound_spec_within
    {nSteps nBound : Nat}
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBound : nSteps + 17 ≤ nBound)
    (hLoop :
      cpsTripleWithin nSteps (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin nBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by simpa [expTwoMulBoundaryLoopBound_eq] using hBound)
      hLoop

/-- Specialization of the named boundary composition to the 256-iteration
    saved-bit two-MUL loop body bound. This is the outer shell expected by the
    eventual full-loop proof once the loop proof itself is available. -/
theorem exp_two_mul_full_loop_boundary_of_body_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hLoop :
      cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest)
        (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
          baseWord rest exitCond)) :
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_boundary_loop_epilogue_of_loop_bounded_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 baseWord exponentWord rest exitCond base
      (by rfl)
      hLoop

end EvmAsm.Evm64.Exp.Compose
