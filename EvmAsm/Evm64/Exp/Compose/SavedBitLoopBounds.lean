/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

  Named step-count expressions for the two-MUL saved-bit EXP loop
  composition helpers.
-/

import EvmAsm.Evm64.Exp.Compose.Base

namespace EvmAsm.Evm64.Exp.Compose

/-- Instruction bound for one named saved-bit two-MUL iteration, excluding
    externally supplied loop-back and loop-exit continuations. -/
abbrev expTwoMulNamedIterStepBound : Nat :=
  (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))

/-- Bound for the prologue/pointer-advance boundary before the saved-bit
    two-MUL loop. -/
abbrev expTwoMulBoundaryPrefixBound : Nat := 6 + 1

/-- Bound for the pointer-restore/epilogue boundary after the saved-bit
    two-MUL loop exits. -/
abbrev expTwoMulBoundarySuffixBound : Nat := 1 + 9

/-- Bound for the named saved-bit two-MUL boundary composition around a loop
    proof with `nSteps`. -/
abbrev expTwoMulBoundaryLoopBound (nSteps : Nat) : Nat :=
  (expTwoMulBoundaryPrefixBound + nSteps) + expTwoMulBoundarySuffixBound

/-- Bound for `iterations` saved-bit two-MUL loop iterations. -/
abbrev expTwoMulIterationsBodyBound (iterations : Nat) : Nat :=
  iterations * expTwoMulNamedIterStepBound

/-- Aggregate bound for 256 saved-bit two-MUL loop iterations, excluding the
    prologue/pointer-advance and pointer-restore/epilogue boundary. -/
abbrev expTwoMulFullLoopBodyBound : Nat :=
  expTwoMulIterationsBodyBound 256

/-- Remaining body bound after peeling one iteration from the 256-iteration
    saved-bit two-MUL loop. -/
abbrev expTwoMulFullLoopBodyTailBound : Nat :=
  expTwoMulIterationsBodyBound 255

/-- Aggregate bound for the full saved-bit two-MUL loop including the
    prologue/pointer-advance and pointer-restore/epilogue boundary. -/
abbrev expTwoMulFullLoopBoundaryBound : Nat :=
  expTwoMulBoundaryLoopBound expTwoMulFullLoopBodyBound

theorem expTwoMulNamedIterStepBound_eq :
    expTwoMulNamedIterStepBound = 189 := by
  norm_num [expTwoMulNamedIterStepBound]

theorem expTwoMulBoundaryLoopBound_eq (nSteps : Nat) :
    expTwoMulBoundaryLoopBound nSteps = nSteps + 17 := by
  unfold expTwoMulBoundaryLoopBound expTwoMulBoundaryPrefixBound
    expTwoMulBoundarySuffixBound
  omega

theorem expTwoMulIterationsBodyBound_zero :
    expTwoMulIterationsBodyBound 0 = 0 := by
  rfl

theorem expTwoMulIterationsBodyBound_eq (iterations : Nat) :
    expTwoMulIterationsBodyBound iterations = iterations * 189 := by
  rw [expTwoMulIterationsBodyBound, expTwoMulNamedIterStepBound_eq]

theorem expTwoMulIterationsBodyBound_succ (iterations : Nat) :
    expTwoMulIterationsBodyBound (iterations + 1) =
      expTwoMulNamedIterStepBound + expTwoMulIterationsBodyBound iterations := by
  unfold expTwoMulIterationsBodyBound
  rw [Nat.add_one, Nat.succ_mul, Nat.add_comm]

theorem expTwoMulIterationsBodyBound_mono {iterations iterations' : Nat}
    (h : iterations ≤ iterations') :
    expTwoMulIterationsBodyBound iterations ≤
      expTwoMulIterationsBodyBound iterations' := by
  unfold expTwoMulIterationsBodyBound
  exact Nat.mul_le_mul_right expTwoMulNamedIterStepBound h

theorem expTwoMulFullLoopBodyBound_eq :
    expTwoMulFullLoopBodyBound = 48384 := by
  norm_num [expTwoMulFullLoopBodyBound, expTwoMulIterationsBodyBound,
    expTwoMulNamedIterStepBound_eq]

theorem expTwoMulFullLoopBodyTailBound_eq :
    expTwoMulFullLoopBodyTailBound = 48195 := by
  norm_num [expTwoMulFullLoopBodyTailBound, expTwoMulIterationsBodyBound,
    expTwoMulNamedIterStepBound_eq]

/-- Peel the first named iteration from the 256-iteration body bound. -/
theorem expTwoMulFullLoopBodyBound_eq_iter_plus_tail :
    expTwoMulFullLoopBodyBound =
      expTwoMulNamedIterStepBound + expTwoMulFullLoopBodyTailBound := by
  norm_num [expTwoMulFullLoopBodyBound, expTwoMulFullLoopBodyTailBound,
    expTwoMulNamedIterStepBound_eq]

/-- View the 256-iteration full-body bound as one peeled iteration followed by
    the 255-iteration tail. -/
theorem expTwoMulFullLoopBodyBound_eq_tail_succ :
    expTwoMulFullLoopBodyBound = expTwoMulIterationsBodyBound (255 + 1) := by
  rw [expTwoMulFullLoopBodyBound_eq_iter_plus_tail,
    expTwoMulIterationsBodyBound_succ]

/-- The peeled named iteration plus the 255-iteration tail fits in the
    256-iteration full-body budget. -/
theorem expTwoMulNamedIterStepBound_add_fullTail_le_full :
    expTwoMulNamedIterStepBound + expTwoMulFullLoopBodyTailBound ≤
      expTwoMulFullLoopBodyBound := by
  rw [← expTwoMulFullLoopBodyBound_eq_iter_plus_tail]

/-- Same budget fact with the duplicated tail bound shape produced by the
    continuation-composition rule. -/
theorem expTwoMulNamedIterStepBound_add_max_fullTail_le_full :
    expTwoMulNamedIterStepBound +
        max expTwoMulFullLoopBodyTailBound expTwoMulFullLoopBodyTailBound ≤
      expTwoMulFullLoopBodyBound := by
  rw [Nat.max_self]
  exact expTwoMulNamedIterStepBound_add_fullTail_le_full

theorem expTwoMulFullLoopBoundaryBound_eq :
    expTwoMulFullLoopBoundaryBound = 48401 := by
  rw [expTwoMulFullLoopBoundaryBound, expTwoMulBoundaryLoopBound_eq,
    expTwoMulFullLoopBodyBound_eq]

end EvmAsm.Evm64.Exp.Compose
