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

/-- Aggregate bound for 256 saved-bit two-MUL loop iterations, excluding the
    prologue/pointer-advance and pointer-restore/epilogue boundary. -/
abbrev expTwoMulFullLoopBodyBound : Nat :=
  256 * expTwoMulNamedIterStepBound

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

theorem expTwoMulFullLoopBodyBound_eq :
    expTwoMulFullLoopBodyBound = 48384 := by
  norm_num [expTwoMulFullLoopBodyBound, expTwoMulNamedIterStepBound_eq]

theorem expTwoMulFullLoopBoundaryBound_eq :
    expTwoMulFullLoopBoundaryBound = 48401 := by
  rw [expTwoMulFullLoopBoundaryBound, expTwoMulBoundaryLoopBound_eq,
    expTwoMulFullLoopBodyBound_eq]

end EvmAsm.Evm64.Exp.Compose
