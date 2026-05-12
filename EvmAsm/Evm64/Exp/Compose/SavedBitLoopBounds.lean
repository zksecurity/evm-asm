/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

  Named step-count expressions for the two-MUL saved-bit EXP loop
  composition helpers.
-/

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

end EvmAsm.Evm64.Exp.Compose
