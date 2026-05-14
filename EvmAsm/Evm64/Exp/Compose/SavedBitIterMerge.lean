/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge

  Branch-elimination helper for the named two-MUL saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Merge one named canonical appended-MUL EXP iteration with externally
    supplied continuations for the loop-back and loop-exit edges. This is the
    structural induction step needed by the full 256-iteration loop proof. -/
theorem exp_two_mul_named_iter_with_continuations_spec_within
    {nCont : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nCont (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nCont (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + nCont)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsBranchWithin_merge_same_cr
      (by
        simpa [expTwoMulIterBit, expTwoMulIterW, expTwoMulIterAw,
          expTwoMulIterRw, expTwoMulIterCountNew] using
          (exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_appended_mul_spec_within
            e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 base hbase))
      hLoop hExit

/-- Variant of `exp_two_mul_named_iter_with_continuations_spec_within` that
    permits different bounds for the loop-back and loop-exit continuations. -/
theorem exp_two_mul_named_iter_with_continuations_max_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit)

/-- Bounded variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. This lets the
    future 256-step induction use a closed-form loop bound while each branch
    continuation keeps its natural local bound. -/
theorem exp_two_mul_named_iter_with_continuations_bounded_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound :
      expTwoMulNamedIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_named_iter_with_continuations_max_spec_within
        e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 base hbase hLoop hExit)

/-- Exact named-bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_named_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulIterW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulIterW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_max_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase

/-- Closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_bounded_spec_within`, using the
    normalized one-iteration cost `189`. -/
theorem exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound : 189 + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (by simpa [expTwoMulNamedIterStepBound_eq] using hBound)
      hLoop hExit

/-- Exact closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_closed_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (189 + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase (by rfl)

end EvmAsm.Evm64.Exp.Compose
