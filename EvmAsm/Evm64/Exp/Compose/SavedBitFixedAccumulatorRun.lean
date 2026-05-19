/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedAccumulatorRun

  Small algebraic helpers for composing the pure fixed-loop accumulator run.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

/-- Split a pure fixed-loop accumulator run into a prefix and suffix. -/
theorem expTwoMulFixedAccumulatorRun_add
    (baseWord exponentWord accWord : EvmWord) (k m n : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k (m + n) =
      expTwoMulFixedAccumulatorRun baseWord exponentWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k m)
        (k + m) n := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorRun]
  | succ n ih =>
      rw [Nat.add_succ, expTwoMulFixedAccumulatorRun_succ,
        expTwoMulFixedAccumulatorRun_succ, ih]
      congr 1
      rw [Nat.add_assoc]

end EvmAsm.Evm64.Exp.Compose
