/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

  Symbolic loop invariant anchor for the fixed x19 two-MUL saved-bit EXP loop.
-/

import EvmAsm.Evm64.EvmWordArith.Exp
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The exponent prefix that has been consumed after `k` fixed-loop iterations.
    The fixed loop scans most-significant bit first, so this is the high prefix
    shifted down into the low end of the EVM word. -/
def expTwoMulFixedProcessedExponent (exponentWord : EvmWord) (k : Nat) :
    EvmWord :=
  exponentWord >>> (256 - k)

/-- Semantic accumulator target after `k` fixed-loop iterations. -/
def expTwoMulFixedAccumulatorTarget
    (baseWord exponentWord : EvmWord) (k : Nat) : EvmWord :=
  EvmWord.exp baseWord (expTwoMulFixedProcessedExponent exponentWord k)

theorem expTwoMulFixedProcessedExponent_full (exponentWord : EvmWord) :
    expTwoMulFixedProcessedExponent exponentWord 256 = exponentWord := by
  simp [expTwoMulFixedProcessedExponent]

theorem expTwoMulFixedAccumulatorTarget_full
    (baseWord exponentWord : EvmWord) :
    expTwoMulFixedAccumulatorTarget baseWord exponentWord 256 =
      EvmWord.exp baseWord exponentWord := by
  simp [expTwoMulFixedAccumulatorTarget, expTwoMulFixedProcessedExponent_full]

/-- One Bool-unified semantic accumulator update for the fixed loop.

    Every iteration squares the current accumulator. The conditional multiply
    path additionally multiplies by the original base when the consumed bit is
    one. -/
def expTwoMulFixedAccumulatorStep
    (baseWord accWord : EvmWord) (bit : Bool) : EvmWord :=
  let squared := accWord * accWord
  if bit then baseWord * squared else squared

/-- Pure semantic invariant carried by the fixed-loop induction path. -/
def expTwoMulFixedAccumulatorInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) : Prop :=
  expResultWord r0 r1 r2 r3 =
    expTwoMulFixedAccumulatorTarget baseWord exponentWord k

@[irreducible]
def expTwoMulFixedSemanticInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) : Assertion :=
  ⌜expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3⌝

theorem expTwoMulFixedSemanticInvariant_unfold
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word} :
    expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3 =
      ⌜expTwoMulFixedAccumulatorInvariant baseWord exponentWord k r0 r1 r2 r3⌝ := by
  delta expTwoMulFixedSemanticInvariant
  rfl

theorem expTwoMulFixedSemanticInvariant_pcFree
    {baseWord exponentWord : EvmWord} {k : Nat}
    {r0 r1 r2 r3 : Word} :
    (expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3).pcFree := by
  rw [expTwoMulFixedSemanticInvariant_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedSemanticInvariant
    (baseWord exponentWord : EvmWord) (k : Nat)
    (r0 r1 r2 r3 : Word) :
    Assertion.PCFree
      (expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3) :=
  ⟨expTwoMulFixedSemanticInvariant_pcFree⟩

/-- Generic Bool-unified successor rule for the semantic accumulator invariant.

    The CPS one-step proof should discharge `hStep` from the concrete
    squaring/conditional-multiply case and `hSemanticStep` from the exponent
    bit algebra, then use this lemma for both branch outcomes. -/
theorem expTwoMulFixedAccumulatorInvariant_succ_of_step
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hStep :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorStep baseWord
          (expResultWord r0 r1 r2 r3) bit)
    (hSemanticStep :
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) bit =
          expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1)) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hStep, hInv, hSemanticStep]

/-- The fixed iteration precondition indexed by the semantic iteration count.

    This is the precondition family future fixed-loop induction should recurse
    over, instead of generating one named precondition per concrete iteration. -/
@[irreducible]
def expTwoMulFixedIterPreN
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
    vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
  expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3

theorem expTwoMulFixedIterPreN_unfold
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPreN k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
        vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 **
      expTwoMulFixedSemanticInvariant baseWord exponentWord k r0 r1 r2 r3) := by
  delta expTwoMulFixedIterPreN
  rfl

theorem expTwoMulFixedIterPreN_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord}
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPreN k baseWord exponentWord
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11).pcFree := by
  rw [expTwoMulFixedIterPreN_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterPreN
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPreN k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11) :=
  ⟨expTwoMulFixedIterPreN_pcFree⟩

end EvmAsm.Evm64.Exp.Compose
