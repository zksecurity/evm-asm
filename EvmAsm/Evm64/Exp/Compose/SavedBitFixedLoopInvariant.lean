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

/-- The next exponent bit consumed by iteration `k`, as a Bool.

    The fixed loop scans most-significant bit first, so iteration `k` consumes
    source bit `255 - k`. -/
def expTwoMulFixedProcessedBit (exponentWord : EvmWord) (k : Nat) : Bool :=
  decide (((exponentWord >>> (255 - k)).toNat % 2) = 1)

def expTwoMulFixedProcessedBitWord (exponentWord : EvmWord) (k : Nat) : Word :=
  if expTwoMulFixedProcessedBit exponentWord k then 1 else 0

theorem expTwoMulFixedProcessedBitWord_eq_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k = 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = false := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide

theorem expTwoMulFixedProcessedBitWord_ne_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k ≠ 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = true := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide

theorem expTwoMulFixedProcessedBitWord_add_zero_eq_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k +
        signExtend12 (0 : BitVec 12) = 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = false := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide

theorem expTwoMulFixedProcessedBitWord_add_zero_ne_zero_iff
    (exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedProcessedBitWord exponentWord k +
        signExtend12 (0 : BitVec 12) ≠ 0 ↔
      expTwoMulFixedProcessedBit exponentWord k = true := by
  unfold expTwoMulFixedProcessedBitWord
  cases expTwoMulFixedProcessedBit exponentWord k <;> decide

theorem expTwoMulFixedProcessedExponent_succ_toNat
    (exponentWord : EvmWord) {k : Nat} (hk : k < 256) :
    (expTwoMulFixedProcessedExponent exponentWord (k + 1)).toNat =
      2 * (expTwoMulFixedProcessedExponent exponentWord k).toNat +
        if expTwoMulFixedProcessedBit exponentWord k then 1 else 0 := by
  unfold expTwoMulFixedProcessedExponent expTwoMulFixedProcessedBit
  simp [Nat.shiftRight_eq_div_pow]
  set shift := 255 - k
  have hShift : 256 - k = shift + 1 := by omega
  rw [hShift]
  rw [show 2 ^ (shift + 1) = 2 ^ shift * 2 by rw [Nat.pow_succ]]
  rw [← Nat.div_div_eq_div_mul]
  let shifted := exponentWord.toNat / 2 ^ shift
  have hmod : shifted % 2 < 2 := Nat.mod_lt shifted (by decide)
  have hmod_cases : shifted % 2 = 0 ∨ shifted % 2 = 1 := by omega
  rcases hmod_cases with h_zero | h_one
  · simp [shifted, h_zero]
    omega
  · simp [shifted, h_one]
    omega

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

theorem expTwoMulFixedAccumulatorStep_eq_target_of_processedExponent_succ
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    (hNext :
      (expTwoMulFixedProcessedExponent exponentWord (k + 1)).toNat =
        2 * (expTwoMulFixedProcessedExponent exponentWord k).toNat +
          if bit then 1 else 0) :
    expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k) bit =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1) := by
  unfold expTwoMulFixedAccumulatorStep expTwoMulFixedAccumulatorTarget
  by_cases hbit : bit
  · simp [hbit] at hNext ⊢
    exact (EvmWord.exp_double_add_one_right_of_toNat_eq
      baseWord
      (expTwoMulFixedProcessedExponent exponentWord k)
      (expTwoMulFixedProcessedExponent exponentWord (k + 1))
      hNext).symm
  · simp [hbit] at hNext ⊢
    exact (EvmWord.exp_double_right_of_toNat_eq
      baseWord
      (expTwoMulFixedProcessedExponent exponentWord k)
      (expTwoMulFixedProcessedExponent exponentWord (k + 1))
      hNext).symm

theorem expTwoMulFixedAccumulatorStep_eq_target_succ
    (baseWord exponentWord : EvmWord) {k : Nat} (hk : k < 256) :
    expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorTarget baseWord exponentWord k)
        (expTwoMulFixedProcessedBit exponentWord k) =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + 1) :=
  expTwoMulFixedAccumulatorStep_eq_target_of_processedExponent_succ
    (expTwoMulFixedProcessedExponent_succ_toNat exponentWord hk)

/-- Semantic accumulator obtained by running `n` generic fixed-loop updates
    starting from the target at iteration `k`.

    This is intentionally indexed by `n`, not by concrete iteration names, so
    the loop proof can recurse over this family instead of peeling 256 named
    pre/post pairs. -/
def expTwoMulFixedAccumulatorAfter
    (baseWord exponentWord : EvmWord) (k : Nat) : Nat → EvmWord
  | 0 => expTwoMulFixedAccumulatorTarget baseWord exponentWord k
  | n + 1 =>
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorAfter baseWord exponentWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n))

theorem expTwoMulFixedAccumulatorAfter_zero
    (baseWord exponentWord : EvmWord) (k : Nat) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k 0 =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord k := by
  rfl

theorem expTwoMulFixedAccumulatorAfter_succ
    (baseWord exponentWord : EvmWord) (k n : Nat) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k (n + 1) =
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorAfter baseWord exponentWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n)) := by
  rfl

theorem expTwoMulFixedAccumulatorAfter_eq_target_add
    (baseWord exponentWord : EvmWord) (k n : Nat) (hBound : k + n ≤ 256) :
    expTwoMulFixedAccumulatorAfter baseWord exponentWord k n =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + n) := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorAfter]
  | succ n ih =>
      rw [expTwoMulFixedAccumulatorAfter_succ]
      have hPrev : k + n ≤ 256 := by omega
      have hStep : k + n < 256 := by omega
      rw [ih hPrev]
      simpa [Nat.add_assoc] using
        expTwoMulFixedAccumulatorStep_eq_target_succ
          baseWord exponentWord (k := k + n) hStep

theorem expTwoMulFixedAccumulatorInvariant_of_after
    {baseWord exponentWord : EvmWord} {k n : Nat}
    {r0' r1' r2' r3' : Word}
    (hBound : k + n ≤ 256)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorAfter baseWord exponentWord k n) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + n)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hRun, expTwoMulFixedAccumulatorAfter_eq_target_add
    baseWord exponentWord k n hBound]

/-- Semantic accumulator obtained by running `n` generic fixed-loop updates
    from an arbitrary current accumulator word.

    This is the form the CPS loop composition should expose: the machine proof
    establishes the concrete post-iteration result is this run, while the
    invariant theorem below connects that run back to the mathematical target. -/
def expTwoMulFixedAccumulatorRun
    (baseWord exponentWord accWord : EvmWord) (k : Nat) : Nat → EvmWord
  | 0 => accWord
  | n + 1 =>
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n))

theorem expTwoMulFixedAccumulatorRun_zero
    (baseWord exponentWord accWord : EvmWord) (k : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k 0 =
      accWord := by
  rfl

theorem expTwoMulFixedAccumulatorRun_succ
    (baseWord exponentWord accWord : EvmWord) (k n : Nat) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k (n + 1) =
      expTwoMulFixedAccumulatorStep baseWord
        (expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n)
        (expTwoMulFixedProcessedBit exponentWord (k + n)) := by
  rfl

theorem expTwoMulFixedAccumulatorRun_eq_after_of_start
    {baseWord exponentWord accWord : EvmWord} {k n : Nat}
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord k) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n =
      expTwoMulFixedAccumulatorAfter baseWord exponentWord k n := by
  induction n with
  | zero =>
      simp [expTwoMulFixedAccumulatorRun, expTwoMulFixedAccumulatorAfter,
        hStart]
  | succ n ih =>
      rw [expTwoMulFixedAccumulatorRun_succ,
        expTwoMulFixedAccumulatorAfter_succ, ih]

theorem expTwoMulFixedAccumulatorRun_eq_target_add
    {baseWord exponentWord accWord : EvmWord} {k n : Nat}
    (hBound : k + n ≤ 256)
    (hStart :
      accWord = expTwoMulFixedAccumulatorTarget baseWord exponentWord k) :
    expTwoMulFixedAccumulatorRun baseWord exponentWord accWord k n =
      expTwoMulFixedAccumulatorTarget baseWord exponentWord (k + n) := by
  rw [expTwoMulFixedAccumulatorRun_eq_after_of_start hStart]
  exact expTwoMulFixedAccumulatorAfter_eq_target_add
    baseWord exponentWord k n hBound

theorem expTwoMulFixedAccumulatorInvariant_of_run
    {baseWord exponentWord : EvmWord} {k n : Nat}
    {r0 r1 r2 r3 r0' r1' r2' r3' : Word}
    (hBound : k + n ≤ 256)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hRun :
      expResultWord r0' r1' r2' r3' =
        expTwoMulFixedAccumulatorRun baseWord exponentWord
          (expResultWord r0 r1 r2 r3) k n) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + n)
      r0' r1' r2' r3' := by
  unfold expTwoMulFixedAccumulatorInvariant at *
  rw [hRun, expTwoMulFixedAccumulatorRun_eq_target_add
    hBound hInv]

/-- Expected fixed-loop `x19` exponent cursor at the start of iteration `k`.

    The loop starts from limb 3, shifts the current limb left once per bit, and
    reloads the next lower limb every 64 iterations. -/
def expTwoMulFixedCursorWord (exponentWord : EvmWord) (k : Nat) : Word :=
  exponentWord.getLimbN (3 - k / 64) <<< (k % 64)

def expTwoMulFixedCursorInvariant
    (exponentWord : EvmWord) (k : Nat) (e : Word) : Prop :=
  e = expTwoMulFixedCursorWord exponentWord k

@[irreducible]
def expTwoMulFixedCursorAssertion
    (exponentWord : EvmWord) (k : Nat) (e : Word) : Assertion :=
  ⌜expTwoMulFixedCursorInvariant exponentWord k e⌝

theorem expTwoMulFixedCursorAssertion_unfold
    {exponentWord : EvmWord} {k : Nat} {e : Word} :
    expTwoMulFixedCursorAssertion exponentWord k e =
      ⌜expTwoMulFixedCursorInvariant exponentWord k e⌝ := by
  delta expTwoMulFixedCursorAssertion
  rfl

theorem expTwoMulFixedCursorAssertion_pcFree
    {exponentWord : EvmWord} {k : Nat} {e : Word} :
    (expTwoMulFixedCursorAssertion exponentWord k e).pcFree := by
  rw [expTwoMulFixedCursorAssertion_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedCursorAssertion
    (exponentWord : EvmWord) (k : Nat) (e : Word) :
    Assertion.PCFree (expTwoMulFixedCursorAssertion exponentWord k e) :=
  ⟨expTwoMulFixedCursorAssertion_pcFree⟩

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
