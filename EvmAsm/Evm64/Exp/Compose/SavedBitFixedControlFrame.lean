/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

  Small control-invariant helpers for the fixed-loop induction frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)

theorem expTwoMulFixedSavedNextLimbFrame_unfold
    {ptr nextNextLimb : Word} :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  delta expTwoMulFixedSavedNextLimbFrame
  rfl

theorem expTwoMulFixedSavedNextLimbFrame_pcFree
    (ptr nextNextLimb : Word) :
    (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb) :=
  ⟨expTwoMulFixedSavedNextLimbFrame_pcFree ptr nextNextLimb⟩

@[irreducible]
def expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (2 - (k + 1) / 64))

theorem expTwoMulFixedSavedNextLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (2 - (k + 1) / 64)) := by
  delta expTwoMulFixedSavedNextLimbFrameN
  rfl

theorem expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold, hNextNext]

@[irreducible]
def expTwoMulFixedReloadLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (1 - k / 64))

theorem expTwoMulFixedReloadLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (1 - k / 64)) := by
  delta expTwoMulFixedReloadLimbFrameN
  rfl

theorem expTwoMulFixedReloadLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 63) :
    expTwoMulFixedReloadLimbFrameN exponentWord k ptr =
      expTwoMulFixedReloadLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold,
    expTwoMulFixedReloadLimbFrameN_unfold]
  congr 1
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

theorem expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hMod : k % 64 = 63)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedReloadLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedReloadLimbFrameN_unfold, hNextNext]
  congr 1
  have hdiv : (k + 1) / 64 = k / 64 + 1 := by
    omega
  rw [hdiv]
  have hCases : k / 64 = 0 ∨ k / 64 = 1 ∨ 2 ≤ k / 64 := by
    omega
  rcases hCases with hZero | hOne | hGe
  · rw [hZero]
  · rw [hOne]
  · rw [Nat.sub_eq_zero_of_le (by omega : 2 ≤ k / 64 + 1),
      Nat.sub_eq_zero_of_le (by omega : 1 ≤ k / 64)]

theorem expTwoMulFixedControlInvariant_nextLimb
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  exact hControl.2

theorem expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  rw [expTwoMulFixedControlInvariant_nextLimb hControl]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

end EvmAsm.Evm64.Exp.Compose
