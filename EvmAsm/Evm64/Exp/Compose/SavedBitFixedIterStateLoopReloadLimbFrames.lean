/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames

  Opaque continuation-frame definitions for reload-limb direct adapters.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expReloadLimbDirectTailFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)

theorem expReloadLimbDirectTailFrame_unfold
    {ptr nextNextLimb : Word} :
    expReloadLimbDirectTailFrame ptr nextNextLimb =
      (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) := by
  delta expReloadLimbDirectTailFrame
  rfl

@[irreducible]
def expReloadDirectTailFrame
    (ptr nextNextLimb : Word) (frame : Assertion) : Assertion :=
  expReloadLimbDirectTailFrame ptr nextNextLimb ** frame

theorem expReloadDirectTailFrame_unfold
    {ptr nextNextLimb : Word} {frame : Assertion} :
    expReloadDirectTailFrame ptr nextNextLimb frame =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame) := by
  rw [expReloadDirectTailFrame, expReloadLimbDirectTailFrame_unfold]

@[irreducible]
def expReloadLimbDirectFalseFrame
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) = 0⌝)

theorem expReloadLimbDirectFalseFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝) := by
  delta expReloadLimbDirectFalseFrame
  rfl

@[irreducible]
def expReloadDirectFalseFrame
    (controlC6 e iterCount ptr nextLimb : Word)
    (frame : Assertion) : Assertion :=
  expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb ** frame

theorem expReloadDirectFalseFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} {frame : Assertion} :
    expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb frame =
      ((((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
          ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
          ⌜(e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) = 0⌝) **
        frame) := by
  rw [expReloadDirectFalseFrame, expReloadLimbDirectFalseFrame_unfold]

@[irreducible]
def expReloadLimbDirectTrueFrame
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
    ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
    ⌜(e >>> (63 : BitVec 6).toNat) +
      signExtend12 (0 : BitVec 12) ≠ 0⌝)

theorem expReloadLimbDirectTrueFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} :
    expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝) := by
  delta expReloadLimbDirectTrueFrame
  rfl

@[irreducible]
def expReloadDirectTrueFrame
    (controlC6 e iterCount ptr nextLimb : Word)
    (frame : Assertion) : Assertion :=
  expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb ** frame

theorem expReloadDirectTrueFrame_unfold
    {controlC6 e iterCount ptr nextLimb : Word} {frame : Assertion} :
    expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb frame =
      ((((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
          ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
          ⌜(e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0⌝) **
        frame) := by
  rw [expReloadDirectTrueFrame, expReloadLimbDirectTrueFrame_unfold]

end EvmAsm.Evm64.Exp.Compose
