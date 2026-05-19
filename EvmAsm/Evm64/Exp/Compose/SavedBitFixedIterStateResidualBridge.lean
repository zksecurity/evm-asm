/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateResidualBridge

  Re-entry bridges from state-framed reload residuals to the next fixed
  iteration precondition when the caller frame supplies the next pointer cell.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateResidualPures

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- A false-bit reload residual can re-enter the next state-carrying fixed
    iteration precondition once the remaining frame supplies the following
    pointer cell. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (((ptr + signExtend12 (-8 : BitVec 12) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
      64 nextLimb v6 (expTwoMulIterCountNew iterCount) v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      (squareW.getLimbN 3) (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ **
        frame) ps := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false] at h
  dsimp
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterPre_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [expTwoMulFixedIterSkipCountPostScratchPrefix,
    expTwoMulFixedIterSkipRestScratchPrefix,
    expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold,
    expTwoMulFixedIterScratchIs,
    expTwoMulFixedIterBaseFrame,
    expTwoMulIterBaseFrame_unfold,
    signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    ne_eq,
    evmWordIs] at h ⊢
  sep_perm h

/-- A true-bit reload residual can re-enter the next state-carrying fixed
    iteration precondition once the remaining frame supplies the following
    pointer cell. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (((ptr + signExtend12 (-8 : BitVec 12) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
      64 nextLimb v6 (expTwoMulIterCountNew iterCount) v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      (rw.getLimbN 3) (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1)
      (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1)
      (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        frame) ps := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true] at h
  dsimp
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterPre_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  simp only [expTwoMulFixedIterSkipCondCountPostScratchPrefix,
    expTwoMulFixedIterSkipCondRestScratchPrefix,
    expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame,
    expTwoMulFixedIterSkipCondRestScratchSuffix,
    expTwoMulFixedIterReloadPointerFrame_unfold,
    expTwoMulFixedIterScratchIs,
    expTwoMulIterBaseFrame_unfold,
    signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    ne_eq,
    evmWordIs] at h ⊢
  sep_perm h

end EvmAsm.Evm64.Exp.Compose
