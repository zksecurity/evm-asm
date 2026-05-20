/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFramePre

  With-state precondition helpers that instantiate the saved-limb induction
  frame selected by the fixed-loop control counter.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStatePre

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedIterPreNWithInductionFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
    e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
    r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
    (expTwoMulFixedInductionFrameN exponentWord k controlC6 ptr)

theorem expTwoMulFixedIterPreNWithInductionFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedInductionFrameN exponentWord k controlC6 ptr) := by
  delta expTwoMulFixedIterPreNWithInductionFrame
  rfl

theorem expTwoMulFixedIterPreNWithInductionFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11).pcFree := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterPreNWithInductionFrame
    (k : Nat) (baseWord exponentWord : EvmWord) (controlC6 : Word)
    (e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11) :=
  ⟨expTwoMulFixedIterPreNWithInductionFrame_pcFree⟩

theorem expTwoMulFixedIterPreNWithInductionFrame_reload_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_pre_reload_of_control hC6]

theorem expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 =
    expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord controlC6
      e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11
      (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_unfold,
    expTwoMulFixedInductionFrameN_ordinary_of_control hC6 hNotPre]

theorem expTwoMulFixedIterPreNWithInductionFrame_step_cases_of_control
    {k : Nat} {baseWord exponentWord : EvmWord} {controlC6 : Word}
    {e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp) :
    expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedReloadTailFrameN exponentWord k ptr) ∨
      expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 =
        expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11
          (expTwoMulFixedPreReloadFrameN exponentWord k ptr) ∨
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
          controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 =
          expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
            controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
            tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
            a0 a1 a2 a3 v7 v11
            (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) ∧
        k % 64 < 62) := by
  rcases expTwoMulFixedControlInvariant_step_cases hControl with
    hReload | hPre | ⟨hOrd, hNotPre, hMod⟩
  · exact Or.inl
      (expTwoMulFixedIterPreNWithInductionFrame_reload_of_control hReload)
  · exact Or.inr (Or.inl
      (expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control hPre))
  · exact Or.inr (Or.inr
      ⟨expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
          hOrd hNotPre,
        hMod⟩)

end EvmAsm.Evm64.Exp.Compose
