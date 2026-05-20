/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFrameLoopDirect

  Direct-loop wrappers that consume the with-state induction-frame precondition.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFramePre
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopDirect
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopPreReload

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_reloadTail_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_reload_of_control hC6]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase hC6
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_preReload_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v6' v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_pre_reload_of_control hC6]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase hC6
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_control_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr
        nextLimb evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  rw [expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
    hC6 hNotPre]
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_succ_no_reload_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      (expTwoMulFixedControlInvariant_ordinary_no_reload_mod
        hControl hC6 hNotPre)
      hNextNext hBranch hReloadFalse hReloadTrue hExit

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0)
    (hNotPre : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hPreState :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) psPre := by
    rw [← expTwoMulFixedIterPreNWithInductionFrame_ordinary_of_control
      hC6 hNotPre]
    exact hPre
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPreState
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_ordinary_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNotPre hNextNext hBranch hReloadFalse hReloadTrue
      hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

end EvmAsm.Evm64.Exp.Compose
