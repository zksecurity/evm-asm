/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop

  Induction-facing wrappers for composing fixed EXP loop iterations while
  carrying the bundled semantic state.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Named-bound one-step wrapper for the fixed-loop induction.

    This specializes
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step` to the
    canonical fixed reload-step bound, so a future Nat induction can recurse
    with `expTwoMulFixedReloadIterStepBound + tailBound` directly. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {cr : CodeReq}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hDisjoint :
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).Disjoint cr)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6'
            (expTwoMulIterCountNew iterCount)
            v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0' d1' d2' d3'
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedReloadIterStepBound + nSteps)
      (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame Q hDisjoint hFrame hbase
    hControlMachine hk hCount hBase hNextNext
    (by rw [expTwoMulFixedReloadIterStepBound_eq])
    hBranch hReload

end EvmAsm.Evm64.Exp.Compose
