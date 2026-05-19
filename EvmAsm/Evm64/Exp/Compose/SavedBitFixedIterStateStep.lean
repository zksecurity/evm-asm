/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

  State-count-aware wrappers for one fixed EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepBounds

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Bounded one-step wrapper whose nonzero decremented-count premise comes
    from the bundled fixed-loop count invariant. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

end EvmAsm.Evm64.Exp.Compose
