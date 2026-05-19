/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop

  Induction-facing wrappers for composing fixed EXP loop iterations while
  carrying the bundled semantic state.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostStateBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem pure_assertion_eq_emp_of_true {p : Prop} (hp : p) :
    (⌜p⌝ : Assertion) = empAssertion := by
  rw [← pure_true_eq_emp]
  funext ps
  apply propext
  constructor
  · intro h
    exact ⟨h.1, trivial⟩
  · intro h
    exact ⟨h.1, hp⟩

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

/-- Same-code one-step wrapper for the fixed-loop induction.

    Unlike
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step`, this
    composes the one-iteration prefix with continuations under the same
    canonical fixed EXP code. This is the form needed for recursive loop
    composition. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_sameCode
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound nSteps : Nat} {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
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
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (nBound + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
      hk hCount hBase hNextNext hBound)
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_state_elim
      (by omega) hCount hBranch hReload)

/-- Fixed-bound same-code state step for the recursive loop induction. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound_sameCode
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
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
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
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
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedReloadIterStepBound + nSteps)
      (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_sameCode
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase
    hControlMachine hk hCount hBase hNextNext
    (by rw [expTwoMulFixedReloadIterStepBound_eq])
    hBranch hReload

/-- Fixed-loop one-step wrapper with the canonical remaining-body bound.

    This is the induction-step shape: if every successor state can run for
    `iterations` remaining fixed iterations, the current state can run for
    `iterations + 1` fixed iterations. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    {exit : Word} {cr : CodeReq}
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
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit cr
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
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps
    (expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hDisjoint hFrame hbase
      hControlMachine hk hCount hBase hNextNext hBranch hReload)

/-- Same-code fixed-loop one-step wrapper with the canonical remaining-body
    bound. This is the recursive induction-step shape over the canonical EXP
    code block. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound_sameCode
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
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
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
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
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps
    (expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound_sameCode
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase
      hControlMachine hk hCount hBase hNextNext hBranch hReload)

/-- Final fixed-loop state-frame wrapper.

    At semantic iteration `255`, the next decrement exits the 256-iteration
    loop. This packages the existing state-invariant final peel so the loop
    induction can use the same framed state-precondition surface as the
    recursive case. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_final_iterationsBound
    {baseWord exponentWord : EvmWord} {iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame 255 baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (Q ** frame) := by
  have hStateMachine :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e machineC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
    simpa [hControlMachine] using hState
  have hRaw :
      cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb
          sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11)
        Q := by
    rw [expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
    exact
      exp_two_mul_fixed_iterations_body_peel_case_final_of_state_closed_bound_spec_within
        iterations
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base Q hbase hStateMachine hExit
  exact
    cpsTripleWithin_weaken
      (fun ps h =>
        by
          rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
            expTwoMulFixedIterPreNWithState_unfold,
            expTwoMulFixedIterStateAssertion_unfold,
            pure_assertion_eq_emp_of_true hState,
            sepConj_emp_right'] at h
          exact h)
      (fun ps h => h)
      (cpsTripleWithin_frameR frame hFrame hRaw)

end EvmAsm.Evm64.Exp.Compose
