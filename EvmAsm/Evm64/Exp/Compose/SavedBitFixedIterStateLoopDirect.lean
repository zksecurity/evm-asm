/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopDirect

  Head-step wrappers that let the fixed-loop induction recurse directly
  through reload cases.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Head step wrapper with direct reload re-entry continuations.

    This combines the `k < 255` reload-direct step with the `k = 255` final
    exit case. The current frame supplies the next pointer cell; recursive
    branch continuations keep that cell framed, while recursive reload
    continuations re-enter with the loaded pointer cell and branch pures. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
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
            ((((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame))
          (Q ** ((((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝ **
              frame))
          (Q ** ((((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝ **
              frame))
          (Q ** ((((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        ((((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame))
      (Q ** ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame)) := by
  have hFrameCurrent :
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame).pcFree) := by
    pcFree
    exact hFrame
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base
      (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12) ↦ₘ nextNextLimb) ** frame)
      Q hFrameCurrent hbase hControlMachine hk hBase hNextNext
      hBranch
      (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        cases bit
        · exact
            cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
              (hReloadFalse hk_lt v6' v7' v10' v11' d0' d1' d2' d3')
        · exact
            cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
              (hReloadTrue hk_lt v6' v7' v10' v11' d0' d1' d2' d3'))
      hExit

/-- Convenience form of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre`
    when the only carried frame is the next pointer cell required by reload
    re-entry. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
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
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
      (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [sepConj_emp_right']
        exact h)
      (fun _ h => by
        rw [sepConj_emp_right'] at h
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base empAssertion Q (by pcFree) hbase
        hControlMachine hk hBase hNextNext
        (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              rw [sepConj_emp_right'] at h
              exact h)
            (fun _ h => by
              rw [sepConj_emp_right']
              exact h)
            (hBranch hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3'))
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              rw [sepConj_emp_right'] at h
              exact h)
            (fun _ h => by
              rw [sepConj_emp_right']
              exact h)
            (hReloadFalse hk_lt v6' v7' v10' v11' d0' d1' d2' d3'))
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              rw [sepConj_emp_right'] at h
              exact h)
            (fun _ h => by
              rw [sepConj_emp_right']
              exact h)
            (hReloadTrue hk_lt v6' v7' v10' v11' d0' d1' d2' d3'))
        hExit)

/-- Pointer-only direct head step with the current saved-limb cell expressed
    through the semantic iteration-indexed frame name. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_from_pre
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
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        exact h)
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
        hNextNext hBranch hReloadFalse hReloadTrue hExit)

/-- Ordinary no-reload direct head step with the saved-limb frame advanced to
    the recursive successor index. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_succ_no_reload_from_pre
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
    (hMod : k % 64 < 62)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  have hStep :=
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hNextNext hBranch hReloadFalse hReloadTrue hExit
  exact cpsTripleWithin_weaken
    (fun _ h => h)
    (fun _ h => by
      rw [← expTwoMulFixedSavedNextLimbFrameN_succ_no_reload
        (exponentWord := exponentWord) (ptr := ptr) hMod]
      exact h)
    hStep

/-- Direct head step with the current saved-limb cell expressed by the
    layout-correct reload-limb frame at a reload boundary. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_from_pre
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
    (hMod : k % 64 = 63)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
    expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext hMod hNextNext
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        exact h)
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
        hNextNext hBranch hReloadFalse hReloadTrue hExit)

/-- Control-invariant form of the reload-boundary direct head step.

    Recursive reload branches naturally have the current control invariant and
    the machine fact that decrementing `c6` reaches zero; this wrapper derives
    the modulo boundary fact used by the lower-level named-frame theorem. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre
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
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_from_pre
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)
    hNextNext hBranch hReloadFalse hReloadTrue hExit

/-- From-pre variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre`.

    The current `WithStateFrame` precondition already carries the control
    invariant; this wrapper extracts it internally, leaving recursive reload
    callers to provide only the branch fact `hC6`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_pre
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
            (((ptr + signExtend12 (-8 : BitVec 12)) +
              signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadFalse :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let squareW := expSquaringCallSquareW r0 r1 r2 r3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (squareW.getLimbN 3) (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0' d1' d2' d3'
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) = 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hReloadTrue :
      k < 255 →
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            64 nextLimb v6' (expTwoMulIterCountNew iterCount) v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
            (rw.getLimbN 3) (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            d0' d1' d2' d3'
            (rw.getLimbN 0) (rw.getLimbN 1)
            (rw.getLimbN 2) (rw.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
              ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
              ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
              ⌜(e >>> (63 : BitVec 6).toNat) +
                signExtend12 (0 : BitVec 12) ≠ 0⌝))
          (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
            signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNextNext hBranch hReloadFalse hReloadTrue hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

end EvmAsm.Evm64.Exp.Compose
