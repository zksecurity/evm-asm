/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterExits

  Named exit postconditions for the fixed x19 merged EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

abbrev expTwoMulFixedIterMergedLoopPost
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let ptrFrame : Assertion :=
    (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
  let skipCondFrame : Assertion :=
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let skipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let skipCondRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ rw.getLimbN 3) **
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
    evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  let reloadCondFrame : Assertion :=
    (.x19 ↦ᵣ nextLimb) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let reloadSkipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ nextLimb) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let reloadCondRest : Assertion := skipCondRest
  let skipLoopPost : Assertion :=
    (fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
      ptrFrame
  let reloadLoopPost : Assertion :=
    fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
  fun h => skipLoopPost h ∨ reloadLoopPost h

abbrev expTwoMulFixedIterMergedExitPost
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) : Assertion :=
  let bit := e >>> (63 : BitVec 6).toNat
  let c6New := c6 + signExtend12 (-1 : BitVec 12)
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  let rw := expTwoMulCondRw squareW a0 a1 a2 a3
  let baseFrame : Assertion :=
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
  let ptrFrame : Assertion :=
    (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
  let skipCondFrame : Assertion :=
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let skipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let skipCondRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ rw.getLimbN 3) **
    ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
    ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
    ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
    ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
    evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 140) + 68))
  let reloadCondFrame : Assertion :=
    (.x19 ↦ᵣ nextLimb) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
  let reloadSkipRest : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
    (.x5 ↦ᵣ squareW.getLimbN 3) **
    evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
    regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
    memOwn evmSp ** memOwn (evmSp + 8) **
    memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
    (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
    (.x19 ↦ᵣ nextLimb) **
    (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
    ⌜c6New = 0⌝ **
    (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
    ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
    ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
  let reloadCondRest : Assertion := skipCondRest
  let skipExitPost : Assertion :=
    (fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
      ptrFrame
  let reloadExitPost : Assertion :=
    fun h =>
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
      ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
  fun h => skipExitPost h ∨ reloadExitPost h

abbrev expTwoMulFixedIterMergedExits
    (e c6 iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word) (base : Word) :
    List (Word × Assertion) :=
  [((base + 44),
      expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base),
   ((base + 296),
      expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)]

/-- Named-exit-list view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (expTwoMulFixedIterMergedExits e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  simpa [expTwoMulFixedIterMergedExits, expTwoMulFixedIterMergedLoopPost,
    expTwoMulFixedIterMergedExitPost]
    using
      exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base hbase

/-- Branch view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec with named loop/exit postconditions. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_named_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (expTwoMulFixedIterMergedLoopPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (base + 296)
      (expTwoMulFixedIterMergedExitPost e c6 iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base) := by
  simpa [expTwoMulFixedIterMergedExits]
    using
      cpsNBranchWithin_as_cpsBranchWithin
        (exp_msb_bit_test_fixed_full_iter_merged_named_exits_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
          e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
          r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
          v7 v11 base hbase)

end EvmAsm.Evm64.Exp.Compose
