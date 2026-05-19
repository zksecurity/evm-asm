/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateResidualPures

  Pure extractors for state-framed reload residuals in the fixed EXP loop.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Pure branch/control facts and successor-state payload carried by a
    state-framed reload residual. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    ((bit = true ∧
        (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
      (bit = false ∧
        (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0)) ∧
    (let outW := expTwoMulFixedBranchResult bit
      a0 a1 a2 a3 r0 r1 r2 r3
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      (outW.getLimbN 0) (outW.getLimbN 1)
      (outW.getLimbN 2) (outW.getLimbN 3)) := by
  have hState :=
    expTwoMulFixedReloadBranchResidualWithStateFrame_pure
      (bit := bit) h
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false] at h
    obtain ⟨psHead, _psFrame, _hDisjointFrame, _hUnionFrame,
      hHead, _hStateFrame⟩ := h
    have hScratchFrame :
        (let squareW := expSquaringCallSquareW r0 r1 r2 r3
        ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3
          (expTwoMulIterCountNew iterCount ≠ 0) **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
            e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
          empAssertion) psHead) := by
      simpa [sepConj_emp_right'] using hHead
    have h_pures :=
      expTwoMulFixedIterReloadSkipPointerScratchFrame_pures hScratchFrame
    rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
    exact
      ⟨h_exit, h_c6, Or.inr ⟨rfl, h_bit⟩,
        by simpa [expTwoMulFixedBranchResult_false] using hState⟩
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true] at h
    obtain ⟨psHead, _psFrame, _hDisjointFrame, _hUnionFrame,
      hHead, _hStateFrame⟩ := h
    have hScratchFrame :
        (let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3
          (expTwoMulIterCountNew iterCount ≠ 0) **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
            e c6 ptr nextLimb base) **
          empAssertion) psHead) := by
      simpa [sepConj_emp_right'] using hHead
    have h_pures :=
      expTwoMulFixedIterReloadCondPointerScratchFrame_pures hScratchFrame
    rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
    exact
      ⟨h_exit, h_c6, Or.inl ⟨rfl, h_bit⟩,
        by simpa [expTwoMulFixedBranchResult_true] using hState⟩

/-- Named true-bit specialization of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_pures`. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_true_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 ∧
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) := by
  rcases
    expTwoMulFixedReloadBranchResidualWithStateFrame_pures
      (bit := true) h with
    ⟨h_exit, h_c6, h_bit_cases, h_state⟩
  rcases h_bit_cases with h_bit | h_bit
  · exact ⟨h_exit, h_c6, h_bit.2,
      by simpa [expTwoMulFixedBranchResult_true] using h_state⟩
  · cases h_bit.1

/-- Named false-bit specialization of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_pures`. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_false_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 ∧
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
  rcases
    expTwoMulFixedReloadBranchResidualWithStateFrame_pures
      (bit := false) h with
    ⟨h_exit, h_c6, h_bit_cases, h_state⟩
  rcases h_bit_cases with h_bit | h_bit
  · cases h_bit.1
  · exact ⟨h_exit, h_c6, h_bit.2,
      by simpa [expTwoMulFixedBranchResult_false] using h_state⟩

end EvmAsm.Evm64.Exp.Compose
