/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases

  Framed scratch case splits for fixed x19 case-post assertions.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterPointerPost_eq_pointerFrame
    {ptr nextLimb : Word} :
    expTwoMulFixedIterPointerPost ptr nextLimb =
      expTwoMulFixedIterPointerFrame ptr nextLimb := by
  rw [expTwoMulFixedIterPointerFrame_unfold]

theorem expTwoMulFixedIterCaseLoopPost_scratch_cases_pointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseLoopPost_scratch_cases_frame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        by
          simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          by
            simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases_frame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerPost ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  obtain ⟨psCase, psFrame, hDisjoint, hUnion, hCase, hFrame⟩ := h
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases hCase with hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            psCase, psFrame, hDisjoint, hUnion, hScratch, hFrame⟩))

theorem expTwoMulFixedIterCaseExitPost_scratch_cases_pointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases_frame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨v6, v7, v10, v11, d0, d1, d2, d3,
        by
          simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v6, v7, v10, v11, d0, d1, d2, d3,
          by
            simpa [expTwoMulFixedIterPointerPost_eq_pointerFrame] using hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩))

end EvmAsm.Evm64.Exp.Compose
