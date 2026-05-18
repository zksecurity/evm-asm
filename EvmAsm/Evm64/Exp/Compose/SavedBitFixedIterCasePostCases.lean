/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases

  Case-splitting lemmas for fixed x19 named case-post assertions.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterCaseLoopPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rfl

theorem expTwoMulFixedIterCaseExitPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps := by
  rfl

theorem expTwoMulFixedIterReloadLoopPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps := by
  rfl

theorem expTwoMulFixedIterReloadExitPost_iff
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState} :
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ↔
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps := by
  rfl

theorem expTwoMulFixedIterCaseLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps :=
  expTwoMulFixedIterCaseLoopPost_iff.mp h

theorem expTwoMulFixedIterCaseExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps ∨
    expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base ps :=
  expTwoMulFixedIterCaseExitPost_iff.mp h

theorem expTwoMulFixedIterReloadLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps :=
  expTwoMulFixedIterReloadLoopPost_iff.mp h

theorem expTwoMulFixedIterReloadExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps :=
  expTwoMulFixedIterReloadExitPost_iff.mp h

theorem expTwoMulFixedIterSkipLoopPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps := by
  obtain ⟨psLeft, psRight, hDisjoint, hUnion, hCases, hPtr⟩ := h
  rcases hCases with hCond | hSkip
  · exact Or.inl ⟨psLeft, psRight, hDisjoint, hUnion, hCond, hPtr⟩
  · exact Or.inr ⟨psLeft, psRight, hDisjoint, hUnion, hSkip, hPtr⟩

theorem expTwoMulFixedIterSkipExitPost_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps := by
  obtain ⟨psLeft, psRight, hDisjoint, hUnion, hCases, hPtr⟩ := h
  rcases hCases with hCond | hSkip
  · exact Or.inl ⟨psLeft, psRight, hDisjoint, hUnion, hCond, hPtr⟩
  · exact Or.inr ⟨psLeft, psRight, hDisjoint, hUnion, hSkip, hPtr⟩

theorem expTwoMulFixedIterCaseLoopPost_count_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount ≠ 0) ps := by
  rcases expTwoMulFixedIterCaseLoopPost_cases h with hSkip | hReload
  · rcases expTwoMulFixedIterSkipLoopPost_cases hSkip with hCond | hSkipCount
    · exact Or.inl hCond
    · exact Or.inr (Or.inl hSkipCount)
  · rcases expTwoMulFixedIterReloadLoopPost_cases hReload with hCond | hSkipCount
    · exact Or.inr (Or.inr (Or.inl hCond))
    · exact Or.inr (Or.inr (Or.inr hSkipCount))

theorem expTwoMulFixedIterCaseExitPost_count_cases
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word} {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    (expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) **
      expTwoMulFixedIterPointerPost ptr nextLimb) ps ∨
    expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps ∨
    expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      (expTwoMulIterCountNew iterCount = 0) ps := by
  rcases expTwoMulFixedIterCaseExitPost_cases h with hSkip | hReload
  · rcases expTwoMulFixedIterSkipExitPost_cases hSkip with hCond | hSkipCount
    · exact Or.inl hCond
    · exact Or.inr (Or.inl hSkipCount)
  · rcases expTwoMulFixedIterReloadExitPost_cases hReload with hCond | hSkipCount
    · exact Or.inr (Or.inr (Or.inl hCond))
    · exact Or.inr (Or.inr (Or.inr hSkipCount))

theorem expTwoMulFixedIterSkipCondCountPost_pures
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPost
    expTwoMulFixedIterSkipCondFrame at h
  obtain ⟨_, _, _, _, hMain, hFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, _⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hFrameTail⟩ := hFrame
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hFrameTail
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, hBit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterSkipCountPost_pures
    {iterCount e c6 sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPost
    expTwoMulFixedIterSkipRest at h
  obtain ⟨_, _, _, _, hMain, _hBaseFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, hRest⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hRest1⟩ := hRest
  obtain ⟨_, _, _, _, _, hRest2⟩ := hRest1
  obtain ⟨_, _, _, _, _, hRest3⟩ := hRest2
  obtain ⟨_, _, _, _, _, hRest4⟩ := hRest3
  obtain ⟨_, _, _, _, _, hRest5⟩ := hRest4
  obtain ⟨_, _, _, _, _, hRest6⟩ := hRest5
  obtain ⟨_, _, _, _, _, hRest7⟩ := hRest6
  obtain ⟨_, _, _, _, _, hRest8⟩ := hRest7
  obtain ⟨_, _, _, _, _, hRest9⟩ := hRest8
  obtain ⟨_, _, _, _, _, hRest10⟩ := hRest9
  obtain ⟨_, _, _, _, _, hRest11⟩ := hRest10
  obtain ⟨_, _, _, _, _, hRest12⟩ := hRest11
  obtain ⟨_, _, _, _, _, hRest13⟩ := hRest12
  obtain ⟨_, _, _, _, _, hRest14⟩ := hRest13
  obtain ⟨_, _, _, _, _, hRest15⟩ := hRest14
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hRest15
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, hBit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨hExit, hC6, hBit⟩

theorem expTwoMulFixedIterReloadCondCountPost_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {ps : PartialState}
    (h :
      expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterReloadCondCountPost
    expTwoMulFixedIterReloadCondFrame at h
  obtain ⟨_, _, _, _, hMain, hFrame⟩ := h
  obtain ⟨_, _, _, _, hCount, _⟩ := hMain
  obtain ⟨_, _, _, _, _, hCountTail⟩ := hCount
  have hExit : exitCond := ((sepConj_pure_right _).1 hCountTail).2
  obtain ⟨_, _, _, _, _, hFrame1⟩ := hFrame
  obtain ⟨_, _, _, _, _, hFrame2⟩ := hFrame1
  have hC6 : c6 + signExtend12 (-1 : BitVec 12) = 0 :=
    ((sepConj_pure_left _).1 hFrame2).1
  have hAfterC6 := ((sepConj_pure_left _).1 hFrame2).2
  obtain ⟨_, _, _, _, _, hFrame3⟩ := hAfterC6
  obtain ⟨_, _, _, _, _, hBitPure⟩ := hFrame3
  obtain ⟨_, hBit⟩ := hBitPure
  exact ⟨hExit, hC6, hBit⟩

end EvmAsm.Evm64.Exp.Compose
