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

end EvmAsm.Evm64.Exp.Compose
