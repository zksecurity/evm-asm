/-
  EvmAsm.Evm64.SDiv.Compose.Bridges

  SDIV-Post-shape-matching wrappers around the generic memory-quad to
  `evmWordIs` bridges from `Compose/Base.lean`. Slot 3 of each quad uses
  `signExtend12 evm_sdivDividendTopLimbOff` (resp. `divisorTopLimbOff`)
  instead of the literal `signExtend12 24` / `56`, matching the shape
  produced by `saveRaSignsAbsSignXorThenDivCallPost` so callers can fold
  the four sum-memIs atoms without first unfolding the offset constants.

  Split out from `Compose/Base.lean` to respect the 1200-line cap on
  Compose files (slice 4 micro evm-asm-d5lxr).
-/

import EvmAsm.Evm64.SDiv.Compose.QuadMemBridges

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- Fully-explicit unfolding of `divModStackDispatchPre`: replaces the two
    `evmWordIs` atoms (`evmWordIs sp a` and `evmWordIs (sp + 32) b`) with
    eight raw `↦ₘ` atoms at absolute offsets `sp + 0/8/16/24` and
    `sp + 32/40/48/56`. Composes `divModStackDispatchPre_unfold` with the
    two `evmWordIs_sp_unfold` / `evmWordIs_sp32_unfold` lemmas. Useful for
    callers whose post produces 4 limb-level mems at each slot (rather
    than `evmWordIs`), so seq-composition with `evm_div_callable_spec_in_sdivCode`
    can proceed without manual evmWordIs folding. Slice 4 helper for
    evm-asm-j8bfz. -/
theorem divModStackDispatchPre_unfold_explicit
    {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word} :
    EvmAsm.Evm64.divModStackDispatchPre sp a b v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
      ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3)) **
     (((sp + 32) ↦ₘ b.getLimbN 0) ** ((sp + 40) ↦ₘ b.getLimbN 1) **
      ((sp + 48) ↦ₘ b.getLimbN 2) ** ((sp + 56) ↦ₘ b.getLimbN 3)) **
     EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  rw [EvmAsm.Evm64.divModStackDispatchPre_unfold,
      evmWordIs_sp_unfold, evmWordIs_sp32_unfold]

/-- SDIV-offset-shaped version of `divModStackDispatchPre_unfold_explicit`.
    It keeps the stack slots in the same `sp + signExtend12 ...` form produced
    by the SDIV wrapper postcondition, avoiding a separate address
    normalization step before `xperm_hyp`. -/
theorem divModStackDispatchPre_unfold_explicit_sdiv
    {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
     retMem dMem dloMem scratch_un0 : Word} :
    EvmAsm.Evm64.divModStackDispatchPre sp a b v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
      retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) **
     (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x0 ↦ᵣ (0 : Word)) **
     (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ a.getLimbN 0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ a.getLimbN 1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ a.getLimbN 2) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
        a.getLimbN 3)) **
     (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ b.getLimbN 0) **
      ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ b.getLimbN 1) **
      ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ b.getLimbN 2) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        b.getLimbN 3)) **
    EvmAsm.Evm64.divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  rw [divModStackDispatchPre_unfold_explicit]
  rw [show (sp + signExtend12 (0 : BitVec 12)) = sp by
    rw [show signExtend12 (0 : BitVec 12) = (0 : Word) by decide]
    simp]
  rw [show (sp + signExtend12 (8 : BitVec 12)) = sp + 8 by
    rw [show signExtend12 (8 : BitVec 12) = (8 : Word) by decide]]
  rw [show (sp + signExtend12 (16 : BitVec 12)) = sp + 16 by
    rw [show signExtend12 (16 : BitVec 12) = (16 : Word) by decide]]
  rw [show (sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) =
      sp + 24 by
    unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
    rw [show signExtend12 (24 : BitVec 12) = (24 : Word) by decide]]
  rw [show (sp + signExtend12 (32 : BitVec 12)) = sp + 32 by
    rw [show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]]
  rw [show (sp + signExtend12 (40 : BitVec 12)) = sp + 40 by
    rw [show signExtend12 (40 : BitVec 12) = (40 : Word) by decide]]
  rw [show (sp + signExtend12 (48 : BitVec 12)) = sp + 48 by
    rw [show signExtend12 (48 : BitVec 12) = (48 : Word) by decide]]
  rw [show (sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) =
      sp + 56 by
    unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
    rw [show signExtend12 (56 : BitVec 12) = (56 : Word) by decide]]

end EvmAsm.Evm64.SDiv.Compose
