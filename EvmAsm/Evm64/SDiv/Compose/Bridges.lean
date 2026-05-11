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

import EvmAsm.Evm64.SDiv.Compose.Base

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- SDIV-Post-shaped variant of `evmWordIs_eq_quadMem_named`: same dividend
    bridge but slot 3's offset is `signExtend12 evm_sdivDividendTopLimbOff`
    (definitionally equal to `signExtend12 24`). Matches the literal shape
    in `saveRaSignsAbsSignXorThenDivCallPost`'s unfolded form so callers
    can fold the four dividend-side memIs atoms without first unfolding
    `evm_sdivDividendTopLimbOff`. -/
theorem evmWordIs_eq_quadMem_sdivDividend (sp s0 s1 s2 s3 : Word) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ s3)) =
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  exact evmWordIs_eq_quadMem_named sp s0 s1 s2 s3

/-- SDIV-Post-shaped variant of `evmWordIs_eq_quadMem_sp32_named`: same
    divisor bridge but slot 3's offset is
    `signExtend12 evm_sdivDivisorTopLimbOff` (definitionally equal to
    `signExtend12 56`). Companion to `evmWordIs_eq_quadMem_sdivDividend`
    for the divisor slot. -/
theorem evmWordIs_eq_quadMem_sdivDivisor (sp s0 s1 s2 s3 : Word) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ s3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  unfold EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  exact evmWordIs_eq_quadMem_sp32_named sp s0 s1 s2 s3

/-- Mid-tree variant of `evmWordIs_eq_quadMem_sdivDividend`: threads a
    remainder `Q` so callers can fold four dividend sum-memIs atoms into
    a single `evmWordIs sp` atom even when they sit at the head of a
    longer sepConj chain (as in `saveRaSignsAbsSignXorThenDivCallPost`'s
    unfolded form). Parallel to `evmWordIs_sp_unfold_right` in
    `EvmAsm/Evm64/Stack.lean`. Slice 4 micro evm-asm-0zmyg. -/
theorem evmWordIs_eq_quadMem_sdivDividend_right
    (sp s0 s1 s2 s3 : Word) (Q : Assertion) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ s3) **
     Q) =
    ((evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)) ** Q) := by
  rw [← evmWordIs_eq_quadMem_sdivDividend sp s0 s1 s2 s3]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

/-- Mid-tree variant of `evmWordIs_eq_quadMem_sdivDivisor`. Same idea as
    `evmWordIs_eq_quadMem_sdivDividend_right` but for the divisor slot. -/
theorem evmWordIs_eq_quadMem_sdivDivisor_right
    (sp s0 s1 s2 s3 : Word) (Q : Assertion) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ s3) **
     Q) =
    ((evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)) ** Q) := by
  rw [← evmWordIs_eq_quadMem_sdivDivisor sp s0 s1 s2 s3]
  rw [sepConj_assoc', sepConj_assoc', sepConj_assoc']

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

end EvmAsm.Evm64.SDiv.Compose
