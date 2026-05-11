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

/-- Bridge lemma: four `↦ₘ`-memory atoms at `sp + signExtend12 (0/8/16/24)`
    fold into a single `evmWordIs sp` atom holding `EvmWord.fromLimbs` of the
    four limbs. Bite-sized helper for slice 4 (evm-asm-hvweh): the full
    pre-`divCall` composition needs to bridge memory-quad atoms produced by
    the absolute-value sequences to the `evmWordIs sp a` / `evmWordIs (sp+32) b`
    inputs of `evm_div_callable_spec_in_sdivCode`. This lemma covers the
    `sp` (dividend) slot; the `sp+32` (divisor) slot uses the analogous
    `evmWordIs_sp32` infrastructure.

    The `limbs` argument is left abstract so callers control the precise
    `Fin 4 → Word` representation (typically built via `match i with ...`
    matching the post-`abs` memory shape). -/
theorem evmWordIs_eq_quadMem (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs sp (EvmWord.fromLimbs limbs) := by
  have h0 : (sp + signExtend12 (0 : BitVec 12) : Word) = sp := by
    unfold signExtend12; bv_decide
  have h8 : (sp + signExtend12 (8 : BitVec 12) : Word) = sp + 8 := by
    unfold signExtend12; bv_decide
  have h16 : (sp + signExtend12 (16 : BitVec 12) : Word) = sp + 16 := by
    unfold signExtend12; bv_decide
  have h24 : (sp + signExtend12 (24 : BitVec 12) : Word) = sp + 24 := by
    unfold signExtend12; bv_decide
  rw [h0, h8, h16, h24]
  exact (evmWordIs_fromLimbs (addr := sp) limbs).symm

/-- Divisor-slot companion to `evmWordIs_eq_quadMem`: four `↦ₘ`-memory atoms
    at `sp + signExtend12 (32/40/48/56)` fold into a single
    `evmWordIs (sp + 32)` atom. Bite-sized helper for slice 4 (evm-asm-j8ity):
    the post-`abs` divisor limbs live at `sp + signExtend12 (32..56)` while
    `evm_div_callable_spec_in_sdivCode` consumes them as
    `evmWordIs (sp + 32) b`; this lemma bridges the two shapes. -/
theorem evmWordIs_eq_quadMem_sp32 (sp : Word) (limbs : Fin 4 → Word) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limbs 0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limbs 1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limbs 2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limbs 3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs limbs) := by
  have h32 : (sp + signExtend12 (32 : BitVec 12) : Word) = sp + 32 := by
    unfold signExtend12; bv_decide
  have h40 : (sp + signExtend12 (40 : BitVec 12) : Word) = (sp + 32) + 8 := by
    unfold signExtend12; bv_decide
  have h48 : (sp + signExtend12 (48 : BitVec 12) : Word) = (sp + 32) + 16 := by
    unfold signExtend12; bv_decide
  have h56 : (sp + signExtend12 (56 : BitVec 12) : Word) = (sp + 32) + 24 := by
    unfold signExtend12; bv_decide
  rw [h32, h40, h48, h56]
  exact (evmWordIs_fromLimbs (addr := sp + 32) limbs).symm

/-- Named-arguments specialization of `evmWordIs_eq_quadMem` (slice 4
    micro evm-asm-nregq). Folds four `↦ₘ` atoms holding explicitly-named
    limb values `s0..s3` into a single `evmWordIs sp` atom carrying a
    `Fin 4 → Word` lambda that returns each limb. Convenience wrapper used
    by the SDIV `divCall` framing step to bridge the post of
    `saveRa_signs_abs_signXor_then_divCall_spec_in_sdivCode` (where the
    four dividend-absolute-value sums live as plain memIs atoms) into the
    `evmWordIs sp a` input shape of `evm_div_callable_spec_in_sdivCode`. -/
theorem evmWordIs_eq_quadMem_named (sp s0 s1 s2 s3 : Word) :
    (((sp + signExtend12 (0 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ s3)) =
    evmWordIs sp (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  rw [← evmWordIs_eq_quadMem sp
    (fun i : Fin 4 => match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)]

/-- Named-arguments specialization of `evmWordIs_eq_quadMem_sp32`
    (slice 4 micro evm-asm-nregq). Divisor-slot companion to
    `evmWordIs_eq_quadMem_named`: folds four `↦ₘ` atoms at
    `sp + signExtend12 (32/40/48/56)` into `evmWordIs (sp + 32)` carrying
    a 4-case `Fin 4 → Word` lambda. -/
theorem evmWordIs_eq_quadMem_sp32_named (sp s0 s1 s2 s3 : Word) :
    (((sp + signExtend12 (32 : BitVec 12)) ↦ₘ s0) **
     ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ s1) **
     ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ s2) **
     ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ s3)) =
    evmWordIs (sp + 32) (EvmWord.fromLimbs fun i : Fin 4 =>
      match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3) := by
  rw [← evmWordIs_eq_quadMem_sp32 sp
    (fun i : Fin 4 => match i with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3)]

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

end EvmAsm.Evm64.SDiv.Compose
