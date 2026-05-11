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

end EvmAsm.Evm64.SDiv.Compose
