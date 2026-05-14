/-
  EvmAsm.Evm64.SDiv.Compose.DivCallAbsComponents

  Shared signed-absolute-value component abbreviations for SDIV div-call
  handoff proofs.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix

namespace EvmAsm.Evm64.SDiv.Compose

abbrev sdivAbsSign (top : Word) : Word :=
  top >>> (63 : BitVec 6).toNat

abbrev sdivAbsMask (top : Word) : Word :=
  (0 : Word) - sdivAbsSign top

abbrev sdivAbsSum0 (limb0 top : Word) : Word :=
  (limb0 ^^^ sdivAbsMask top) + sdivAbsSign top

abbrev sdivAbsCarry0 (limb0 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum0 limb0 top) (sdivAbsSign top) then (1 : Word) else 0

abbrev sdivAbsSum1 (limb0 limb1 top : Word) : Word :=
  (limb1 ^^^ sdivAbsMask top) + sdivAbsCarry0 limb0 top

abbrev sdivAbsCarry1 (limb0 limb1 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum1 limb0 limb1 top) (sdivAbsCarry0 limb0 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum2 (limb0 limb1 limb2 top : Word) : Word :=
  (limb2 ^^^ sdivAbsMask top) + sdivAbsCarry1 limb0 limb1 top

abbrev sdivAbsCarry2 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum2 limb0 limb1 limb2 top)
      (sdivAbsCarry1 limb0 limb1 top) then
    (1 : Word)
  else
    0

abbrev sdivAbsSum3 (limb0 limb1 limb2 top : Word) : Word :=
  (top ^^^ sdivAbsMask top) + sdivAbsCarry2 limb0 limb1 limb2 top

abbrev sdivAbsCarry3 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (sdivAbsSum3 limb0 limb1 limb2 top)
      (sdivAbsCarry2 limb0 limb1 limb2 top) then
    (1 : Word)
  else
    0

theorem sdivAbsDividendWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem sdivAbsDivisorWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    sdivAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => sdivAbsSum0 limb0 top
        | 1 => sdivAbsSum1 limb0 limb1 top
        | 2 => sdivAbsSum2 limb0 limb1 limb2 top
        | 3 => sdivAbsSum3 limb0 limb1 limb2 top := by
  rfl

abbrev saveRaDivCallSignFrame
    (vRa resultSign divisorSign : Word) : EvmAsm.Rv64.Assertion :=
  ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
    (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))

abbrev sdivDivCallResultSign (dividendTop divisorTop : Word) : Word :=
  sdivAbsSign dividendTop ^^^ sdivAbsSign divisorTop

end EvmAsm.Evm64.SDiv.Compose
