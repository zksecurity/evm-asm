/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPre

  Irreducible precondition for the SDIV save-ra/dividend-sign/divisor-sign
  prefix.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseCode

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- Precondition for the SDIV save-ra + dividend sign + divisor sign
    composition: standard entry frame with the dividend and divisor top
    limbs accessible in memory and both sign-register slots holding
    their pre-call scratch. Wrapped `@[irreducible]` so downstream proofs
    do not re-reduce the 7-atom sepConj at each use site. -/
@[irreducible]
def saveRaDividendSignThenDivisorSignPre
    (vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word) :
    Assertion :=
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
    ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
       dividendTop))) **
   ((.x9 ↦ᵣ sDivisorOld) **
    ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
      divisorTop))

theorem saveRaDividendSignThenDivisorSignPre_unfold
    {vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word} :
    saveRaDividendSignThenDivisorSignPre vRa vSavedOld sp sDividendOld
        dividendTop sDivisorOld divisorTop =
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
  delta saveRaDividendSignThenDivisorSignPre
  rfl

end EvmAsm.Evm64.SDiv.Compose
