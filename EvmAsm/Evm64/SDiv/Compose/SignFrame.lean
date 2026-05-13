/-
  EvmAsm.Evm64.SDiv.Compose.SignFrame

  Small named assertion for the SDIV wrapper-private sign frame that is carried
  across the unsigned DIV callable.
-/

import EvmAsm.Evm64.SDiv.Compose.Base

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64

/-- SDIV wrapper-private sign frame preserved across the unsigned DIV callable. -/
def sdivDivCallSignFrame (vRa resultSign divisorSign : Word) : Assertion :=
  (.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
  (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))

theorem sdivDivCallSignFrame_unfold
    {vRa resultSign divisorSign : Word} :
    sdivDivCallSignFrame vRa resultSign divisorSign =
      ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
       (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  rfl

end EvmAsm.Evm64.SDiv.Compose
