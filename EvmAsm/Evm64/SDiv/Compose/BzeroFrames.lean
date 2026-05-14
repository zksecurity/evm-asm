/-
  EvmAsm.Evm64.SDiv.Compose.BzeroFrames

  Named frames used after the SDIV zero-divisor unsigned-DIV callable
  returns.
-/

import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.SDiv.Compose.BaseOffsets
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Frame left around the result-sign-fix precondition after the SDIV prefix
    and zero-divisor unsigned-DIV callable have run. -/
@[irreducible]
def saveRaDivCallBzeroResultSignFixFrame
    (vRa sp base divisorSign : Word) (dividendAbsWord : EvmWord) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign) **
  (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))

theorem saveRaDivCallBzeroResultSignFixFrame_unfold
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign) **
       (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  delta saveRaDivCallBzeroResultSignFixFrame
  rfl

/-- Frame remaining after exposing `x18` for the saved-RA return. -/
@[irreducible]
def saveRaDivCallBzeroSavedRaRetFrame
    (sp base divisorSign : Word) (dividendAbsWord : EvmWord) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign)

theorem saveRaDivCallBzeroSavedRaRetFrame_unfold
    {sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign)) := by
  delta saveRaDivCallBzeroSavedRaRetFrame
  rfl

/-- Expose the saved return address atom from the bzero result-sign-fix
    frame, leaving the rest as an explicit return frame. -/
theorem saveRaDivCallBzeroResultSignFixFrame_to_savedRaRet
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
       saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
    saveRaDivCallBzeroSavedRaRetFrame_unfold]
  xperm

end EvmAsm.Evm64.SDiv.Compose
