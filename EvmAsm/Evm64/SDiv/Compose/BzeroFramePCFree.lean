/-
  EvmAsm.Evm64.SDiv.Compose.BzeroFramePCFree

  PC-free instances for zero-divisor SDIV result-sign-fix/return frames.
-/

import EvmAsm.Evm64.SDiv.Compose.BzeroFrames
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixPCFree

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

theorem saveRaDivCallBzeroResultSignFixFrame_pcFree
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    (saveRaDivCallBzeroResultSignFixFrame
      vRa sp base divisorSign dividendAbsWord).pcFree := by
  rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallBzeroResultSignFixFrame
    (vRa sp base divisorSign : Word) (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord) :=
  ⟨saveRaDivCallBzeroResultSignFixFrame_pcFree⟩

theorem saveRaDivCallBzeroSavedRaRetFrame_pcFree
    {sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    (saveRaDivCallBzeroSavedRaRetFrame
      sp base divisorSign dividendAbsWord).pcFree := by
  rw [saveRaDivCallBzeroSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_saveRaDivCallBzeroSavedRaRetFrame
    (sp base divisorSign : Word) (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (saveRaDivCallBzeroSavedRaRetFrame
        sp base divisorSign dividendAbsWord) :=
  ⟨saveRaDivCallBzeroSavedRaRetFrame_pcFree⟩

theorem resultSignFixPost_bzeroResultSignFixFrame_pcFree
    {vRa sp base divisorSign sign limb0 limb1 limb2 limb3 : Word}
    {dividendAbsWord : EvmWord} :
    (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
      saveRaDivCallBzeroResultSignFixFrame
        vRa sp base divisorSign dividendAbsWord).pcFree := by
  pcFree

instance pcFreeInst_resultSignFixPost_bzeroResultSignFixFrame
    (vRa sp base divisorSign sign limb0 limb1 limb2 limb3 : Word)
    (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
        saveRaDivCallBzeroResultSignFixFrame
          vRa sp base divisorSign dividendAbsWord) :=
  ⟨resultSignFixPost_bzeroResultSignFixFrame_pcFree⟩

theorem resultSignFixPost_savedRaRetFrame_pcFree
    {sp base divisorSign sign limb0 limb1 limb2 limb3 : Word}
    {dividendAbsWord : EvmWord} :
    (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
      saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord).pcFree := by
  pcFree

instance pcFreeInst_resultSignFixPost_savedRaRetFrame
    (sp base divisorSign sign limb0 limb1 limb2 limb3 : Word)
    (dividendAbsWord : EvmWord) :
    Assertion.PCFree
      (resultSignFixPost (sp + 32) sign limb0 limb1 limb2 limb3 **
        saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord) :=
  ⟨resultSignFixPost_savedRaRetFrame_pcFree⟩

end EvmAsm.Evm64.SDiv.Compose
