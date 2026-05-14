/-
  EvmAsm.Evm64.SDiv.Compose.ResultSignFixPCFree

  PC-free instances for standalone SDIV result-sign-fix bundles.
-/

import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnPre

namespace EvmAsm.Evm64.SDiv.Compose

theorem resultSignFixPost_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPost sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPost_unfold]
  dsimp
  pcFree

instance pcFreeInst_resultSignFixPost
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree (resultSignFixPost sp sign limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPost_pcFree⟩

theorem resultSignFixPreOwnX10_pcFree
    {sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnX10
      sp sign valueOld carryOld limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnX10_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnX10
    (sp sign valueOld carryOld limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (resultSignFixPreOwnX10
        sp sign valueOld carryOld limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnX10_pcFree⟩

theorem resultSignFixPreOwnX10X7_pcFree
    {sp sign carryOld limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnX10X7
      sp sign carryOld limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnX10X7_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnX10X7
    (sp sign carryOld limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (resultSignFixPreOwnX10X7 sp sign carryOld limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnX10X7_pcFree⟩

theorem resultSignFixPreOwnScratch_pcFree
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3).pcFree := by
  rw [resultSignFixPreOwnScratch_unfold]
  pcFree

instance pcFreeInst_resultSignFixPreOwnScratch
    (sp sign limb0 limb1 limb2 limb3 : Word) :
    EvmAsm.Rv64.Assertion.PCFree (resultSignFixPreOwnScratch sp sign limb0 limb1 limb2 limb3) :=
  ⟨resultSignFixPreOwnScratch_pcFree⟩

end EvmAsm.Evm64.SDiv.Compose
