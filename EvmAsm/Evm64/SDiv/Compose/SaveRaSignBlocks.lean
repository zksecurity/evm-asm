/-
  EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlocks

  SDIV wrapper specs for the saved-`ra` prologue and sign-bit probe blocks.
-/

import EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPost

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

theorem saveRa_spec_in_sdivCode
    (vRa vSavedOld : Word) (base : Word) :
    cpsTripleWithin 1 base (base + 4) (sdivCode base)
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld))
      ((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  have hmono :
      ∀ a i, (EvmAsm.Evm64.evm_sdiv_save_ra_block_code .x18 base) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_saveRa_sub (base := base) a i
      (by simpa [saveRaCode, saveRaOff,
        EvmAsm.Evm64.evm_sdiv_save_ra_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_save_ra_block_spec_within .x18
      vRa vSavedOld base (by decide))

theorem dividendSign_spec_in_sdivCode
    (sp sOld dividendTop : Word) (base : Word) :
    cpsTripleWithin 2 (base + dividendSignOff) ((base + dividendSignOff) + 8)
      (sdivCode base)
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x8
          EvmAsm.Evm64.evm_sdivDividendTopLimbOff
          (base + dividendSignOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_dividendSign_sub (base := base) a i
      (by simpa [dividendSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff sp sOld dividendTop
      (base + dividendSignOff) (by decide))

theorem saveRa_then_dividendSign_spec_in_sdivCode
    (vRa vSavedOld sp sOld dividendTop : Word) (base : Word) :
    cpsTripleWithin 3 base ((base + dividendSignOff) + 8) (sdivCode base)
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
       ((.x12 ↦ᵣ sp) **
        (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop))) := by
  have hSave :=
    cpsTripleWithin_frameR
      (((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sOld) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
          dividendTop)))
      (by pcFree)
      (saveRa_spec_in_sdivCode vRa vSavedOld base)
  have hSign :=
    cpsTripleWithin_frameL
      (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))))
      (by pcFree)
      (dividendSign_spec_in_sdivCode sp sOld dividendTop base)
  exact cpsTripleWithin_seq_same_cr hSave hSign

theorem divisorSign_spec_in_sdivCode
    (sp sOld divisorTop : Word) (base : Word) :
    cpsTripleWithin 2 (base + divisorSignOff) ((base + divisorSignOff) + 8)
      (sdivCode base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sOld) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop))
      ((.x12 ↦ᵣ sp) **
       (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
         divisorTop)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_sign_bit_block_code .x12 .x9
          EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
          (base + divisorSignOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_divisorSign_sub (base := base) a i
      (by simpa [divisorSignCode,
        EvmAsm.Evm64.evm_sdiv_sign_bit_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block_spec_within .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff sp sOld divisorTop
      (base + divisorSignOff) (by decide))

end EvmAsm.Evm64.SDiv.Compose
