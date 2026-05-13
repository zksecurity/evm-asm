/-
  EvmAsm.Evm64.SDiv.Compose.BaseSignSequence

  SDIV wrapper composition for the saved-`ra` prologue followed by the
  dividend and divisor sign-bit probes.
-/

import EvmAsm.Evm64.SDiv.Compose.SaveRaSignsPre

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

/-- Postcondition for the same composition: `ra` saved to the spill
    slot (x18 ← vRa + 0), `x8` and `x9` hold the dividend/divisor sign
    bits (top-limb >>> 63), and the top-limb memory cells are
    unchanged. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaDividendSignThenDivisorSignPost
    (vRa sp dividendTop divisorTop : Word) : Assertion :=
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
    ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
     ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
       dividendTop))) **
   ((.x12 ↦ᵣ sp) **
    (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
    ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
      divisorTop))

theorem saveRaDividendSignThenDivisorSignPost_unfold
    {vRa sp dividendTop divisorTop : Word} :
    saveRaDividendSignThenDivisorSignPost vRa sp dividendTop divisorTop =
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
        ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
         ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       ((.x12 ↦ᵣ sp) **
        (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
  delta saveRaDividendSignThenDivisorSignPost
  rfl

theorem saveRa_dividendSign_then_divisorSign_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    cpsTripleWithin 5 base ((base + divisorSignOff) + 8) (sdivCode base)
      (saveRaDividendSignThenDivisorSignPre vRa vSavedOld sp sDividendOld
        dividendTop sDivisorOld divisorTop)
      (saveRaDividendSignThenDivisorSignPost vRa sp dividendTop divisorTop) := by
  rw [saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold]
  let pre : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
      ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let mid : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x12 ↦ᵣ sp) **
       (.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x9 ↦ᵣ sDivisorOld) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let midDivisor : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sDivisorOld) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  let post : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
       ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
         dividendTop))) **
     ((.x12 ↦ᵣ sp) **
      (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
      ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
        divisorTop)))
  have hPrefix : cpsTripleWithin 3 base (base + divisorSignOff)
      (sdivCode base) pre mid := by
    dsimp [pre, mid]
    simpa [dividendSignOff, divisorSignOff, BitVec.add_assoc] using
      (cpsTripleWithin_frameR
        ((.x9 ↦ᵣ sDivisorOld) **
         ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))
        (by pcFree)
        (saveRa_then_dividendSign_spec_in_sdivCode
          vRa vSavedOld sp sDividendOld dividendTop base))
  have hDivisor : cpsTripleWithin 2 (base + divisorSignOff)
      ((base + divisorSignOff) + 8) (sdivCode base) midDivisor post := by
    dsimp [midDivisor, post]
    exact
      cpsTripleWithin_frameL
        (((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
         ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
          ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
            dividendTop)))
        (by pcFree)
        (divisorSign_spec_in_sdivCode sp sDivisorOld divisorTop base)
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, midDivisor] at hp ⊢
      xperm_hyp hp) hPrefix hDivisor
  simpa [pre, post] using hSeq

end EvmAsm.Evm64.SDiv.Compose
