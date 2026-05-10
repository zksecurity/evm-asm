/-
  EvmAsm.Evm64.SDiv.Compose.Base

  Shared composition infrastructure for SDIV: `sdivCode` (the union of
  all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `sdivCode`, and shared length lemmas.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). Concrete
  definitions will be added once `evm_sdiv` is laid out (slice
  evm-asm-01uh) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Byte offset of the saved-`ra` prologue inside `evm_sdiv_wrapper`. -/
def saveRaOff : Nat := 0

/-- Byte offset of the dividend sign probe inside `evm_sdiv_wrapper`. -/
def dividendSignOff : Nat := 4

/-- Byte offset of the divisor sign probe inside `evm_sdiv_wrapper`. -/
def divisorSignOff : Nat := 12

/-- Byte offset of the in-place dividend absolute-value block. -/
def dividendAbsOff : Nat := 20

/-- Byte offset of the in-place divisor absolute-value block. -/
def divisorAbsOff : Nat := 104

/-- Byte offset of the sign-xor instruction selecting result negation. -/
def signXorOff : Nat := 188

/-- Byte offset of the near call into `evm_div_callable`. -/
def divCallOff : Nat := 192

/-- Byte offset of the in-place quotient sign-fixup block. -/
def resultSignFixOff : Nat := 196

/-- Byte offset of the saved-`ra` return instruction. -/
def savedRaRetOff : Nat := 280

/-- Byte offset at the end of the SDIV wrapper. The appended unsigned
    divider callable starts here. -/
def wrapperEndOff : Nat := 284

/-- Bundled byte offsets for the concrete SDIV wrapper layout. -/
theorem sdiv_wrapper_block_byte_offsets :
    saveRaOff = 0 ∧
    dividendSignOff = 4 ∧
    divisorSignOff = 12 ∧
    dividendAbsOff = 20 ∧
    divisorAbsOff = 104 ∧
    signXorOff = 188 ∧
    divCallOff = 192 ∧
    resultSignFixOff = 196 ∧
    savedRaRetOff = 280 ∧
    wrapperEndOff = 284 := by
  native_decide

/-- Successive fall-through byte offsets for the concrete SDIV wrapper. -/
theorem sdiv_wrapper_fallthrough_offsets :
    saveRaOff + 4 = dividendSignOff ∧
    dividendSignOff + 8 = divisorSignOff ∧
    divisorSignOff + 8 = dividendAbsOff ∧
    dividendAbsOff + 84 = divisorAbsOff ∧
    divisorAbsOff + 84 = signXorOff ∧
    signXorOff + 4 = divCallOff ∧
    divCallOff + 4 = resultSignFixOff ∧
    resultSignFixOff + 84 = savedRaRetOff ∧
    savedRaRetOff + 4 = wrapperEndOff := by
  native_decide

/-- Full SDIV code region handle: wrapper followed by `evm_div_callable`. -/
abbrev sdivCode (base : Word) : CodeReq :=
  CodeReq.ofProg base EvmAsm.Evm64.evm_sdiv

/-- Code handle for the saved-`ra` prologue block. -/
abbrev saveRaCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + saveRaOff) (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18)

/-- Code handle for the dividend sign-bit probe. -/
abbrev dividendSignCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + dividendSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff)

/-- Code handle for the divisor sign-bit probe. -/
abbrev divisorSignCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divisorSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff)

/-- Code handle for the in-place dividend absolute-value block. -/
abbrev dividendAbsCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + dividendAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24)

/-- Code handle for the in-place divisor absolute-value block. -/
abbrev divisorAbsCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divisorAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56)

/-- Code handle for the sign-xor instruction selecting result negation. -/
abbrev signXorCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + signXorOff) (EvmAsm.Rv64.XOR' .x8 .x8 .x9)

/-- Code handle for the near call into `evm_div_callable`. -/
abbrev divCallCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divCallOff)
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff)

/-- Code handle for the in-place quotient sign-fixup block. -/
abbrev resultSignFixCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + resultSignFixOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      32 40 48 56)

/-- Code handle for the saved-`ra` return instruction. -/
abbrev savedRaRetCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + savedRaRetOff)
    (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18)

/-- Code handle for the appended unsigned divider callable. -/
abbrev divCallableCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable

theorem sdivCode_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (sdivCode base) a = some i := by
  unfold saveRaCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_sdiv (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (sdivCode base) a = some i := by
  unfold dividendSignCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (sdivCode base) a = some i := by
  unfold divisorSignCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) 3
    (by simp [divisorSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCode base) a = some i := by
  unfold dividendAbsCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCode base) a = some i := by
  unfold divisorAbsCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCode base) a = some i := by
  unfold signXorCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCode base) a = some i := by
  unfold divCallCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCode base) a = some i := by
  unfold resultSignFixCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      32 40 48 56) 49
    (by simp [resultSignFixOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCode base) a = some i := by
  unfold savedRaRetCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCode base) a = some i → (sdivCode base) a = some i := by
  unfold divCallableCode sdivCode
  exact CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv EvmAsm.Evm64.evm_div_callable 71
    (by simp [wrapperEndOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_length]; norm_num)

theorem sdivCode_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (signXorCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (divCallCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (sdivCode base) a = some i) ∧
    (∀ a i, (divCallableCode base) a = some i → (sdivCode base) a = some i) := by
  exact ⟨sdivCode_saveRa_sub, sdivCode_dividendSign_sub,
    sdivCode_divisorSign_sub, sdivCode_dividendAbs_sub,
    sdivCode_divisorAbs_sub, sdivCode_signXor_sub, sdivCode_divCall_sub,
    sdivCode_resultSignFix_sub, sdivCode_savedRaRet_sub,
    sdivCode_divCallable_sub⟩

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

theorem saveRa_dividendSign_then_divisorSign_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop : Word)
    (base : Word) :
    cpsTripleWithin 5 base ((base + divisorSignOff) + 8) (sdivCode base)
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop)))
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
        ((.x8 ↦ᵣ (dividendTop >>> (63 : BitVec 6).toNat)) **
         ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff) ↦ₘ
           dividendTop))) **
       ((.x12 ↦ᵣ sp) **
        (.x9 ↦ᵣ (divisorTop >>> (63 : BitVec 6).toNat)) **
        ((sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) ↦ₘ
          divisorTop))) := by
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

theorem dividendAbs_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    let mem0 := sp + signExtend12 (0 : BitVec 12)
    let mem1 := sp + signExtend12 (8 : BitVec 12)
    let mem2 := sp + signExtend12 (16 : BitVec 12)
    let mem3 := sp + signExtend12 (24 : BitVec 12)
    let mask := (0 : Word) - sign
    let xored0 := limb0 ^^^ mask
    let sum0 := xored0 + sign
    let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
    let xored1 := limb1 ^^^ mask
    let sum1 := xored1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let xored2 := limb2 ^^^ mask
    let sum2 := xored2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let xored3 := limb3 ^^^ mask
    let sum3 := xored3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCode base)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
       (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ limb3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
       (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)) := by
  intro mem0 mem1 mem2 mem3 mask xored0 sum0 carry0 xored1 sum1 carry1
    xored2 sum2 carry2 xored3 sum3 carry3
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + dividendAbsOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_dividendAbs_sub (base := base) a i
      (by simpa [dividendAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide))

theorem saveRa_signs_then_dividendAbs_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    let sign := dividendTop >>> (63 : BitVec 6).toNat
    let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
    let mem0 := sp + signExtend12 (0 : BitVec 12)
    let mem1 := sp + signExtend12 (8 : BitVec 12)
    let mem2 := sp + signExtend12 (16 : BitVec 12)
    let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
    let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
    let mask := (0 : Word) - sign
    let xored0 := limb0 ^^^ mask
    let sum0 := xored0 + sign
    let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
    let xored1 := limb1 ^^^ mask
    let sum1 := xored1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let xored2 := limb2 ^^^ mask
    let sum2 := xored2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let xored3 := dividendTop ^^^ mask
    let sum3 := xored3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCode base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
         ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
        ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
       (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
         (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
        ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2))))
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
        ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
       ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
        (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
        (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
        (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))) := by
  intro sign divisorSign mem0 mem1 mem2 mem3 divisorMem3 mask xored0 sum0
    carry0 xored1 sum1 carry1 xored2 sum2 carry2 xored3 sum3 carry3
  let extra : Assertion :=
    (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
      (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
     ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
  let pre : Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
       ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
      ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let mid : Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
       ((.x8 ↦ᵣ sign) ** (mem3 ↦ₘ dividendTop))) **
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     extra)
  let absPre : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
      (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
      (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ dividendTop)))
  let post : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
      (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
      (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
      (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)))
  have hPrefix : cpsTripleWithin 5 base (base + dividendAbsOff)
      (sdivCode base) pre mid := by
    dsimp [pre, mid, extra, mem3, divisorMem3, sign, divisorSign]
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc] using
      (cpsTripleWithin_frameR
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))
        (by pcFree)
        (saveRa_dividendSign_then_divisorSign_spec_in_sdivCode
          vRa vSavedOld sp sDividendOld dividendTop sDivisorOld divisorTop
          base))
  have hAbs : cpsTripleWithin 21 (base + dividendAbsOff)
      ((base + dividendAbsOff) + 84) (sdivCode base) absPre post := by
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        (dividendAbs_spec_in_sdivCode
          sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
          base)
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

theorem divisorAbs_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    let mem0 := sp + signExtend12 (32 : BitVec 12)
    let mem1 := sp + signExtend12 (40 : BitVec 12)
    let mem2 := sp + signExtend12 (48 : BitVec 12)
    let mem3 := sp + signExtend12 (56 : BitVec 12)
    let mask := (0 : Word) - sign
    let xored0 := limb0 ^^^ mask
    let sum0 := xored0 + sign
    let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
    let xored1 := limb1 ^^^ mask
    let sum1 := xored1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let xored2 := limb2 ^^^ mask
    let sum2 := xored2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let xored3 := limb3 ^^^ mask
    let sum3 := xored3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (sdivCode base)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
       (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ limb3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
       (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)) := by
  intro mem0 mem1 mem2 mem3 mask xored0 sum0 carry0 xored1 sum1 carry1
    xored2 sum2 carry2 xored3 sum3 carry3
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x9 .x10 .x7 .x11 32 40 48 56
          (base + divisorAbsOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_divisorAbs_sub (base := base) a i
      (by simpa [divisorAbsCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide))

theorem saveRa_signs_abs_then_divisorAbs_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (base : Word) :
    let dividendSign := dividendTop >>> (63 : BitVec 6).toNat
    let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
    let dividendMem0 := sp + signExtend12 (0 : BitVec 12)
    let dividendMem1 := sp + signExtend12 (8 : BitVec 12)
    let dividendMem2 := sp + signExtend12 (16 : BitVec 12)
    let dividendMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
    let divisorMem0 := sp + signExtend12 (32 : BitVec 12)
    let divisorMem1 := sp + signExtend12 (40 : BitVec 12)
    let divisorMem2 := sp + signExtend12 (48 : BitVec 12)
    let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
    let dividendMask := (0 : Word) - dividendSign
    let dividendXored0 := dividendLimb0 ^^^ dividendMask
    let dividendSum0 := dividendXored0 + dividendSign
    let dividendCarry0 := if BitVec.ult dividendSum0 dividendSign then (1 : Word) else 0
    let dividendXored1 := dividendLimb1 ^^^ dividendMask
    let dividendSum1 := dividendXored1 + dividendCarry0
    let dividendCarry1 := if BitVec.ult dividendSum1 dividendCarry0 then (1 : Word) else 0
    let dividendXored2 := dividendLimb2 ^^^ dividendMask
    let dividendSum2 := dividendXored2 + dividendCarry1
    let dividendCarry2 := if BitVec.ult dividendSum2 dividendCarry1 then (1 : Word) else 0
    let dividendXored3 := dividendTop ^^^ dividendMask
    let dividendSum3 := dividendXored3 + dividendCarry2
    let divisorMask := (0 : Word) - divisorSign
    let divisorXored0 := divisorLimb0 ^^^ divisorMask
    let divisorSum0 := divisorXored0 + divisorSign
    let divisorCarry0 := if BitVec.ult divisorSum0 divisorSign then (1 : Word) else 0
    let divisorXored1 := divisorLimb1 ^^^ divisorMask
    let divisorSum1 := divisorXored1 + divisorCarry0
    let divisorCarry1 := if BitVec.ult divisorSum1 divisorCarry0 then (1 : Word) else 0
    let divisorXored2 := divisorLimb2 ^^^ divisorMask
    let divisorSum2 := divisorXored2 + divisorCarry1
    let divisorCarry2 := if BitVec.ult divisorSum2 divisorCarry1 then (1 : Word) else 0
    let divisorXored3 := divisorTop ^^^ divisorMask
    let divisorSum3 := divisorXored3 + divisorCarry2
    let divisorCarry3 := if BitVec.ult divisorSum3 divisorCarry2 then (1 : Word) else 0
    cpsTripleWithin 47 base ((base + divisorAbsOff) + 84) (sdivCode base)
      ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
          ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
           (dividendMem3 ↦ₘ dividendTop))) **
         ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
          (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
         ((dividendMem0 ↦ₘ dividendLimb0) **
          (dividendMem1 ↦ₘ dividendLimb1) **
          (dividendMem2 ↦ₘ dividendLimb2)))) **
       ((divisorMem0 ↦ₘ divisorLimb0) **
        (divisorMem1 ↦ₘ divisorLimb1) **
        (divisorMem2 ↦ₘ divisorLimb2)))
      ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
        ((.x8 ↦ᵣ dividendSign) **
         (dividendMem0 ↦ₘ dividendSum0) **
         (dividendMem1 ↦ₘ dividendSum1) **
         (dividendMem2 ↦ₘ dividendSum2) **
         (dividendMem3 ↦ₘ dividendSum3))) **
       ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
        (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
        (.x11 ↦ᵣ divisorCarry3) **
        (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
        (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3))) := by
  intro dividendSign divisorSign dividendMem0 dividendMem1 dividendMem2
    dividendMem3 divisorMem0 divisorMem1 divisorMem2 divisorMem3
    dividendMask dividendXored0 dividendSum0 dividendCarry0 dividendXored1
    dividendSum1 dividendCarry1 dividendXored2 dividendSum2 dividendCarry2
    dividendXored3 dividendSum3 divisorMask divisorXored0
    divisorSum0 divisorCarry0 divisorXored1 divisorSum1 divisorCarry1
    divisorXored2 divisorSum2 divisorCarry2 divisorXored3 divisorSum3
    divisorCarry3
  let dividendCarry3 := if BitVec.ult dividendSum3 dividendCarry2 then (1 : Word) else 0
  let divisorLower : Assertion :=
    ((divisorMem0 ↦ₘ divisorLimb0) ** (divisorMem1 ↦ₘ divisorLimb1) **
     (divisorMem2 ↦ₘ divisorLimb2))
  let pre : Assertion :=
    ((((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) **
         (dividendMem3 ↦ₘ dividendTop))) **
       ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
      (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ dividendMaskOld) **
        (.x7 ↦ᵣ dividendValueOld) ** (.x11 ↦ᵣ dividendCarryOld)) **
       ((dividendMem0 ↦ₘ dividendLimb0) **
        (dividendMem1 ↦ₘ dividendLimb1) **
        (dividendMem2 ↦ₘ dividendLimb2)))) **
     divisorLower)
  let mid : Assertion :=
    (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
       ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ dividendSign) **
       (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
       (.x11 ↦ᵣ dividendCarry3) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     divisorLower)
  let absPre : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ dividendMask) ** (.x7 ↦ᵣ dividendSum3) **
      (.x11 ↦ᵣ dividendCarry3) **
      (divisorMem0 ↦ₘ divisorLimb0) **
      (divisorMem1 ↦ₘ divisorLimb1) **
      (divisorMem2 ↦ₘ divisorLimb2) **
      (divisorMem3 ↦ₘ divisorTop)))
  let post : Assertion :=
    ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
      ((.x8 ↦ᵣ dividendSign) **
       (dividendMem0 ↦ₘ dividendSum0) **
       (dividendMem1 ↦ₘ dividendSum1) **
       (dividendMem2 ↦ₘ dividendSum2) **
       (dividendMem3 ↦ₘ dividendSum3))) **
     ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ divisorSign) **
      (.x10 ↦ᵣ divisorMask) ** (.x7 ↦ᵣ divisorSum3) **
      (.x11 ↦ᵣ divisorCarry3) **
      (divisorMem0 ↦ₘ divisorSum0) ** (divisorMem1 ↦ₘ divisorSum1) **
      (divisorMem2 ↦ₘ divisorSum2) ** (divisorMem3 ↦ₘ divisorSum3)))
  have hPrefix : cpsTripleWithin 26 base (base + divisorAbsOff)
      (sdivCode base) pre mid := by
    dsimp [pre, mid, divisorLower, dividendSign, divisorSign, dividendMem0,
      dividendMem1, dividendMem2, dividendMem3, divisorMem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, dividendMask, dividendXored0,
      dividendSum0, dividendCarry0, dividendXored1, dividendSum1,
      dividendCarry1, dividendXored2, dividendSum2, dividendCarry2,
      dividendXored3, dividendSum3, dividendCarry3]
    simpa [dividendAbsOff, divisorAbsOff, BitVec.add_assoc] using
      (cpsTripleWithin_frameR
        ((divisorMem0 ↦ₘ divisorLimb0) **
         (divisorMem1 ↦ₘ divisorLimb1) **
         (divisorMem2 ↦ₘ divisorLimb2))
        (by pcFree)
        (saveRa_signs_then_dividendAbs_spec_in_sdivCode
          vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
          dividendMaskOld dividendValueOld dividendCarryOld
          dividendLimb0 dividendLimb1 dividendLimb2 dividendTop base))
  have hAbs : cpsTripleWithin 21 (base + divisorAbsOff)
      ((base + divisorAbsOff) + 84) (sdivCode base) absPre post := by
    simpa [absPre, post, divisorMem0, divisorMem1, divisorMem2, divisorMem3,
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff, divisorMask, divisorXored0,
      divisorSum0, divisorCarry0, divisorXored1, divisorSum1, divisorCarry1,
      divisorXored2, divisorSum2, divisorCarry2, divisorXored3, divisorSum3,
      divisorCarry3] using
      cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
          ((.x8 ↦ᵣ dividendSign) **
           (dividendMem0 ↦ₘ dividendSum0) **
           (dividendMem1 ↦ₘ dividendSum1) **
           (dividendMem2 ↦ₘ dividendSum2) **
           (dividendMem3 ↦ₘ dividendSum3))))
        (by pcFree)
        (divisorAbs_spec_in_sdivCode
          sp divisorSign dividendMask dividendSum3 dividendCarry3
          divisorLimb0 divisorLimb1 divisorLimb2 divisorTop base)
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, divisorLower] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

theorem divCall_spec_in_sdivCode
    (vOld : Word) (base : Word) :
    cpsTripleWithin 1 (base + divCallOff)
        ((base + divCallOff) + signExtend21 EvmAsm.Evm64.evm_sdivCallOff)
      (sdivCode base)
      (.x1 ↦ᵣ vOld)
      (.x1 ↦ᵣ ((base + divCallOff) + 4)) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_div_call_block_code
          EvmAsm.Evm64.evm_sdivCallOff (base + divCallOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_divCall_sub (base := base) a i
      (by simpa [divCallCode,
        EvmAsm.Evm64.evm_sdiv_div_call_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_div_call_block_spec_within
      EvmAsm.Evm64.evm_sdivCallOff vOld (base + divCallOff))

theorem resultSignFix_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    let mem0 := sp + signExtend12 (32 : BitVec 12)
    let mem1 := sp + signExtend12 (40 : BitVec 12)
    let mem2 := sp + signExtend12 (48 : BitVec 12)
    let mem3 := sp + signExtend12 (56 : BitVec 12)
    let mask := (0 : Word) - sign
    let xored0 := limb0 ^^^ mask
    let sum0 := xored0 + sign
    let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
    let xored1 := limb1 ^^^ mask
    let sum1 := xored1 + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let xored2 := limb2 ^^^ mask
    let sum2 := xored2 + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let xored3 := limb3 ^^^ mask
    let sum3 := xored3 + carry2
    let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       (mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) **
       (mem2 ↦ₘ limb2) ** (mem3 ↦ₘ limb3))
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
       (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3)) := by
  intro mem0 mem1 mem2 mem3 mask xored0 sum0 carry0 xored1 sum1 carry1
    xored2 sum2 carry2 xored3 sum3 carry3
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 32 40 48 56
          (base + resultSignFixOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide))

theorem signXor_spec_in_sdivCode
    (signDividend signDivisor : Word) (base : Word) :
    cpsTripleWithin 1 (base + signXorOff) ((base + signXorOff) + 4)
      (sdivCode base)
      ((.x8 ↦ᵣ signDividend) ** (.x9 ↦ᵣ signDivisor))
      ((.x8 ↦ᵣ (signDividend ^^^ signDivisor)) ** (.x9 ↦ᵣ signDivisor)) := by
  have hmono :
      ∀ a i, (CodeReq.singleton (base + signXorOff) (.XOR .x8 .x8 .x9)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_signXor_sub (base := base) a i
      (by
        rw [signXorCode, EvmAsm.Rv64.XOR', EvmAsm.Rv64.single,
          CodeReq.ofProg_singleton]
        exact h)
  exact cpsTripleWithin_extend_code hmono
    (xor_spec_gen_rd_eq_rs1_within .x8 .x9 signDividend signDivisor
      (base + signXorOff) (by decide))

theorem savedRaRet_spec_in_sdivCode
    (vSavedRa : Word) (base : Word) :
    cpsTripleWithin 1 (base + savedRaRetOff)
        ((vSavedRa + signExtend12 (0 : BitVec 12)) &&& ~~~1)
      (sdivCode base)
      (.x18 ↦ᵣ vSavedRa)
      (.x18 ↦ᵣ vSavedRa) := by
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_code .x18
          (base + savedRaRetOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_savedRaRet_sub (base := base) a i
      (by simpa [savedRaRetCode,
        EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_code] using h)
  exact cpsTripleWithin_extend_code hmono
    (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block_spec_within .x18
      vSavedRa (base + savedRaRetOff))

end EvmAsm.Evm64.SDiv.Compose
