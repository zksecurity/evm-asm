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
      0 8 16 24)

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
      0 8 16 24) 49
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

/-- Precondition for the SDIV dividend-abs (conditional 2's-complement
    negation) block. Wraps the register/memory entry shape as an
    `@[irreducible]` def so downstream proofs do not re-unfold the
    sepConj atoms at each use site. -/
@[irreducible]
def dividendAbsPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem dividendAbsPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta dividendAbsPre
  rfl

/-- Postcondition for the SDIV dividend-abs block: each limb is XORed
    with `mask = -sign` and the ripple-carry add of `sign` is propagated
    through the four limbs. Wrapped `@[irreducible]` to hide the let
    chain from downstream proofs. -/
@[irreducible]
def dividendAbsPost (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)

theorem dividendAbsPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    dividendAbsPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)) := by
  delta dividendAbsPost
  rfl

theorem dividendAbs_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    cpsTripleWithin 21 (base + dividendAbsOff) ((base + dividendAbsOff) + 84)
      (sdivCode base)
      (dividendAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (dividendAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [dividendAbsPre_unfold, dividendAbsPost_unfold]
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
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + dividendAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact cpsTripleWithin_extend_code hmono hSpec

/-- Precondition for the SDIV save-ra + dividend/divisor signs +
    dividendAbs prefix. Takes only the bare wrapper inputs; the
    `sp`-relative dividend/divisor memory addresses are computed
    internally so the let-chain that previously lived in the theorem
    signature stays hidden inside this `@[irreducible]` def. -/
@[irreducible]
def saveRaSignsThenDividendAbsPre
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word) : Assertion :=
  let mem0 := sp + signExtend12 (0 : BitVec 12)
  let mem1 := sp + signExtend12 (8 : BitVec 12)
  let mem2 := sp + signExtend12 (16 : BitVec 12)
  let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
     ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
    ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
   (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
     (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
    ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))

theorem saveRaSignsThenDividendAbsPre_unfold
    {vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld
      limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
        maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop =
      (let mem0 := sp + signExtend12 (0 : BitVec 12)
       let mem1 := sp + signExtend12 (8 : BitVec 12)
       let mem2 := sp + signExtend12 (16 : BitVec 12)
       let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       ((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
          ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (mem3 ↦ₘ dividendTop))) **
         ((.x9 ↦ᵣ sDivisorOld) ** (divisorMem3 ↦ₘ divisorTop))) **
        (((.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ maskOld) **
          (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld)) **
         ((mem0 ↦ₘ limb0) ** (mem1 ↦ₘ limb1) ** (mem2 ↦ₘ limb2)))) := by
  delta saveRaSignsThenDividendAbsPre
  rfl

/-- Postcondition for the SDIV save-ra/signs/dividendAbs prefix. Takes
    only the bare wrapper inputs; the sign/mask/sum/carry let-chain
    (~12 derived values) is computed internally so the theorem signature
    stays flat. Wrapped `@[irreducible]`. -/
@[irreducible]
def saveRaSignsThenDividendAbsPost
    (vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word) : Assertion :=
  let sign := dividendTop >>> (63 : BitVec 6).toNat
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  let mem0 := sp + signExtend12 (0 : BitVec 12)
  let mem1 := sp + signExtend12 (8 : BitVec 12)
  let mem2 := sp + signExtend12 (16 : BitVec 12)
  let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
  let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (dividendTop ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
    ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
   ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
    (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
    (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
    (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))

theorem saveRaSignsThenDividendAbsPost_unfold
    {vRa sp divisorTop limb0 limb1 limb2 dividendTop : Word} :
    saveRaSignsThenDividendAbsPost vRa sp divisorTop limb0 limb1 limb2 dividendTop =
      (let sign := dividendTop >>> (63 : BitVec 6).toNat
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       let mem0 := sp + signExtend12 (0 : BitVec 12)
       let mem1 := sp + signExtend12 (8 : BitVec 12)
       let mem2 := sp + signExtend12 (16 : BitVec 12)
       let mem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDividendTopLimbOff
       let divisorMem3 := sp + signExtend12 EvmAsm.Evm64.evm_sdivDivisorTopLimbOff
       let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (dividendTop ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
         ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))) **
        ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
         (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
         (mem0 ↦ₘ sum0) ** (mem1 ↦ₘ sum1) **
         (mem2 ↦ₘ sum2) ** (mem3 ↦ₘ sum3))) := by
  delta saveRaSignsThenDividendAbsPost
  rfl

theorem saveRa_signs_then_dividendAbs_spec_in_sdivCode
    (vRa vSavedOld sp sDividendOld sDivisorOld divisorTop
      maskOld valueOld carryOld limb0 limb1 limb2 dividendTop : Word)
    (base : Word) :
    cpsTripleWithin 26 base ((base + dividendAbsOff) + 84) (sdivCode base)
      (saveRaSignsThenDividendAbsPre vRa vSavedOld sp sDividendOld sDivisorOld
        divisorTop maskOld valueOld carryOld
        limb0 limb1 limb2 dividendTop)
      (saveRaSignsThenDividendAbsPost vRa sp divisorTop
        limb0 limb1 limb2 dividendTop) := by
  rw [saveRaSignsThenDividendAbsPre_unfold,
      saveRaSignsThenDividendAbsPost_unfold]
  -- Re-introduce the let-chain locally so the existing composition proof
  -- (which references these derived names) keeps working unchanged.
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
    simpa [divisorSignOff, dividendAbsOff, BitVec.add_assoc,
      saveRaDividendSignThenDivisorSignPre_unfold,
      saveRaDividendSignThenDivisorSignPost_unfold] using
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
    have hSpec := dividendAbs_spec_in_sdivCode
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 dividendTop
      base
    rw [dividendAbsPre_unfold, dividendAbsPost_unfold] at hSpec
    simpa [absPre, post, mem0, mem1, mem2, mem3,
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff, mask, xored0, sum0,
      carry0, xored1, sum1, carry1, xored2, sum2, carry2, xored3, sum3,
      carry3] using
      cpsTripleWithin_frameL
        ((((.x1 ↦ᵣ vRa) **
          (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) **
          ((.x9 ↦ᵣ divisorSign) ** (divisorMem3 ↦ₘ divisorTop))))
        (by pcFree)
        hSpec
  have hSeq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      dsimp [mid, absPre, extra] at hp ⊢
      xperm_hyp hp) hPrefix hAbs
  simpa [pre, post] using hSeq

/-- Precondition for the SDIV divisor-abs (conditional 2's-complement
    negation) block. Mirrors `dividendAbsPre` but with the sign in `x9`
    and limb memory cells at the `+32 … +56` divisor slots. Wrapped
    `@[irreducible]` so downstream proofs do not re-unfold the sepConj
    atoms at each use site. -/
@[irreducible]
def divisorAbsPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)

theorem divisorAbsPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ limb0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ limb1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ limb2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ limb3)) := by
  delta divisorAbsPre
  rfl

/-- Postcondition for the SDIV divisor-abs block: mirrors
    `dividendAbsPost` but with the sign register `x9` and the divisor
    memory slots `+32 … +56`. Wrapped `@[irreducible]` to hide the let
    chain from downstream proofs. -/
@[irreducible]
def divisorAbsPost (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
  ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
  ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
  ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ sum3)

theorem divisorAbsPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    divisorAbsPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + signExtend12 (32 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (40 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (48 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (56 : BitVec 12)) ↦ₘ sum3)) := by
  delta divisorAbsPost
  rfl

theorem divisorAbs_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    cpsTripleWithin 21 (base + divisorAbsOff) ((base + divisorAbsOff) + 84)
      (sdivCode base)
      (divisorAbsPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (divisorAbsPost sp sign limb0 limb1 limb2 limb3) := by
  rw [divisorAbsPre_unfold, divisorAbsPost_unfold]
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
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x9 .x10 .x7 .x11 32 40 48 56
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + divisorAbsOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact cpsTripleWithin_extend_code hmono hSpec


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

/-- Precondition for the SDIV result sign-fixup (conditional 2's-complement
    negation) block. The unsigned DIV callable returns with `x12` advanced
    to the quotient cell, so this block operates on offsets `0…24` from the
    live stack pointer. Wrapped `@[irreducible]` so downstream proofs do not
    re-unfold the sepConj atoms at each use site. -/
@[irreducible]
def resultSignFixPre (sp sign maskOld valueOld carryOld
    limb0 limb1 limb2 limb3 : Word) : Assertion :=
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)

theorem resultSignFixPre_unfold
    {sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3 =
      ((.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ maskOld) ** (.x7 ↦ᵣ valueOld) ** (.x11 ↦ᵣ carryOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ limb0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ limb1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ limb2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ limb3)) := by
  delta resultSignFixPre
  rfl

/-- Postcondition for the SDIV result sign-fixup block: mirrors
    `divisorAbsPost` but with the sign register `x8`. Wrapped
    `@[irreducible]` to hide the let chain from downstream proofs. -/
@[irreducible]
def resultSignFixPost (sp sign limb0 limb1 limb2 limb3 : Word) : Assertion :=
  let mask := (0 : Word) - sign
  let sum0 := (limb0 ^^^ mask) + sign
  let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
  (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
  (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
  ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
  ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
  ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
  ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)

theorem resultSignFixPost_unfold
    {sp sign limb0 limb1 limb2 limb3 : Word} :
    resultSignFixPost sp sign limb0 limb1 limb2 limb3 =
      (let mask := (0 : Word) - sign
       let sum0 := (limb0 ^^^ mask) + sign
       let carry0 := if BitVec.ult sum0 sign then (1 : Word) else 0
       let sum1 := (limb1 ^^^ mask) + carry0
       let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
       let sum2 := (limb2 ^^^ mask) + carry1
       let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
       let sum3 := (limb3 ^^^ mask) + carry2
       let carry3 := if BitVec.ult sum3 carry2 then (1 : Word) else 0
       (.x0 ↦ᵣ (0 : Word)) ** (.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sign) **
       (.x10 ↦ᵣ mask) ** (.x7 ↦ᵣ sum3) ** (.x11 ↦ᵣ carry3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ sum0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ sum1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ sum2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ sum3)) := by
  delta resultSignFixPost
  rfl

theorem resultSignFix_spec_in_sdivCode
    (sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3 : Word)
    (base : Word) :
    cpsTripleWithin 21 (base + resultSignFixOff)
      ((base + resultSignFixOff) + 84) (sdivCode base)
      (resultSignFixPre sp sign maskOld valueOld carryOld
        limb0 limb1 limb2 limb3)
      (resultSignFixPost sp sign limb0 limb1 limb2 limb3) := by
  rw [resultSignFixPre_unfold, resultSignFixPost_unfold]
  have hmono :
      ∀ a i,
        (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code
          .x12 .x8 .x10 .x7 .x11 0 8 16 24
          (base + resultSignFixOff)) a = some i →
        (sdivCode base) a = some i := by
    intro a i h
    exact sdivCode_resultSignFix_sub (base := base) a i
      (by simpa [resultSignFixCode,
        EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_code] using h)
  have hSpec :=
    EvmAsm.Evm64.evm_sdiv_cond_negate_256_block_spec_within
      .x12 .x8 .x10 .x7 .x11 0 8 16 24
      sp sign maskOld valueOld carryOld limb0 limb1 limb2 limb3
      (base + resultSignFixOff) (by decide) (by decide) (by decide)
  rw [EvmAsm.Evm64.condNegate256BlockPre_unfold,
    EvmAsm.Evm64.condNegate256BlockPost_unfold] at hSpec
  exact cpsTripleWithin_extend_code hmono hSpec

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

/-- Wrapper sub-region inside `sdivCode`. -/
theorem sdivCode_wrapper_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg base evm_sdiv_wrapper) a = some i →
      (sdivCode base) a = some i := by
  unfold sdivCode
  exact CodeReq.ofProg_mono_sub base base evm_sdiv evm_sdiv_wrapper 0
    (by bv_omega)
    (by unfold evm_sdiv; simp only [seq, Program]; rfl)
    (by
      rw [evm_sdiv_length, evm_sdiv_wrapper_length]
      norm_num)
    (by
      rw [evm_sdiv_length]
      norm_num)

/-- The appended unsigned DIV callable sub-region inside `sdivCode`. -/
theorem sdivCode_div_callable_sub {base : Word} :
    ∀ a i, (evm_div_callable_code (base + 284)) a = some i →
      (sdivCode base) a = some i := by
  intro a i h
  rw [evm_div_callable_code_eq_ofProg (base + 284)] at h
  unfold sdivCode
  exact CodeReq.ofProg_mono_sub base (base + 284)
    evm_sdiv evm_div_callable 71
    (by
      bv_omega)
    (by
      unfold evm_sdiv seq
      rw [← evm_sdiv_wrapper_length]
      have h_drop :
          List.drop evm_sdiv_wrapper.length
              (evm_sdiv_wrapper ++ evm_div_callable) =
            evm_div_callable := by
        exact List.drop_append_length
      rw [h_drop]
      simp only [List.take_length])
    (by native_decide)
    (by
      rw [evm_sdiv_length]
      norm_num)
    a i h

/-- Bundled top-level SDIV code subsumptions for the wrapper and appended
    unsigned DIV callable. -/
theorem sdivCode_top_level_subs {base : Word} :
    (∀ a i, (CodeReq.ofProg base evm_sdiv_wrapper) a = some i →
      (sdivCode base) a = some i) ∧
    (∀ a i, (evm_div_callable_code (base + 284)) a = some i →
      (sdivCode base) a = some i) := by
  exact ⟨sdivCode_wrapper_sub, sdivCode_div_callable_sub⟩

/-- The near `JAL` at the SDIV wrapper's `divCall` block targets the appended
    unsigned DIV callable, which starts at `base + wrapperEndOff`.  This is
    the entry-PC alignment fact needed to sequence the wrapper prefix with the
    callable DIV stack dispatcher. -/
theorem divCall_target_eq_wrapperEndOff (base : Word) :
    (base + divCallOff) + signExtend21 EvmAsm.Evm64.evm_sdivCallOff =
      base + wrapperEndOff := by
  show (base + (192 : Word)) + (92 : Word) = base + (284 : Word)
  bv_decide

/-- Under the standard RV PC-alignment invariant (`base` has its low bit
    clear), the JALR low-bit mask `&&& ~~~1` on the post-`divCall` return
    address `base + resultSignFixOff` is the identity. Bite-sized helper
    for slice 4 (evm-asm-tdlsu): used to align the exit PC of
    `evm_div_callable_spec_in_sdivCode` (which returns to `saved_ra &&& ~~~1`
    via JALR) with the SDIV wrapper's `resultSignFix` entry. -/
theorem base_add_resultSignFixOff_andn_one
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + resultSignFixOff) &&& ~~~(1 : Word) = base + resultSignFixOff := by
  show (base + (196 : Word)) &&& ~~~(1 : Word) = base + (196 : Word)
  bv_decide

/-- The return address written by the SDIV wrapper's near `divCall` is exactly
    the result-sign-fixup entry, and masking bit 0 for the eventual `JALR`
    keeps it there.  This is the concrete `raVal &&& ~~~1` alignment fact
    needed when composing the wrapper prefix with `evm_div_callable`. -/
theorem divCall_return_andn_one_eq_resultSignFixOff
    (base : Word) (hbase : base &&& 1 = 0) :
    (((base + divCallOff) + 4 : Word) &&& ~~~(1 : Word)) =
      base + resultSignFixOff := by
  show (((base + (192 : Word)) + (4 : Word)) &&& ~~~(1 : Word)) =
      base + (196 : Word)
  bv_decide

end EvmAsm.Evm64.SDiv.Compose
