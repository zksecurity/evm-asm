/-
  EvmAsm.Evm64.SDiv.Compose.BaseCode

  CodeReq handles and sub-block inclusion lemmas for the SDIV wrapper.
-/

import EvmAsm.Evm64.SDiv.Compose.CodeHandles

namespace EvmAsm.Evm64.SDiv.Compose

theorem sdivCode_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (sdivCode base) a = some i := by
  unfold saveRaCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_sdiv_legacy (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (sdivCode base) a = some i := by
  unfold dividendSignCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (sdivCode base) a = some i := by
  unfold divisorSignCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) 3
    (by simp [divisorSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCode base) a = some i := by
  unfold dividendAbsCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCode base) a = some i := by
  unfold divisorAbsCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCode base) a = some i := by
  unfold signXorCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv_legacy (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCode base) a = some i := by
  unfold divCallCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCode base) a = some i := by
  unfold resultSignFixCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCode base) a = some i := by
  unfold savedRaRetCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv_legacy (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCode_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCode base) a = some i → (sdivCode base) a = some i := by
  unfold divCallableCode sdivCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv_legacy EvmAsm.Evm64.evm_div_callable 71
    (by simp [wrapperEndOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_legacy_length]; norm_num)

theorem sdivCodeV4_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold saveRaCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold dividendSignCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divisorSignCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff) 3
    (by simp [divisorSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold dividendAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 5
    (by simp [dividendAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divisorAbsCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 26
    (by simp [divisorAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_signXor_sub {base : Word} :
    ∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold signXorCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + signXorOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Rv64.XOR' .x8 .x8 .x9) 47
    (by simp [signXorOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCall_sub {base : Word} :
    ∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divCallOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff) 48
    (by simp [divCallOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold resultSignFixCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_sdiv_v4
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold savedRaRetCode sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_sdiv_v4 (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

theorem sdivCodeV4_divCallable_sub {base : Word} :
    ∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i := by
  unfold divCallableCodeV4 sdivCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_sdiv_v4 EvmAsm.Evm64.evm_div_callable_v4 71
    (by simp [wrapperEndOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_sdiv_v4_length]; norm_num)

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

theorem sdivCodeV4_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (signXorCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (sdivCodeV4 base) a = some i) ∧
    (∀ a i, (divCallableCodeV4 base) a = some i → (sdivCodeV4 base) a = some i) := by
  exact ⟨sdivCodeV4_saveRa_sub, sdivCodeV4_dividendSign_sub,
    sdivCodeV4_divisorSign_sub, sdivCodeV4_dividendAbs_sub,
    sdivCodeV4_divisorAbs_sub, sdivCodeV4_signXor_sub, sdivCodeV4_divCall_sub,
    sdivCodeV4_resultSignFix_sub, sdivCodeV4_savedRaRet_sub,
    sdivCodeV4_divCallable_sub⟩

end EvmAsm.Evm64.SDiv.Compose
