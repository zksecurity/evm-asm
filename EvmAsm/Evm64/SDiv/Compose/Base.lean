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
import EvmAsm.Evm64.SDiv.Compose.BaseCode
import EvmAsm.Evm64.SDiv.Compose.BaseOffsets
import EvmAsm.Evm64.SDiv.Compose.BaseSignSequence
import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsSequence
import EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsSequence
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFix

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

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
