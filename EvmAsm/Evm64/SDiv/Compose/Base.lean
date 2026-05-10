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

/-- Canonical code requirement for the full SDIV region: the wrapper followed
    by the appended unsigned DIV callable. -/
abbrev sdivCode (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_sdiv

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
theorem sdivCode_block_subs {base : Word} :
    (∀ a i, (CodeReq.ofProg base evm_sdiv_wrapper) a = some i →
      (sdivCode base) a = some i) ∧
    (∀ a i, (evm_div_callable_code (base + 284)) a = some i →
      (sdivCode base) a = some i) := by
  exact ⟨sdivCode_wrapper_sub, sdivCode_div_callable_sub⟩

end EvmAsm.Evm64.SDiv.Compose
