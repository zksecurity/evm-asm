/-
  EvmAsm.Evm64.SDiv.Compose.BaseFinalBlockSpecs

  Low-level SDIV wrapper specs for the final single-block instructions:
  the near DIV call, result-sign XOR, and saved-`ra` return.
-/

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

end EvmAsm.Evm64.SDiv.Compose
