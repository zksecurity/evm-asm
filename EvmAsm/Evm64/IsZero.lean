/-
  EvmAsm.Evm64.IsZero

  Full 256-bit EVM ISZERO spec composed from per-limb specs.
  12 instructions total. Unary: pops 1, pushes 1, sp unchanged.
-/

import EvmAsm.Evm64.Comparison

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM ISZERO: result = 1 iff all 4 limbs are 0.
    Unary: reads 256-bit word at sp, overwrites with boolean result.
    12 instructions = 48 bytes. -/
theorem evm_iszero_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 4) :
    let or_all := a0 ||| a1 ||| a2 ||| a3
    let result := if BitVec.ult or_all (1 : Word) then (1 : Word) else 0
    cpsTriple base (base + 48)
      (-- OR reduction code (7 instructions: base+0..base+24)
       (base ↦ᵢ .LD .x7 .x12 0) **
       ((base + 4) ↦ᵢ .LD .x6 .x12 8) ** ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) **
       ((base + 12) ↦ᵢ .LD .x6 .x12 16) ** ((base + 16) ↦ᵢ .OR .x7 .x7 .x6) **
       ((base + 20) ↦ᵢ .LD .x6 .x12 24) ** ((base + 24) ↦ᵢ .OR .x7 .x7 .x6) **
       -- SLTIU (1 instruction)
       ((base + 28) ↦ᵢ .SLTIU .x7 .x7 1) **
       -- Store phase (4 instructions: base+32..base+44)
       ((base + 32) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 36) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 40) ↦ᵢ .SD .x12 .x0 16) **
       ((base + 44) ↦ᵢ .SD .x12 .x0 24) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3))
      (-- Same code (preserved)
       (base ↦ᵢ .LD .x7 .x12 0) **
       ((base + 4) ↦ᵢ .LD .x6 .x12 8) ** ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) **
       ((base + 12) ↦ᵢ .LD .x6 .x12 16) ** ((base + 16) ↦ᵢ .OR .x7 .x7 .x6) **
       ((base + 20) ↦ᵢ .LD .x6 .x12 24) ** ((base + 24) ↦ᵢ .OR .x7 .x7 .x6) **
       ((base + 28) ↦ᵢ .SLTIU .x7 .x7 1) **
       ((base + 32) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 36) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 40) ↦ᵢ .SD .x12 .x0 16) **
       ((base + 44) ↦ᵢ .SD .x12 .x0 24) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ a3) **
       (sp ↦ₘ result) ** ((sp + 8) ↦ₘ 0) ** ((sp + 16) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0)) := by
  intro or_all; intro result
  -- LD x7 x12 0 (load limb 0 into x7)
  have L0 := ld_spec_gen .x7 .x12 sp v7 a0 0 base (by nofun) (by validMem)
  -- OR limbs 1-3
  have O1 := iszero_or_limb_spec 8 sp a1 v6 a0 (base + 4) (by validMem)
  have O2 := iszero_or_limb_spec 16 sp a2 a1 (a0 ||| a1) (base + 12) (by validMem)
  have O3 := iszero_or_limb_spec 24 sp a3 a2 (a0 ||| a1 ||| a2) (base + 20) (by validMem)
  -- SLTIU
  have T := sltiu_spec_gen_same .x7 (a0 ||| a1 ||| a2 ||| a3) 1 (base + 28) (by nofun)
  simp only [signExtend12_1] at T
  -- Store phase
  have S0 := sd_spec_gen .x12 .x7 sp
    (if BitVec.ult (a0 ||| a1 ||| a2 ||| a3) (1 : Word) then (1 : Word) else 0)
    a0 0 (base + 32) (by validMem)
  have S1 := sd_x0_spec_gen .x12 sp a1 8 (base + 36) (by validMem)
  have S2 := sd_x0_spec_gen .x12 sp a2 16 (base + 40) (by validMem)
  have S3 := sd_x0_spec_gen .x12 sp a3 24 (base + 44) (by validMem)
  runBlock L0 O1 O2 O3 T S0 S1 S2 S3

end EvmAsm.Rv64
