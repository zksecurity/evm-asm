/-
  EvmAsm.Evm64.Xor

  Full 256-bit EVM XOR spec with ValidMemRange abstractions.
-/

import EvmAsm.Evm64.Bitwise

namespace EvmAsm.Rv64

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM XOR: composes 4 per-limb XOR specs + sp adjustment. -/
theorem evm_xor_spec (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 68)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       ((base + 64) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       ((base + 64) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a3 ^^^ b3)) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ (a0 ^^^ b0)) ** ((sp + 40) ↦ₘ (a1 ^^^ b1)) ** ((sp + 48) ↦ₘ (a2 ^^^ b2)) ** ((sp + 56) ↦ₘ (a3 ^^^ b3))) := by
  have hv0 : isValidDwordAccess (sp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (sp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; have := hvalid.get (i := 3) (by omega); simpa using this
  have hv32 : isValidDwordAccess (sp + signExtend12 (32 : BitVec 12)) = true := by
    simp only [signExtend12_32]; have := hvalid.get (i := 4) (by omega); simpa using this
  have hv40 : isValidDwordAccess (sp + signExtend12 (40 : BitVec 12)) = true := by
    simp only [signExtend12_40]; have := hvalid.get (i := 5) (by omega); simpa using this
  have hv48 : isValidDwordAccess (sp + signExtend12 (48 : BitVec 12)) = true := by
    simp only [signExtend12_48]; have := hvalid.get (i := 6) (by omega); simpa using this
  have hv56 : isValidDwordAccess (sp + signExtend12 (56 : BitVec 12)) = true := by
    simp only [signExtend12_56]; have := hvalid.get (i := 7) (by omega); simpa using this
  have L0 := xor_limb_spec 0 32 sp a0 b0 v7 v6 base hv0 hv32
  have L1 := xor_limb_spec 8 40 sp a1 b1 (a0 ^^^ b0) b0 (base + 16) hv8 hv40
  have L2 := xor_limb_spec 16 48 sp a2 b2 (a1 ^^^ b1) b1 (base + 32) hv16 hv48
  have L3 := xor_limb_spec 24 56 sp a3 b3 (a2 ^^^ b2) b2 (base + 48) hv24 hv56
  have LADDI := addi_spec_gen_same .x12 sp 32 (base + 64) (by nofun)
  runBlock L0 L1 L2 L3 LADDI

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM XOR. -/
theorem evm_xor_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 68)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       ((base + 64) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       ((base + 64) ↦ᵢ .ADDI .x12 .x12 32) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 ^^^ b.getLimb 3)) ** (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a ^^^ b)) := by
  have h_main := evm_xor_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    v7 v6 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, EvmWord.getLimb_xor]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
