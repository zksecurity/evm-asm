/-
  EvmAsm.Evm.Xor

  Full 256-bit EVM XOR spec composed from per-limb specs.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- Full 256-bit EVM XOR via generic binary_bitwise_spec. -/
theorem evm_xor_spec (code : CodeMem) (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hcode : ProgramAt code base evm_xor)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple code base (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a7 ^^^ b7)) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ (a0 ^^^ b0)) ** ((sp + 36) ↦ₘ (a1 ^^^ b1)) ** ((sp + 40) ↦ₘ (a2 ^^^ b2)) ** ((sp + 44) ↦ₘ (a3 ^^^ b3)) **
       ((sp + 48) ↦ₘ (a4 ^^^ b4)) ** ((sp + 52) ↦ₘ (a5 ^^^ b5)) ** ((sp + 56) ↦ₘ (a6 ^^^ b6)) ** ((sp + 60) ↦ₘ (a7 ^^^ b7))) := by
  have hc0  := hcode.fetch 0  base        (.LW .x7 .x12 0)         (by decide) (by decide) (by bv_addr)
  have hc1  := hcode.fetch 1  (base + 4)  (.LW .x6 .x12 32)        (by decide) (by decide) (by bv_addr)
  have hc2  := hcode.fetch 2  (base + 8)  (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc3  := hcode.fetch 3  (base + 12) (.SW .x12 .x7 32)         (by decide) (by decide) (by bv_addr)
  have hc4  := hcode.fetch 4  (base + 16) (.LW .x7 .x12 4)         (by decide) (by decide) (by bv_addr)
  have hc5  := hcode.fetch 5  (base + 20) (.LW .x6 .x12 36)        (by decide) (by decide) (by bv_addr)
  have hc6  := hcode.fetch 6  (base + 24) (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc7  := hcode.fetch 7  (base + 28) (.SW .x12 .x7 36)         (by decide) (by decide) (by bv_addr)
  have hc8  := hcode.fetch 8  (base + 32) (.LW .x7 .x12 8)         (by decide) (by decide) (by bv_addr)
  have hc9  := hcode.fetch 9  (base + 36) (.LW .x6 .x12 40)        (by decide) (by decide) (by bv_addr)
  have hc10 := hcode.fetch 10 (base + 40) (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc11 := hcode.fetch 11 (base + 44) (.SW .x12 .x7 40)         (by decide) (by decide) (by bv_addr)
  have hc12 := hcode.fetch 12 (base + 48) (.LW .x7 .x12 12)        (by decide) (by decide) (by bv_addr)
  have hc13 := hcode.fetch 13 (base + 52) (.LW .x6 .x12 44)        (by decide) (by decide) (by bv_addr)
  have hc14 := hcode.fetch 14 (base + 56) (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc15 := hcode.fetch 15 (base + 60) (.SW .x12 .x7 44)         (by decide) (by decide) (by bv_addr)
  have hc16 := hcode.fetch 16 (base + 64) (.LW .x7 .x12 16)        (by decide) (by decide) (by bv_addr)
  have hc17 := hcode.fetch 17 (base + 68) (.LW .x6 .x12 48)        (by decide) (by decide) (by bv_addr)
  have hc18 := hcode.fetch 18 (base + 72) (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc19 := hcode.fetch 19 (base + 76) (.SW .x12 .x7 48)         (by decide) (by decide) (by bv_addr)
  have hc20 := hcode.fetch 20 (base + 80) (.LW .x7 .x12 20)        (by decide) (by decide) (by bv_addr)
  have hc21 := hcode.fetch 21 (base + 84) (.LW .x6 .x12 52)        (by decide) (by decide) (by bv_addr)
  have hc22 := hcode.fetch 22 (base + 88) (.XOR .x7 .x7 .x6)       (by decide) (by decide) (by bv_addr)
  have hc23 := hcode.fetch 23 (base + 92) (.SW .x12 .x7 52)         (by decide) (by decide) (by bv_addr)
  have hc24 := hcode.fetch 24 (base + 96) (.LW .x7 .x12 24)        (by decide) (by decide) (by bv_addr)
  have hc25 := hcode.fetch 25 (base + 100) (.LW .x6 .x12 56)       (by decide) (by decide) (by bv_addr)
  have hc26 := hcode.fetch 26 (base + 104) (.XOR .x7 .x7 .x6)      (by decide) (by decide) (by bv_addr)
  have hc27 := hcode.fetch 27 (base + 108) (.SW .x12 .x7 56)        (by decide) (by decide) (by bv_addr)
  have hc28 := hcode.fetch 28 (base + 112) (.LW .x7 .x12 28)       (by decide) (by decide) (by bv_addr)
  have hc29 := hcode.fetch 29 (base + 116) (.LW .x6 .x12 60)       (by decide) (by decide) (by bv_addr)
  have hc30 := hcode.fetch 30 (base + 120) (.XOR .x7 .x7 .x6)      (by decide) (by decide) (by bv_addr)
  have hc31 := hcode.fetch 31 (base + 124) (.SW .x12 .x7 60)        (by decide) (by decide) (by bv_addr)
  have hc32 := hcode.fetch 32 (base + 128) (.ADDI .x12 .x12 32)    (by decide) (by decide) (by bv_addr)
  exact binary_bitwise_spec code sp base (· ^^^ ·) (.XOR .x7 .x7 .x6)
    a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6
    (fun off_a off_b => xor_limb_spec code off_a off_b sp)
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11
    hc12 hc13 hc14 hc15 hc16 hc17 hc18 hc19 hc20 hc21 hc22 hc23
    hc24 hc25 hc26 hc27 hc28 hc29 hc30 hc31 hc32
    hvalid

/-- Stack-level 256-bit EVM XOR. -/
theorem evm_xor_stack_spec (code : CodeMem) (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hcode : ProgramAt code base evm_xor)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple code base (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 7 ^^^ b.getLimb 7)) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a ^^^ b)) := by
  simp only [evmWordIs, EvmWord.getLimb_xor, sepConj_assoc']
  have h32_4  : sp + 32 + 4  = sp + 36 := by bv_addr
  have h32_8  : sp + 32 + 8  = sp + 40 := by bv_addr
  have h32_12 : sp + 32 + 12 = sp + 44 := by bv_addr
  have h32_16 : sp + 32 + 16 = sp + 48 := by bv_addr
  have h32_20 : sp + 32 + 20 = sp + 52 := by bv_addr
  have h32_24 : sp + 32 + 24 = sp + 56 := by bv_addr
  have h32_28 : sp + 32 + 28 = sp + 60 := by bv_addr
  simp only [h32_4, h32_8, h32_12, h32_16, h32_20, h32_24, h32_28]
  exact evm_xor_spec code sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    (b.getLimb 4) (b.getLimb 5) (b.getLimb 6) (b.getLimb 7)
    v7 v6 hcode hvalid

end EvmAsm
