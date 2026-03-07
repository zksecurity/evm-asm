/-
  EvmAsm.Evm.Not

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Full NOT spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Full 256-bit EVM NOT: composes 8 per-limb NOT specs.
    24 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (v7 : Word)
    -- Memory validity
    (hv0 : isValidMemAccess sp = true)
    (hv4 : isValidMemAccess (sp + 4) = true)
    (hv8 : isValidMemAccess (sp + 8) = true)
    (hv12 : isValidMemAccess (sp + 12) = true)
    (hv16 : isValidMemAccess (sp + 16) = true)
    (hv20 : isValidMemAccess (sp + 20) = true)
    (hv24 : isValidMemAccess (sp + 24) = true)
    (hv28 : isValidMemAccess (sp + 28) = true) :
    let c := signExtend12 (-1 : BitVec 12)
    cpsTriple base (base + 96)
      (-- Limb 0 code
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       -- Limb 1 code
       ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
       -- Limb 2 code
       ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
       -- Limb 3 code
       ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
       -- Limb 4 code
       ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
       -- Limb 5 code
       ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
       -- Limb 6 code
       ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
       -- Limb 7 code
       ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
       ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
       ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
       ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
       ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
       ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 4) ↦ₘ (a1 ^^^ c)) ** ((sp + 8) ↦ₘ (a2 ^^^ c)) ** ((sp + 12) ↦ₘ (a3 ^^^ c)) **
       ((sp + 16) ↦ₘ (a4 ^^^ c)) ** ((sp + 20) ↦ₘ (a5 ^^^ c)) ** ((sp + 24) ↦ₘ (a6 ^^^ c)) ** ((sp + 28) ↦ₘ (a7 ^^^ c))) := by
  -- Memory validity with signExtend normalization
  have hvm0 : isValidMemAccess (sp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0
  have hvm4 : isValidMemAccess (sp + signExtend12 (4 : BitVec 12)) = true := by
    simp only [signExtend12_4]; exact hv4
  have hvm8 : isValidMemAccess (sp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; exact hv8
  have hvm12 : isValidMemAccess (sp + signExtend12 (12 : BitVec 12)) = true := by
    simp only [signExtend12_12]; exact hv12
  have hvm16 : isValidMemAccess (sp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; exact hv16
  have hvm20 : isValidMemAccess (sp + signExtend12 (20 : BitVec 12)) = true := by
    simp only [signExtend12_20]; exact hv20
  have hvm24 : isValidMemAccess (sp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; exact hv24
  have hvm28 : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true := by
    simp only [signExtend12_28]; exact hv28
  -- Compose 8 per-limb NOT specs via runBlock (manual mode with address normalization)
  have L0 := not_limb_spec 0 sp a0 v7 base hvm0
  have L1 := not_limb_spec 4 sp a1 (a0 ^^^ signExtend12 (-1 : BitVec 12)) (base + 12) hvm4
  have L2 := not_limb_spec 8 sp a2 (a1 ^^^ signExtend12 (-1 : BitVec 12)) (base + 24) hvm8
  have L3 := not_limb_spec 12 sp a3 (a2 ^^^ signExtend12 (-1 : BitVec 12)) (base + 36) hvm12
  have L4 := not_limb_spec 16 sp a4 (a3 ^^^ signExtend12 (-1 : BitVec 12)) (base + 48) hvm16
  have L5 := not_limb_spec 20 sp a5 (a4 ^^^ signExtend12 (-1 : BitVec 12)) (base + 60) hvm20
  have L6 := not_limb_spec 24 sp a6 (a5 ^^^ signExtend12 (-1 : BitVec 12)) (base + 72) hvm24
  have L7 := not_limb_spec 28 sp a7 (a6 ^^^ signExtend12 (-1 : BitVec 12)) (base + 84) hvm28
  runBlock L0 L1 L2 L3 L4 L5 L6 L7

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 32 := by
  native_decide

set_option maxHeartbeats 6400000 in
/-- Stack-level 256-bit EVM NOT: complements an EvmWord in-place. -/
theorem evm_not_stack_spec (sp base : Addr)
    (a : EvmWord) (v7 : Word)
    (hv0 : isValidMemAccess sp = true)
    (hv4 : isValidMemAccess (sp + 4) = true)
    (hv8 : isValidMemAccess (sp + 8) = true)
    (hv12 : isValidMemAccess (sp + 12) = true)
    (hv16 : isValidMemAccess (sp + 16) = true)
    (hv20 : isValidMemAccess (sp + 20) = true)
    (hv24 : isValidMemAccess (sp + 24) = true)
    (hv28 : isValidMemAccess (sp + 28) = true) :
    let c := signExtend12 (-1 : BitVec 12)
    cpsTriple base (base + 96)
      (-- Code
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
       ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
       ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
       ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
       ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
       ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28) **
       -- Registers + memory
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      (-- Same code (preserved)
       (base ↦ᵢ .LW .x7 .x12 0) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 8) ↦ᵢ .SW .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LW .x7 .x12 4) ** ((base + 16) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 20) ↦ᵢ .SW .x12 .x7 4) **
       ((base + 24) ↦ᵢ .LW .x7 .x12 8) ** ((base + 28) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 32) ↦ᵢ .SW .x12 .x7 8) **
       ((base + 36) ↦ᵢ .LW .x7 .x12 12) ** ((base + 40) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 44) ↦ᵢ .SW .x12 .x7 12) **
       ((base + 48) ↦ᵢ .LW .x7 .x12 16) ** ((base + 52) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 56) ↦ᵢ .SW .x12 .x7 16) **
       ((base + 60) ↦ᵢ .LW .x7 .x12 20) ** ((base + 64) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 68) ↦ᵢ .SW .x12 .x7 20) **
       ((base + 72) ↦ᵢ .LW .x7 .x12 24) ** ((base + 76) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 80) ↦ᵢ .SW .x12 .x7 24) **
       ((base + 84) ↦ᵢ .LW .x7 .x12 28) ** ((base + 88) ↦ᵢ .XORI .x7 .x7 (-1)) ** ((base + 92) ↦ᵢ .SW .x12 .x7 28) **
       -- Registers + memory (updated)
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a.getLimb 7 ^^^ c)) ** evmWordIs sp (~~~a)) := by
  -- Helper: (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1)
  have not_limb_eq : ∀ i : Fin 8,
      (~~~a).getLimb i = a.getLimb i ^^^ signExtend12 (-1 : BitVec 12) := by
    intro i
    rw [EvmWord.getLimb_not, BitVec.not_def, BitVec.xor_comm, ← signExtend12_neg1_eq_allOnes]
  -- Apply evm_not_spec with individual limbs
  have h_main := evm_not_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    v7 hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs, not_limb_eq]
      xperm_hyp hq)
    h_main

end EvmAsm
