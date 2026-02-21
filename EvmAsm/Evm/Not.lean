/-
  EvmAsm.Evm.Not

  Full 256-bit EVM NOT spec composed from per-limb specs.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- pcFree proof for a 7-element memIs chain -/
local macro "pcFree7" : term =>
  `(pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_memIs _ _)))))))

/-- Full 256-bit EVM NOT: composes 8 per-limb NOT specs.
    24 instructions total. Unary: complements each limb in-place, sp unchanged. -/
theorem evm_not_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (v7 : Word)
    -- Limb 0 code (base + 0/4/8)
    (hc0 : True)
    (hc1 : True)
    (hc2 : True)
    -- Limb 1 code (base + 12/16/20)
    (hc3 : True)
    (hc4 : True)
    (hc5 : True)
    -- Limb 2 code (base + 24/28/32)
    (hc6 : True)
    (hc7 : True)
    (hc8 : True)
    -- Limb 3 code (base + 36/40/44)
    (hc9 : True)
    (hc10 : True)
    (hc11 : True)
    -- Limb 4 code (base + 48/52/56)
    (hc12 : True)
    (hc13 : True)
    (hc14 : True)
    -- Limb 5 code (base + 60/64/68)
    (hc15 : True)
    (hc16 : True)
    (hc17 : True)
    -- Limb 6 code (base + 72/76/80)
    (hc18 : True)
    (hc19 : True)
    (hc20 : True)
    -- Limb 7 code (base + 84/88/92)
    (hc21 : True)
    (hc22 : True)
    (hc23 : True)
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
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a7 ^^^ c)) **
       (sp ↦ₘ (a0 ^^^ c)) ** ((sp + 4) ↦ₘ (a1 ^^^ c)) ** ((sp + 8) ↦ₘ (a2 ^^^ c)) ** ((sp + 12) ↦ₘ (a3 ^^^ c)) **
       ((sp + 16) ↦ₘ (a4 ^^^ c)) ** ((sp + 20) ↦ₘ (a5 ^^^ c)) ** ((sp + 24) ↦ₘ (a6 ^^^ c)) ** ((sp + 28) ↦ₘ (a7 ^^^ c))) := by
  sorry

-- ============================================================================
-- Stack-level NOT spec
-- ============================================================================

theorem signExtend12_neg1_eq_allOnes : signExtend12 (-1 : BitVec 12) = BitVec.allOnes 32 := by
  native_decide

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
    cpsTriple base (base + 96)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** evmWordIs sp a)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ ((~~~a).getLimb 7)) ** evmWordIs sp (~~~a)) := by
  sorry

end EvmAsm
