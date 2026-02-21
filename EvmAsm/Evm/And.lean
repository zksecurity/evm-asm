/-
  EvmAsm.Evm.And

  Full 256-bit EVM AND spec with ProgramAt/ValidMemRange abstractions.
-/

import EvmAsm.Evm.Bitwise

namespace EvmAsm

-- ============================================================================
-- Full 256-bit AND spec with ProgramAt/ValidMemRange
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- Full 256-bit EVM AND: composes 8 per-limb AND specs + sp adjustment.
    33 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A &&& B to sp+32..sp+60, advances sp by 32.
    Uses ProgramAt and ValidMemRange for clean hypotheses. -/
theorem evm_and_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a7 &&& b7)) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ (a0 &&& b0)) ** ((sp + 36) ↦ₘ (a1 &&& b1)) ** ((sp + 40) ↦ₘ (a2 &&& b2)) ** ((sp + 44) ↦ₘ (a3 &&& b3)) **
       ((sp + 48) ↦ₘ (a4 &&& b4)) ** ((sp + 52) ↦ₘ (a5 &&& b5)) ** ((sp + 56) ↦ₘ (a6 &&& b6)) ** ((sp + 60) ↦ₘ (a7 &&& b7))) := by
  sorry

-- ============================================================================
-- Stack-level AND spec
-- ============================================================================

/-- Stack-level 256-bit EVM AND: operates on two EvmWords via evmWordIs.
    Uses ProgramAt and ValidMemRange for clean hypotheses. -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 7 &&& b.getLimb 7)) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b)) := by
  sorry

end EvmAsm
