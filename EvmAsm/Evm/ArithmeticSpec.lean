/-
  EvmAsm.Evm.ArithmeticSpec

  Full 256-bit EVM arithmetic specs (ADD, SUB) composed from per-limb specs.
  Each composes 8 per-limb specs + ADDI sp adjustment into a single cpsTriple.
-/

import EvmAsm.Evm.Arithmetic
import EvmAsm.Tactics.XSimp

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Helpers for full specs
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- pcFree proof for a 14-element memIs chain -/
local macro "pcFree14" : term =>
  `(pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))))))))

/-- pcFree proof for x11 reg + 14-element memIs chain (limb 0 frame) -/
local macro "pcFree15" : term =>
  `(pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))))))))))))

/-- pcFree proof for ADDI frame: 4 regs + 16 mem -/
local macro "pcFreeAddi" : term =>
  `(pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))))))))))))))

-- ============================================================================
-- Full 256-bit ADD spec
-- ============================================================================

/-- Full 256-bit EVM ADD: composes 8 per-limb ADD specs + ADDI sp adjustment.
    62 instructions total. Pops 2 stack words (A at sp, B at sp+32),
    writes A + B to sp+32..sp+60, advances sp by 32.
    Carry propagates through limbs via x5. -/
theorem evm_add_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Memory validity (16 hypotheses for sp+0, sp+4, ..., sp+60)
    (hv0 : isValidMemAccess sp = true)
    (hv4 : isValidMemAccess (sp + 4) = true)
    (hv8 : isValidMemAccess (sp + 8) = true)
    (hv12 : isValidMemAccess (sp + 12) = true)
    (hv16 : isValidMemAccess (sp + 16) = true)
    (hv20 : isValidMemAccess (sp + 20) = true)
    (hv24 : isValidMemAccess (sp + 24) = true)
    (hv28 : isValidMemAccess (sp + 28) = true)
    (hv32 : isValidMemAccess (sp + 32) = true)
    (hv36 : isValidMemAccess (sp + 36) = true)
    (hv40 : isValidMemAccess (sp + 40) = true)
    (hv44 : isValidMemAccess (sp + 44) = true)
    (hv48 : isValidMemAccess (sp + 48) = true)
    (hv52 : isValidMemAccess (sp + 52) = true)
    (hv56 : isValidMemAccess (sp + 56) = true)
    (hv60 : isValidMemAccess (sp + 60) = true) :
    -- Carry chain definitions
    let sum0 := a0 + b0
    let carry0 := if BitVec.ult sum0 b0 then (1 : Word) else 0
    let psum1 := a1 + b1
    let carry1a := if BitVec.ult psum1 b1 then (1 : Word) else 0
    let result1 := psum1 + carry0
    let carry1b := if BitVec.ult result1 carry0 then (1 : Word) else 0
    let carry1 := carry1a ||| carry1b
    let psum2 := a2 + b2
    let carry2a := if BitVec.ult psum2 b2 then (1 : Word) else 0
    let result2 := psum2 + carry1
    let carry2b := if BitVec.ult result2 carry1 then (1 : Word) else 0
    let carry2 := carry2a ||| carry2b
    let psum3 := a3 + b3
    let carry3a := if BitVec.ult psum3 b3 then (1 : Word) else 0
    let result3 := psum3 + carry2
    let carry3b := if BitVec.ult result3 carry2 then (1 : Word) else 0
    let carry3 := carry3a ||| carry3b
    let psum4 := a4 + b4
    let carry4a := if BitVec.ult psum4 b4 then (1 : Word) else 0
    let result4 := psum4 + carry3
    let carry4b := if BitVec.ult result4 carry3 then (1 : Word) else 0
    let carry4 := carry4a ||| carry4b
    let psum5 := a5 + b5
    let carry5a := if BitVec.ult psum5 b5 then (1 : Word) else 0
    let result5 := psum5 + carry4
    let carry5b := if BitVec.ult result5 carry4 then (1 : Word) else 0
    let carry5 := carry5a ||| carry5b
    let psum6 := a6 + b6
    let carry6a := if BitVec.ult psum6 b6 then (1 : Word) else 0
    let result6 := psum6 + carry5
    let carry6b := if BitVec.ult result6 carry5 then (1 : Word) else 0
    let carry6 := carry6a ||| carry6b
    let psum7 := a7 + b7
    let carry7a := if BitVec.ult psum7 b7 then (1 : Word) else 0
    let result7 := psum7 + carry6
    let carry7b := if BitVec.ult result7 carry6 then (1 : Word) else 0
    let carry7 := carry7a ||| carry7b
    cpsTriple base (base + 248)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ result7) ** (.x6 ↦ᵣ carry7b) ** (.x5 ↦ᵣ carry7) ** (.x11 ↦ᵣ carry7a) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ sum0) ** ((sp + 36) ↦ₘ result1) ** ((sp + 40) ↦ₘ result2) ** ((sp + 44) ↦ₘ result3) **
       ((sp + 48) ↦ₘ result4) ** ((sp + 52) ↦ₘ result5) ** ((sp + 56) ↦ₘ result6) ** ((sp + 60) ↦ₘ result7)) := by
  sorry

end EvmAsm
