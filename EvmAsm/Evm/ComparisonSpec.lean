/-
  EvmAsm.Evm.ComparisonSpec

  Full 256-bit EVM GT spec composed from per-limb LT specs (with swapped operands).
  GT(a, b) = LT(b, a): load b-limbs into x7 and a-limbs into x6, compute borrow(b < a).
  Final borrow = 1 iff b < a iff a > b.
  54 instructions total: 45 borrow + 9 store.
-/

import EvmAsm.Evm.Comparison
import EvmAsm.Tactics.XSimp

open EvmAsm.Tactics

namespace EvmAsm

-- ============================================================================
-- Helpers
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

/-- sp + signExtend12 0 = sp -/
private theorem se0_eq_self (sp : Addr) : sp + signExtend12 (0 : BitVec 12) = sp := by
  simp only [signExtend12_0]; apply BitVec.eq_of_toNat_eq
  simp

/-- pcFree for a 12-element frame: 4 regs + 8 mems -/
local macro "pcFreeAddi12" : term =>
  `(pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))))))

/-- pcFree for x11 reg + 14 memory cells (borrow limb 0 frame) -/
local macro "pcFree15" : term =>
  `(pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))))))))))))

/-- pcFree for 14 memory cells (borrow carry limb frame) -/
local macro "pcFree14" : term =>
  `(pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))))))))

/-- pcFree for 8 memory cells (a-cell frame during store phase) -/
local macro "pcFree8" : term =>
  `(pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))

-- ============================================================================
-- Store phase helper: ADDI + 8 SW instructions
-- ============================================================================

/-- Store phase spec for LT/GT: ADDI sp+32 + SW borrow + 7×SW 0.
    Takes sp → sp+32, stores borrow to mem[sp+32], zeros to mem[sp+36..sp+60].
    9 instructions = 36 bytes. -/
theorem lt_result_store_spec (sp : Addr)
    (borrow v7 v6 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- Memory validity for sp+32..sp+60
    (hv32 : isValidMemAccess (sp + 32) = true)
    (hv36 : isValidMemAccess (sp + 36) = true)
    (hv40 : isValidMemAccess (sp + 40) = true)
    (hv44 : isValidMemAccess (sp + 44) = true)
    (hv48 : isValidMemAccess (sp + 48) = true)
    (hv52 : isValidMemAccess (sp + 52) = true)
    (hv56 : isValidMemAccess (sp + 56) = true)
    (hv60 : isValidMemAccess (sp + 60) = true) :
    cpsTriple base (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- Full 256-bit GT spec
-- ============================================================================

/-- Full 256-bit EVM GT: GT(a, b) = 1 iff a > b (unsigned).
    Computed as borrow chain of (b - a), same circuit as LT(b, a).
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    54 instructions = 216 bytes total. -/
theorem evm_gt_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Memory validity for all 16 stack cells
    (hv0  : isValidMemAccess sp = true)
    (hv4  : isValidMemAccess (sp + 4) = true)
    (hv8  : isValidMemAccess (sp + 8) = true)
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
    -- Borrow chain: b - a (GT direction)
    let borrow0 := if BitVec.ult b0 a0 then (1 : Word) else 0
    let borrow1a := if BitVec.ult b1 a1 then (1 : Word) else 0
    let temp1 := b1 - a1
    let borrow1b := if BitVec.ult temp1 borrow0 then (1 : Word) else 0
    let borrow1 := borrow1a ||| borrow1b
    let borrow2a := if BitVec.ult b2 a2 then (1 : Word) else 0
    let temp2 := b2 - a2
    let borrow2b := if BitVec.ult temp2 borrow1 then (1 : Word) else 0
    let borrow2 := borrow2a ||| borrow2b
    let borrow3a := if BitVec.ult b3 a3 then (1 : Word) else 0
    let temp3 := b3 - a3
    let borrow3b := if BitVec.ult temp3 borrow2 then (1 : Word) else 0
    let borrow3 := borrow3a ||| borrow3b
    let borrow4a := if BitVec.ult b4 a4 then (1 : Word) else 0
    let temp4 := b4 - a4
    let borrow4b := if BitVec.ult temp4 borrow3 then (1 : Word) else 0
    let borrow4 := borrow4a ||| borrow4b
    let borrow5a := if BitVec.ult b5 a5 then (1 : Word) else 0
    let temp5 := b5 - a5
    let borrow5b := if BitVec.ult temp5 borrow4 then (1 : Word) else 0
    let borrow5 := borrow5a ||| borrow5b
    let borrow6a := if BitVec.ult b6 a6 then (1 : Word) else 0
    let temp6 := b6 - a6
    let borrow6b := if BitVec.ult temp6 borrow5 then (1 : Word) else 0
    let borrow6 := borrow6a ||| borrow6b
    let borrow7a := if BitVec.ult b7 a7 then (1 : Word) else 0
    let temp7 := b7 - a7
    let borrow7b := if BitVec.ult temp7 borrow6 then (1 : Word) else 0
    let borrow7 := borrow7a ||| borrow7b
    cpsTriple base (base + 216)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (b7 - a7)) ** (.x6 ↦ᵣ borrow7b) **
       (.x5 ↦ᵣ borrow7) ** (.x11 ↦ᵣ borrow7a) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ borrow7) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- EQ: helper macros and store+SLTIU phase
-- ============================================================================

/-- pcFree for 2 regs + 14 mems (eq_limb0 frame in evm_eq_spec) -/
local macro "pcFree16eq0" : term =>
  `(pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_regIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
   (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))))))))))))

/-- Store phase spec for EQ: SLTIU + ADDI sp+32 + SW eq_result + 7×SW 0.
    SLTIU converts accumulated XOR to boolean eq_result (1 iff all limbs equal).
    ADDI takes sp → sp+32. Stores eq_result to mem[sp+32], zeros to mem[sp+36..sp+60].
    10 instructions = 40 bytes. -/
theorem eq_result_store_spec (sp : Addr)
    (acc v6 v5 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- Memory validity for sp+32..sp+60
    (hv32 : isValidMemAccess (sp + 32) = true)
    (hv36 : isValidMemAccess (sp + 36) = true)
    (hv40 : isValidMemAccess (sp + 40) = true)
    (hv44 : isValidMemAccess (sp + 44) = true)
    (hv48 : isValidMemAccess (sp + 48) = true)
    (hv52 : isValidMemAccess (sp + 52) = true)
    (hv56 : isValidMemAccess (sp + 56) = true)
    (hv60 : isValidMemAccess (sp + 60) = true) :
    let _eq_result := if BitVec.ult acc (1 : Word) then (1 : Word) else 0
    cpsTriple base (base + 40)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- Full 256-bit EQ spec
-- ============================================================================

/-- Full 256-bit EVM EQ: EQ(a, b) = 1 iff a == b (as 256-bit unsigned integers).
    Computed by XOR-ing each limb pair, OR-reducing, then SLTIU to boolean.
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    41 instructions = 164 bytes total. -/
theorem evm_eq_spec (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Memory validity for all 16 stack cells
    (hv0  : isValidMemAccess sp = true)
    (hv4  : isValidMemAccess (sp + 4) = true)
    (hv8  : isValidMemAccess (sp + 8) = true)
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
    -- XOR-OR accumulation chain
    let acc0 := a0 ^^^ b0
    let acc1 := acc0 ||| (a1 ^^^ b1)
    let acc2 := acc1 ||| (a2 ^^^ b2)
    let acc3 := acc2 ||| (a3 ^^^ b3)
    let acc4 := acc3 ||| (a4 ^^^ b4)
    let acc5 := acc4 ||| (a5 ^^^ b5)
    let acc6 := acc5 ||| (a6 ^^^ b6)
    let acc7 := acc6 ||| (a7 ^^^ b7)
    let eq_result := if BitVec.ult acc7 (1 : Word) then (1 : Word) else 0
    cpsTriple base (base + 164)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ eq_result) ** (.x6 ↦ᵣ (a7 ^^^ b7)) ** (.x5 ↦ᵣ b7) ** (.x11 ↦ᵣ v11) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ eq_result) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  sorry

end EvmAsm
