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
theorem lt_result_store_spec (code : CodeMem) (sp : Addr)
    (borrow v7 v6 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- ADDI x12, x12, 32
    (hc0 : code base = some (.ADDI .x12 .x12 32))
    -- SW x12, x5, 0 (store borrow)
    (hc1 : code (base + 4) = some (.SW .x12 .x5 0))
    -- SW x12, x0, 4..28 (store zeros)
    (hc2 : code (base + 8) = some (.SW .x12 .x0 4))
    (hc3 : code (base + 12) = some (.SW .x12 .x0 8))
    (hc4 : code (base + 16) = some (.SW .x12 .x0 12))
    (hc5 : code (base + 20) = some (.SW .x12 .x0 16))
    (hc6 : code (base + 24) = some (.SW .x12 .x0 20))
    (hc7 : code (base + 28) = some (.SW .x12 .x0 24))
    (hc8 : code (base + 32) = some (.SW .x12 .x0 28))
    -- Memory validity for sp+32..sp+60
    (hv32 : isValidMemAccess (sp + 32) = true)
    (hv36 : isValidMemAccess (sp + 36) = true)
    (hv40 : isValidMemAccess (sp + 40) = true)
    (hv44 : isValidMemAccess (sp + 44) = true)
    (hv48 : isValidMemAccess (sp + 48) = true)
    (hv52 : isValidMemAccess (sp + 52) = true)
    (hv56 : isValidMemAccess (sp + 56) = true)
    (hv60 : isValidMemAccess (sp + 60) = true) :
    cpsTriple code base (base + 36)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  -- Step LA: ADDI x12, x12, 32 (base → base+4)
  have LA := addi_spec_gen_same code .x12 sp 32 base (by nofun) hc0
  simp only [signExtend12_32] at LA
  rw [show base + 4 = base + 4 from rfl] at LA
  have LAf := cpsTriple_frame_left code base (base + 4) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFreeAddi12 LA
  -- Step S0: SW x12, x5, 0 — mem[sp+32] := borrow (base+4 → base+8)
  have S0 := sw_spec_gen code .x12 .x5 (sp + 32) borrow b0 0 (base + 4) hc1
    (by simp only [signExtend12_0]; rw [show (sp + 32 : Addr) + 0 = sp + 32 from by bv_addr]; exact hv32)
  simp only [signExtend12_0] at S0
  rw [show (sp + 32) + 0 = sp + 32 from by bv_addr,
      show (base + 4) + 4 = base + 8 from by bv_addr] at S0
  have S0f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x11 ↦ᵣ v11) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _)))))))))) S0
  -- Step S1: SW x12, x0, 4 — mem[sp+36] := 0 (base+8 → base+12)
  have S1 := sw_x0_spec_gen code .x12 (sp + 32) b1 4 (base + 8) hc2
    (by simp only [signExtend12_4]; rw [show (sp + 32) + 4 = sp + 36 from by bv_addr]; exact hv36)
  simp only [signExtend12_4] at S1
  rw [show (sp + 32) + 4 = sp + 36 from by bv_addr,
      show (base + 8) + 4 = base + 12 from by bv_addr] at S1
  have S1f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S1
  -- Step S2: SW x12, x0, 8 — mem[sp+40] := 0 (base+12 → base+16)
  have S2 := sw_x0_spec_gen code .x12 (sp + 32) b2 8 (base + 12) hc3
    (by simp only [signExtend12_8]; rw [show (sp + 32) + 8 = sp + 40 from by bv_addr]; exact hv40)
  simp only [signExtend12_8] at S2
  rw [show (sp + 32) + 8 = sp + 40 from by bv_addr,
      show (base + 12) + 4 = base + 16 from by bv_addr] at S2
  have S2f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S2
  -- Step S3: SW x12, x0, 12 — mem[sp+44] := 0 (base+16 → base+20)
  have S3 := sw_x0_spec_gen code .x12 (sp + 32) b3 12 (base + 16) hc4
    (by simp only [signExtend12_12]; rw [show (sp + 32) + 12 = sp + 44 from by bv_addr]; exact hv44)
  simp only [signExtend12_12] at S3
  rw [show (sp + 32) + 12 = sp + 44 from by bv_addr,
      show (base + 16) + 4 = base + 20 from by bv_addr] at S3
  have S3f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S3
  -- Step S4: SW x12, x0, 16 — mem[sp+48] := 0 (base+20 → base+24)
  have S4 := sw_x0_spec_gen code .x12 (sp + 32) b4 16 (base + 20) hc5
    (by simp only [signExtend12_16]; rw [show (sp + 32) + 16 = sp + 48 from by bv_addr]; exact hv48)
  simp only [signExtend12_16] at S4
  rw [show (sp + 32) + 16 = sp + 48 from by bv_addr,
      show (base + 20) + 4 = base + 24 from by bv_addr] at S4
  have S4f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S4
  -- Step S5: SW x12, x0, 20 — mem[sp+52] := 0 (base+24 → base+28)
  have S5 := sw_x0_spec_gen code .x12 (sp + 32) b5 20 (base + 24) hc6
    (by simp only [signExtend12_20]; rw [show (sp + 32) + 20 = sp + 52 from by bv_addr]; exact hv52)
  simp only [signExtend12_20] at S5
  rw [show (sp + 32) + 20 = sp + 52 from by bv_addr,
      show (base + 24) + 4 = base + 28 from by bv_addr] at S5
  have S5f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S5
  -- Step S6: SW x12, x0, 24 — mem[sp+56] := 0 (base+28 → base+32)
  have S6 := sw_x0_spec_gen code .x12 (sp + 32) b6 24 (base + 28) hc7
    (by simp only [signExtend12_24]; rw [show (sp + 32) + 24 = sp + 56 from by bv_addr]; exact hv56)
  simp only [signExtend12_24] at S6
  rw [show (sp + 32) + 24 = sp + 56 from by bv_addr,
      show (base + 28) + 4 = base + 32 from by bv_addr] at S6
  have S6f := cpsTriple_frame_left code (base + 28) (base + 32) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S6
  -- Step S7: SW x12, x0, 28 — mem[sp+60] := 0 (base+32 → base+36)
  have S7 := sw_x0_spec_gen code .x12 (sp + 32) b7 28 (base + 32) hc8
    (by simp only [signExtend12_28]; rw [show (sp + 32) + 28 = sp + 60 from by bv_addr]; exact hv60)
  simp only [signExtend12_28] at S7
  rw [show (sp + 32) + 28 = sp + 60 from by bv_addr,
      show (base + 32) + 4 = base + 36 from by bv_addr] at S7
  have S7f := cpsTriple_frame_left code (base + 32) (base + 36) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ borrow) ** ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S7
  -- Compose all 9 steps
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8
  clear hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear LA S0 S1 S2 S3 S4 S5 S6 S7
  have c01 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) LAf S0f
  clear LAf S0f
  have c012 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 S1f
  clear c01 S1f
  have c0123 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012 S2f
  clear c012 S2f
  have c01234 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123 S3f
  clear c0123 S3f
  have c012345 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234 S4f
  clear c01234 S4f
  have c0123456 := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345 S5f
  clear c012345 S5f
  have c01234567 := cpsTriple_seq_with_perm code base (base + 28) (base + 32) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123456 S6f
  clear c0123456 S6f
  have cfull := cpsTriple_seq_with_perm code base (base + 32) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234567 S7f
  clear c01234567 S7f
  exact cpsTriple_consequence code base (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Full 256-bit GT spec
-- ============================================================================

/-- Full 256-bit EVM GT: GT(a, b) = 1 iff a > b (unsigned).
    Computed as borrow chain of (b - a), same circuit as LT(b, a).
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    54 instructions = 216 bytes total. -/
theorem evm_gt_spec (code : CodeMem) (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Limb 0 code (GT: b first, a second)
    (hc0 : code base = some (.LW .x7 .x12 32))
    (hc1 : code (base + 4) = some (.LW .x6 .x12 0))
    (hc2 : code (base + 8) = some (.SLTU .x5 .x7 .x6))
    -- Limb 1
    (hc3 : code (base + 12) = some (.LW .x7 .x12 36))
    (hc4 : code (base + 16) = some (.LW .x6 .x12 4))
    (hc5 : code (base + 20) = some (.SLTU .x11 .x7 .x6))
    (hc6 : code (base + 24) = some (.SUB .x7 .x7 .x6))
    (hc7 : code (base + 28) = some (.SLTU .x6 .x7 .x5))
    (hc8 : code (base + 32) = some (.OR .x5 .x11 .x6))
    -- Limb 2
    (hc9  : code (base + 36) = some (.LW .x7 .x12 40))
    (hc10 : code (base + 40) = some (.LW .x6 .x12 8))
    (hc11 : code (base + 44) = some (.SLTU .x11 .x7 .x6))
    (hc12 : code (base + 48) = some (.SUB .x7 .x7 .x6))
    (hc13 : code (base + 52) = some (.SLTU .x6 .x7 .x5))
    (hc14 : code (base + 56) = some (.OR .x5 .x11 .x6))
    -- Limb 3
    (hc15 : code (base + 60) = some (.LW .x7 .x12 44))
    (hc16 : code (base + 64) = some (.LW .x6 .x12 12))
    (hc17 : code (base + 68) = some (.SLTU .x11 .x7 .x6))
    (hc18 : code (base + 72) = some (.SUB .x7 .x7 .x6))
    (hc19 : code (base + 76) = some (.SLTU .x6 .x7 .x5))
    (hc20 : code (base + 80) = some (.OR .x5 .x11 .x6))
    -- Limb 4
    (hc21 : code (base + 84) = some (.LW .x7 .x12 48))
    (hc22 : code (base + 88) = some (.LW .x6 .x12 16))
    (hc23 : code (base + 92) = some (.SLTU .x11 .x7 .x6))
    (hc24 : code (base + 96) = some (.SUB .x7 .x7 .x6))
    (hc25 : code (base + 100) = some (.SLTU .x6 .x7 .x5))
    (hc26 : code (base + 104) = some (.OR .x5 .x11 .x6))
    -- Limb 5
    (hc27 : code (base + 108) = some (.LW .x7 .x12 52))
    (hc28 : code (base + 112) = some (.LW .x6 .x12 20))
    (hc29 : code (base + 116) = some (.SLTU .x11 .x7 .x6))
    (hc30 : code (base + 120) = some (.SUB .x7 .x7 .x6))
    (hc31 : code (base + 124) = some (.SLTU .x6 .x7 .x5))
    (hc32 : code (base + 128) = some (.OR .x5 .x11 .x6))
    -- Limb 6
    (hc33 : code (base + 132) = some (.LW .x7 .x12 56))
    (hc34 : code (base + 136) = some (.LW .x6 .x12 24))
    (hc35 : code (base + 140) = some (.SLTU .x11 .x7 .x6))
    (hc36 : code (base + 144) = some (.SUB .x7 .x7 .x6))
    (hc37 : code (base + 148) = some (.SLTU .x6 .x7 .x5))
    (hc38 : code (base + 152) = some (.OR .x5 .x11 .x6))
    -- Limb 7
    (hc39 : code (base + 156) = some (.LW .x7 .x12 60))
    (hc40 : code (base + 160) = some (.LW .x6 .x12 28))
    (hc41 : code (base + 164) = some (.SLTU .x11 .x7 .x6))
    (hc42 : code (base + 168) = some (.SUB .x7 .x7 .x6))
    (hc43 : code (base + 172) = some (.SLTU .x6 .x7 .x5))
    (hc44 : code (base + 176) = some (.OR .x5 .x11 .x6))
    -- Store phase
    (hc45 : code (base + 180) = some (.ADDI .x12 .x12 32))
    (hc46 : code (base + 184) = some (.SW .x12 .x5 0))
    (hc47 : code (base + 188) = some (.SW .x12 .x0 4))
    (hc48 : code (base + 192) = some (.SW .x12 .x0 8))
    (hc49 : code (base + 196) = some (.SW .x12 .x0 12))
    (hc50 : code (base + 200) = some (.SW .x12 .x0 16))
    (hc51 : code (base + 204) = some (.SW .x12 .x0 20))
    (hc52 : code (base + 208) = some (.SW .x12 .x0 24))
    (hc53 : code (base + 212) = some (.SW .x12 .x0 28))
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
    cpsTriple code base (base + 216)
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
  -- Address normalization helpers
  have hse0 : sp + signExtend12 (0 : BitVec 12) = sp := se0_eq_self sp
  -- ========== Limb 0: lt_limb0_spec (off_a=32=b, off_b=0=a) ==========
  -- borrow0 = (b0 < a0) — GT limb 0 borrow
  have L0 := lt_limb0_spec code 32 0 sp b0 a0 v7 v6 v5 base hc0 hc1 hc2
    (by simp only [signExtend12_32]; exact hv32)
    (by rw [hse0]; exact hv0)
  simp only [signExtend12_32] at L0; rw [hse0] at L0
  have L0f := cpsTriple_frame_left code base (base + 12) _ _
    ((.x11 ↦ᵣ v11) **
     ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L0
  -- ========== Limb 1: lt_limb_carry_spec (off_a=36=b1, off_b=4=a1) ==========
  have L1 := lt_limb_carry_spec code 36 4 sp b1 a1 b0 a0
    (if BitVec.ult b0 a0 then (1 : Word) else 0) v11 (base + 12)
    hc3
    (by rw [show (base + 12) + 4 = base + 16 from by bv_addr]; exact hc4)
    (by rw [show (base + 12) + 8 = base + 20 from by bv_addr]; exact hc5)
    (by rw [show (base + 12) + 12 = base + 24 from by bv_addr]; exact hc6)
    (by rw [show (base + 12) + 16 = base + 28 from by bv_addr]; exact hc7)
    (by rw [show (base + 12) + 20 = base + 32 from by bv_addr]; exact hc8)
    (by simp only [signExtend12_36]; exact hv36)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_36, signExtend12_4] at L1
  rw [show (base + 12) + 24 = base + 36 from by bv_addr] at L1
  have L1f := cpsTriple_frame_left code (base + 12) (base + 36) _ _
    ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L1
  -- Set up borrow chain abbreviations
  let borrow0_val := (if BitVec.ult b0 a0 then (1 : Word) else 0)
  let temp1_val := b1 - a1
  let borrow1a_val := (if BitVec.ult b1 a1 then (1 : Word) else 0)
  let borrow1b_val := (if BitVec.ult temp1_val borrow0_val then (1 : Word) else 0)
  let borrow1_val := borrow1a_val ||| borrow1b_val
  -- ========== Limb 2: off_a=40=b2, off_b=8=a2 ==========
  have L2 := lt_limb_carry_spec code 40 8 sp b2 a2
    temp1_val borrow1b_val borrow1_val borrow1a_val (base + 36)
    hc9
    (by rw [show (base + 36) + 4 = base + 40 from by bv_addr]; exact hc10)
    (by rw [show (base + 36) + 8 = base + 44 from by bv_addr]; exact hc11)
    (by rw [show (base + 36) + 12 = base + 48 from by bv_addr]; exact hc12)
    (by rw [show (base + 36) + 16 = base + 52 from by bv_addr]; exact hc13)
    (by rw [show (base + 36) + 20 = base + 56 from by bv_addr]; exact hc14)
    (by simp only [signExtend12_40]; exact hv40)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_40, signExtend12_8] at L2
  rw [show (base + 36) + 24 = base + 60 from by bv_addr] at L2
  have L2f := cpsTriple_frame_left code (base + 36) (base + 60) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) **
     ((sp + 44) ↦ₘ b3) ** ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) **
     ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L2
  -- ========== Limb 3: off_a=44=b3, off_b=12=a3 ==========
  let temp2_val := b2 - a2
  let borrow2a_val := (if BitVec.ult b2 a2 then (1 : Word) else 0)
  let borrow2b_val := (if BitVec.ult temp2_val borrow1_val then (1 : Word) else 0)
  let borrow2_val := borrow2a_val ||| borrow2b_val
  have L3 := lt_limb_carry_spec code 44 12 sp b3 a3
    temp2_val borrow2b_val borrow2_val borrow2a_val (base + 60)
    hc15
    (by rw [show (base + 60) + 4 = base + 64 from by bv_addr]; exact hc16)
    (by rw [show (base + 60) + 8 = base + 68 from by bv_addr]; exact hc17)
    (by rw [show (base + 60) + 12 = base + 72 from by bv_addr]; exact hc18)
    (by rw [show (base + 60) + 16 = base + 76 from by bv_addr]; exact hc19)
    (by rw [show (base + 60) + 20 = base + 80 from by bv_addr]; exact hc20)
    (by simp only [signExtend12_44]; exact hv44)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_44, signExtend12_12] at L3
  rw [show (base + 60) + 24 = base + 84 from by bv_addr] at L3
  have L3f := cpsTriple_frame_left code (base + 60) (base + 84) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L3
  -- ========== Limb 4: off_a=48=b4, off_b=16=a4 ==========
  let temp3_val := b3 - a3
  let borrow3a_val := (if BitVec.ult b3 a3 then (1 : Word) else 0)
  let borrow3b_val := (if BitVec.ult temp3_val borrow2_val then (1 : Word) else 0)
  let borrow3_val := borrow3a_val ||| borrow3b_val
  have L4 := lt_limb_carry_spec code 48 16 sp b4 a4
    temp3_val borrow3b_val borrow3_val borrow3a_val (base + 84)
    hc21
    (by rw [show (base + 84) + 4 = base + 88 from by bv_addr]; exact hc22)
    (by rw [show (base + 84) + 8 = base + 92 from by bv_addr]; exact hc23)
    (by rw [show (base + 84) + 12 = base + 96 from by bv_addr]; exact hc24)
    (by rw [show (base + 84) + 16 = base + 100 from by bv_addr]; exact hc25)
    (by rw [show (base + 84) + 20 = base + 104 from by bv_addr]; exact hc26)
    (by simp only [signExtend12_48]; exact hv48)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_48, signExtend12_16] at L4
  rw [show (base + 84) + 24 = base + 108 from by bv_addr] at L4
  have L4f := cpsTriple_frame_left code (base + 84) (base + 108) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L4
  -- ========== Limb 5: off_a=52=b5, off_b=20=a5 ==========
  let temp4_val := b4 - a4
  let borrow4a_val := (if BitVec.ult b4 a4 then (1 : Word) else 0)
  let borrow4b_val := (if BitVec.ult temp4_val borrow3_val then (1 : Word) else 0)
  let borrow4_val := borrow4a_val ||| borrow4b_val
  have L5 := lt_limb_carry_spec code 52 20 sp b5 a5
    temp4_val borrow4b_val borrow4_val borrow4a_val (base + 108)
    hc27
    (by rw [show (base + 108) + 4 = base + 112 from by bv_addr]; exact hc28)
    (by rw [show (base + 108) + 8 = base + 116 from by bv_addr]; exact hc29)
    (by rw [show (base + 108) + 12 = base + 120 from by bv_addr]; exact hc30)
    (by rw [show (base + 108) + 16 = base + 124 from by bv_addr]; exact hc31)
    (by rw [show (base + 108) + 20 = base + 128 from by bv_addr]; exact hc32)
    (by simp only [signExtend12_52]; exact hv52)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_52, signExtend12_20] at L5
  rw [show (base + 108) + 24 = base + 132 from by bv_addr] at L5
  have L5f := cpsTriple_frame_left code (base + 108) (base + 132) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L5
  -- ========== Limb 6: off_a=56=b6, off_b=24=a6 ==========
  let temp5_val := b5 - a5
  let borrow5a_val := (if BitVec.ult b5 a5 then (1 : Word) else 0)
  let borrow5b_val := (if BitVec.ult temp5_val borrow4_val then (1 : Word) else 0)
  let borrow5_val := borrow5a_val ||| borrow5b_val
  have L6 := lt_limb_carry_spec code 56 24 sp b6 a6
    temp5_val borrow5b_val borrow5_val borrow5a_val (base + 132)
    hc33
    (by rw [show (base + 132) + 4 = base + 136 from by bv_addr]; exact hc34)
    (by rw [show (base + 132) + 8 = base + 140 from by bv_addr]; exact hc35)
    (by rw [show (base + 132) + 12 = base + 144 from by bv_addr]; exact hc36)
    (by rw [show (base + 132) + 16 = base + 148 from by bv_addr]; exact hc37)
    (by rw [show (base + 132) + 20 = base + 152 from by bv_addr]; exact hc38)
    (by simp only [signExtend12_56]; exact hv56)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_56, signExtend12_24] at L6
  rw [show (base + 132) + 24 = base + 156 from by bv_addr] at L6
  have L6f := cpsTriple_frame_left code (base + 132) (base + 156) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L6
  -- ========== Limb 7: off_a=60=b7, off_b=28=a7 ==========
  let temp6_val := b6 - a6
  let borrow6a_val := (if BitVec.ult b6 a6 then (1 : Word) else 0)
  let borrow6b_val := (if BitVec.ult temp6_val borrow5_val then (1 : Word) else 0)
  let borrow6_val := borrow6a_val ||| borrow6b_val
  have L7 := lt_limb_carry_spec code 60 28 sp b7 a7
    temp6_val borrow6b_val borrow6_val borrow6a_val (base + 156)
    hc39
    (by rw [show (base + 156) + 4 = base + 160 from by bv_addr]; exact hc40)
    (by rw [show (base + 156) + 8 = base + 164 from by bv_addr]; exact hc41)
    (by rw [show (base + 156) + 12 = base + 168 from by bv_addr]; exact hc42)
    (by rw [show (base + 156) + 16 = base + 172 from by bv_addr]; exact hc43)
    (by rw [show (base + 156) + 20 = base + 176 from by bv_addr]; exact hc44)
    (by simp only [signExtend12_60]; exact hv60)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_60, signExtend12_28] at L7
  rw [show (base + 156) + 24 = base + 180 from by bv_addr] at L7
  have L7f := cpsTriple_frame_left code (base + 156) (base + 180) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6))
    pcFree14 L7
  -- ========== Store phase (base+180 → base+216) ==========
  let temp7_val := b7 - a7
  let borrow7a_val := (if BitVec.ult b7 a7 then (1 : Word) else 0)
  let borrow7b_val := (if BitVec.ult temp7_val borrow6_val then (1 : Word) else 0)
  let borrow7_val := borrow7a_val ||| borrow7b_val
  have LS := lt_result_store_spec code sp borrow7_val temp7_val borrow7b_val borrow7a_val
    b0 b1 b2 b3 b4 b5 b6 b7 (base + 180)
    hc45
    (by rw [show (base + 180) + 4 = base + 184 from by bv_addr]; exact hc46)
    (by rw [show (base + 180) + 8 = base + 188 from by bv_addr]; exact hc47)
    (by rw [show (base + 180) + 12 = base + 192 from by bv_addr]; exact hc48)
    (by rw [show (base + 180) + 16 = base + 196 from by bv_addr]; exact hc49)
    (by rw [show (base + 180) + 20 = base + 200 from by bv_addr]; exact hc50)
    (by rw [show (base + 180) + 24 = base + 204 from by bv_addr]; exact hc51)
    (by rw [show (base + 180) + 28 = base + 208 from by bv_addr]; exact hc52)
    (by rw [show (base + 180) + 32 = base + 212 from by bv_addr]; exact hc53)
    hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  rw [show (base + 180) + 36 = base + 216 from by bv_addr] at LS
  have LSf := cpsTriple_frame_left code (base + 180) (base + 216) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree8 LS
  -- ========== Compose all phases ==========
  clear hse0 hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28 hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14
  clear hc15 hc16 hc17 hc18 hc19 hc20 hc21 hc22 hc23 hc24 hc25 hc26
  clear hc27 hc28 hc29 hc30 hc31 hc32 hc33 hc34 hc35 hc36 hc37 hc38
  clear hc39 hc40 hc41 hc42 hc43 hc44 hc45 hc46 hc47 hc48 hc49 hc50 hc51 hc52 hc53
  clear L0 L1 L2 L3 L4 L5 L6 L7 LS
  have c01 := cpsTriple_seq_with_perm code base (base + 12) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) L0f L1f
  clear L0f L1f
  have c012 := cpsTriple_seq_with_perm code base (base + 36) (base + 60) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 L2f
  clear c01 L2f
  have c0123 := cpsTriple_seq_with_perm code base (base + 60) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012 L3f
  clear c012 L3f
  have c01234 := cpsTriple_seq_with_perm code base (base + 84) (base + 108) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123 L4f
  clear c0123 L4f
  have c012345 := cpsTriple_seq_with_perm code base (base + 108) (base + 132) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234 L5f
  clear c01234 L5f
  have c0123456 := cpsTriple_seq_with_perm code base (base + 132) (base + 156) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345 L6f
  clear c012345 L6f
  have c01234567 := cpsTriple_seq_with_perm code base (base + 156) (base + 180) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123456 L7f
  clear c0123456 L7f
  have cfull := cpsTriple_seq_with_perm code base (base + 180) (base + 216) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234567 LSf
  clear c01234567 LSf
  exact cpsTriple_consequence code base (base + 216) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

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
theorem eq_result_store_spec (code : CodeMem) (sp : Addr)
    (acc v6 v5 v11 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word) (base : Addr)
    -- SLTIU x7, x7, 1 (convert acc to boolean)
    (hc0 : code base = some (.SLTIU .x7 .x7 1))
    -- ADDI x12, x12, 32
    (hc1 : code (base + 4) = some (.ADDI .x12 .x12 32))
    -- SW x12, x7, 0 (store eq_result)
    (hc2 : code (base + 8) = some (.SW .x12 .x7 0))
    -- SW x12, x0, 4..28 (store zeros)
    (hc3 : code (base + 12) = some (.SW .x12 .x0 4))
    (hc4 : code (base + 16) = some (.SW .x12 .x0 8))
    (hc5 : code (base + 20) = some (.SW .x12 .x0 12))
    (hc6 : code (base + 24) = some (.SW .x12 .x0 16))
    (hc7 : code (base + 28) = some (.SW .x12 .x0 20))
    (hc8 : code (base + 32) = some (.SW .x12 .x0 24))
    (hc9 : code (base + 36) = some (.SW .x12 .x0 28))
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
    cpsTriple code base (base + 40)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ acc) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
       ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
       ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
       ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0) ** ((sp + 60) ↦ₘ 0)) := by
  simp only
  -- Step SLT: SLTIU x7, x7, 1 (base → base+4)
  have SLT := sltiu_spec_gen_same code .x7 acc 1 base (by nofun) hc0
  simp only [signExtend12_1] at SLT
  rw [show base + 4 = base + 4 from rfl] at SLT
  have SLTf := cpsTriple_frame_left code base (base + 4) _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFreeAddi12 SLT
  -- Step LA: ADDI x12, x12, 32 (base+4 → base+8)
  have LA := addi_spec_gen_same code .x12 sp 32 (base + 4) (by nofun) hc1
  simp only [signExtend12_32] at LA
  rw [show (base + 4) + 4 = base + 8 from by bv_addr] at LA
  have LAf := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFreeAddi12 LA
  -- Step S0: SW x12, x7, 0 — mem[sp+32] := eq_result (base+8 → base+12)
  have S0 := sw_spec_gen code .x12 .x7 (sp + 32)
    (if BitVec.ult acc (1 : Word) then (1 : Word) else 0) b0 0 (base + 8) hc2
    (by simp only [signExtend12_0]; rw [show (sp + 32 : Addr) + 0 = sp + 32 from by bv_addr]; exact hv32)
  simp only [signExtend12_0] at S0
  rw [show (sp + 32) + 0 = sp + 32 from by bv_addr,
      show (base + 8) + 4 = base + 12 from by bv_addr] at S0
  have S0f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _)))))))))) S0
  -- Step S1: SW x12, x0, 4 — mem[sp+36] := 0 (base+12 → base+16)
  have S1 := sw_x0_spec_gen code .x12 (sp + 32) b1 4 (base + 12) hc3
    (by simp only [signExtend12_4]; rw [show (sp + 32) + 4 = sp + 36 from by bv_addr]; exact hv36)
  simp only [signExtend12_4] at S1
  rw [show (sp + 32) + 4 = sp + 36 from by bv_addr,
      show (base + 12) + 4 = base + 16 from by bv_addr] at S1
  have S1f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S1
  -- Step S2: SW x12, x0, 8 — mem[sp+40] := 0 (base+16 → base+20)
  have S2 := sw_x0_spec_gen code .x12 (sp + 32) b2 8 (base + 16) hc4
    (by simp only [signExtend12_8]; rw [show (sp + 32) + 8 = sp + 40 from by bv_addr]; exact hv40)
  simp only [signExtend12_8] at S2
  rw [show (sp + 32) + 8 = sp + 40 from by bv_addr,
      show (base + 16) + 4 = base + 20 from by bv_addr] at S2
  have S2f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S2
  -- Step S3: SW x12, x0, 12 — mem[sp+44] := 0 (base+20 → base+24)
  have S3 := sw_x0_spec_gen code .x12 (sp + 32) b3 12 (base + 20) hc5
    (by simp only [signExtend12_12]; rw [show (sp + 32) + 12 = sp + 44 from by bv_addr]; exact hv44)
  simp only [signExtend12_12] at S3
  rw [show (sp + 32) + 12 = sp + 44 from by bv_addr,
      show (base + 20) + 4 = base + 24 from by bv_addr] at S3
  have S3f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S3
  -- Step S4: SW x12, x0, 16 — mem[sp+48] := 0 (base+24 → base+28)
  have S4 := sw_x0_spec_gen code .x12 (sp + 32) b4 16 (base + 24) hc6
    (by simp only [signExtend12_16]; rw [show (sp + 32) + 16 = sp + 48 from by bv_addr]; exact hv48)
  simp only [signExtend12_16] at S4
  rw [show (sp + 32) + 16 = sp + 48 from by bv_addr,
      show (base + 24) + 4 = base + 28 from by bv_addr] at S4
  have S4f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S4
  -- Step S5: SW x12, x0, 20 — mem[sp+52] := 0 (base+28 → base+32)
  have S5 := sw_x0_spec_gen code .x12 (sp + 32) b5 20 (base + 28) hc7
    (by simp only [signExtend12_20]; rw [show (sp + 32) + 20 = sp + 52 from by bv_addr]; exact hv52)
  simp only [signExtend12_20] at S5
  rw [show (sp + 32) + 20 = sp + 52 from by bv_addr,
      show (base + 28) + 4 = base + 32 from by bv_addr] at S5
  have S5f := cpsTriple_frame_left code (base + 28) (base + 32) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S5
  -- Step S6: SW x12, x0, 24 — mem[sp+56] := 0 (base+32 → base+36)
  have S6 := sw_x0_spec_gen code .x12 (sp + 32) b6 24 (base + 32) hc8
    (by simp only [signExtend12_24]; rw [show (sp + 32) + 24 = sp + 56 from by bv_addr]; exact hv56)
  simp only [signExtend12_24] at S6
  rw [show (sp + 32) + 24 = sp + 56 from by bv_addr,
      show (base + 32) + 4 = base + 36 from by bv_addr] at S6
  have S6f := cpsTriple_frame_left code (base + 32) (base + 36) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 60) ↦ₘ b7))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S6
  -- Step S7: SW x12, x0, 28 — mem[sp+60] := 0 (base+36 → base+40)
  have S7 := sw_x0_spec_gen code .x12 (sp + 32) b7 28 (base + 36) hc9
    (by simp only [signExtend12_28]; rw [show (sp + 32) + 28 = sp + 60 from by bv_addr]; exact hv60)
  simp only [signExtend12_28] at S7
  rw [show (sp + 32) + 28 = sp + 60 from by bv_addr,
      show (base + 36) + 4 = base + 40 from by bv_addr] at S7
  have S7f := cpsTriple_frame_left code (base + 36) (base + 40) _ _
    ((.x7 ↦ᵣ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 32) ↦ₘ (if BitVec.ult acc (1 : Word) then (1 : Word) else 0)) **
     ((sp + 36) ↦ₘ 0) ** ((sp + 40) ↦ₘ 0) ** ((sp + 44) ↦ₘ 0) **
     ((sp + 48) ↦ₘ 0) ** ((sp + 52) ↦ₘ 0) ** ((sp + 56) ↦ₘ 0))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
     (pcFree_memIs _ _))))))))))) S7
  -- Compose all 10 steps
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9
  clear hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear SLT LA S0 S1 S2 S3 S4 S5 S6 S7
  have c01 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) SLTf LAf
  clear SLTf LAf
  have c012 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 S0f
  clear c01 S0f
  have c0123 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012 S1f
  clear c012 S1f
  have c01234 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123 S2f
  clear c0123 S2f
  have c012345 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234 S3f
  clear c01234 S3f
  have c0123456 := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345 S4f
  clear c012345 S4f
  have c01234567 := cpsTriple_seq_with_perm code base (base + 28) (base + 32) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123456 S5f
  clear c0123456 S5f
  have c012345678 := cpsTriple_seq_with_perm code base (base + 32) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234567 S6f
  clear c01234567 S6f
  have cfull := cpsTriple_seq_with_perm code base (base + 36) (base + 40) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345678 S7f
  clear c012345678 S7f
  exact cpsTriple_consequence code base (base + 40) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Full 256-bit EQ spec
-- ============================================================================

/-- Full 256-bit EVM EQ: EQ(a, b) = 1 iff a == b (as 256-bit unsigned integers).
    Computed by XOR-ing each limb pair, OR-reducing, then SLTIU to boolean.
    Pops 2 stack words (A at sp+0..sp+28, B at sp+32..sp+60),
    writes result (0 or 1) to sp+32..sp+60, advances sp by 32.
    41 instructions = 164 bytes total. -/
theorem evm_eq_spec (code : CodeMem) (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Limb 0 code (3 instructions)
    (hc0 : code base = some (.LW .x7 .x12 0))
    (hc1 : code (base + 4) = some (.LW .x6 .x12 32))
    (hc2 : code (base + 8) = some (.XOR .x7 .x7 .x6))
    -- Limb 1 code (4 instructions)
    (hc3 : code (base + 12) = some (.LW .x6 .x12 4))
    (hc4 : code (base + 16) = some (.LW .x5 .x12 36))
    (hc5 : code (base + 20) = some (.XOR .x6 .x6 .x5))
    (hc6 : code (base + 24) = some (.OR .x7 .x7 .x6))
    -- Limb 2 code (4 instructions)
    (hc7  : code (base + 28) = some (.LW .x6 .x12 8))
    (hc8  : code (base + 32) = some (.LW .x5 .x12 40))
    (hc9  : code (base + 36) = some (.XOR .x6 .x6 .x5))
    (hc10 : code (base + 40) = some (.OR .x7 .x7 .x6))
    -- Limb 3 code (4 instructions)
    (hc11 : code (base + 44) = some (.LW .x6 .x12 12))
    (hc12 : code (base + 48) = some (.LW .x5 .x12 44))
    (hc13 : code (base + 52) = some (.XOR .x6 .x6 .x5))
    (hc14 : code (base + 56) = some (.OR .x7 .x7 .x6))
    -- Limb 4 code (4 instructions)
    (hc15 : code (base + 60) = some (.LW .x6 .x12 16))
    (hc16 : code (base + 64) = some (.LW .x5 .x12 48))
    (hc17 : code (base + 68) = some (.XOR .x6 .x6 .x5))
    (hc18 : code (base + 72) = some (.OR .x7 .x7 .x6))
    -- Limb 5 code (4 instructions)
    (hc19 : code (base + 76) = some (.LW .x6 .x12 20))
    (hc20 : code (base + 80) = some (.LW .x5 .x12 52))
    (hc21 : code (base + 84) = some (.XOR .x6 .x6 .x5))
    (hc22 : code (base + 88) = some (.OR .x7 .x7 .x6))
    -- Limb 6 code (4 instructions)
    (hc23 : code (base + 92) = some (.LW .x6 .x12 24))
    (hc24 : code (base + 96) = some (.LW .x5 .x12 56))
    (hc25 : code (base + 100) = some (.XOR .x6 .x6 .x5))
    (hc26 : code (base + 104) = some (.OR .x7 .x7 .x6))
    -- Limb 7 code (4 instructions)
    (hc27 : code (base + 108) = some (.LW .x6 .x12 28))
    (hc28 : code (base + 112) = some (.LW .x5 .x12 60))
    (hc29 : code (base + 116) = some (.XOR .x6 .x6 .x5))
    (hc30 : code (base + 120) = some (.OR .x7 .x7 .x6))
    -- Store phase (10 instructions)
    (hc31 : code (base + 124) = some (.SLTIU .x7 .x7 1))
    (hc32 : code (base + 128) = some (.ADDI .x12 .x12 32))
    (hc33 : code (base + 132) = some (.SW .x12 .x7 0))
    (hc34 : code (base + 136) = some (.SW .x12 .x0 4))
    (hc35 : code (base + 140) = some (.SW .x12 .x0 8))
    (hc36 : code (base + 144) = some (.SW .x12 .x0 12))
    (hc37 : code (base + 148) = some (.SW .x12 .x0 16))
    (hc38 : code (base + 152) = some (.SW .x12 .x0 20))
    (hc39 : code (base + 156) = some (.SW .x12 .x0 24))
    (hc40 : code (base + 160) = some (.SW .x12 .x0 28))
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
    cpsTriple code base (base + 164)
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
  simp only
  have hse0 : sp + signExtend12 (0 : BitVec 12) = sp := se0_eq_self sp
  -- ========== Limb 0: eq_limb0_spec (off_a=0=a0, off_b=32=b0) ==========
  have L0 := eq_limb0_spec code 0 32 sp a0 b0 v7 v6 base hc0 hc1 hc2
    (by rw [hse0]; exact hv0)
    (by simp only [signExtend12_32]; exact hv32)
  simp only [signExtend12_32] at L0; rw [hse0] at L0
  rw [show base + 12 = base + 12 from rfl] at L0
  have L0f := cpsTriple_frame_left code base (base + 12) _ _
    ((.x5 ↦ᵣ v5) ** (.x11 ↦ᵣ v11) **
     ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree16eq0 L0
  -- ========== Limb 1: eq_or_limb_spec (off_a=4=a1, off_b=36=b1) ==========
  let acc0_val := a0 ^^^ b0
  have L1 := eq_or_limb_spec code 4 36 sp a1 b1 b0 v5 acc0_val (base + 12)
    hc3
    (by rw [show (base + 12) + 4 = base + 16 from by bv_addr]; exact hc4)
    (by rw [show (base + 12) + 8 = base + 20 from by bv_addr]; exact hc5)
    (by rw [show (base + 12) + 12 = base + 24 from by bv_addr]; exact hc6)
    (by simp only [signExtend12_4]; exact hv4)
    (by simp only [signExtend12_36]; exact hv36)
  simp only [signExtend12_4, signExtend12_36] at L1
  rw [show (base + 12) + 16 = base + 28 from by bv_addr] at L1
  have L1f := cpsTriple_frame_left code (base + 12) (base + 28) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L1
  -- ========== Limb 2: off_a=8=a2, off_b=40=b2 ==========
  let acc1_val := acc0_val ||| (a1 ^^^ b1)
  have L2 := eq_or_limb_spec code 8 40 sp a2 b2 (a1 ^^^ b1) b1 acc1_val (base + 28)
    hc7
    (by rw [show (base + 28) + 4 = base + 32 from by bv_addr]; exact hc8)
    (by rw [show (base + 28) + 8 = base + 36 from by bv_addr]; exact hc9)
    (by rw [show (base + 28) + 12 = base + 40 from by bv_addr]; exact hc10)
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_40]; exact hv40)
  simp only [signExtend12_8, signExtend12_40] at L2
  rw [show (base + 28) + 16 = base + 44 from by bv_addr] at L2
  have L2f := cpsTriple_frame_left code (base + 28) (base + 44) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) **
     ((sp + 44) ↦ₘ b3) ** ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) **
     ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L2
  -- ========== Limb 3: off_a=12=a3, off_b=44=b3 ==========
  let acc2_val := acc1_val ||| (a2 ^^^ b2)
  have L3 := eq_or_limb_spec code 12 44 sp a3 b3 (a2 ^^^ b2) b2 acc2_val (base + 44)
    hc11
    (by rw [show (base + 44) + 4 = base + 48 from by bv_addr]; exact hc12)
    (by rw [show (base + 44) + 8 = base + 52 from by bv_addr]; exact hc13)
    (by rw [show (base + 44) + 12 = base + 56 from by bv_addr]; exact hc14)
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_44]; exact hv44)
  simp only [signExtend12_12, signExtend12_44] at L3
  rw [show (base + 44) + 16 = base + 60 from by bv_addr] at L3
  have L3f := cpsTriple_frame_left code (base + 44) (base + 60) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L3
  -- ========== Limb 4: off_a=16=a4, off_b=48=b4 ==========
  let acc3_val := acc2_val ||| (a3 ^^^ b3)
  have L4 := eq_or_limb_spec code 16 48 sp a4 b4 (a3 ^^^ b3) b3 acc3_val (base + 60)
    hc15
    (by rw [show (base + 60) + 4 = base + 64 from by bv_addr]; exact hc16)
    (by rw [show (base + 60) + 8 = base + 68 from by bv_addr]; exact hc17)
    (by rw [show (base + 60) + 12 = base + 72 from by bv_addr]; exact hc18)
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_48]; exact hv48)
  simp only [signExtend12_16, signExtend12_48] at L4
  rw [show (base + 60) + 16 = base + 76 from by bv_addr] at L4
  have L4f := cpsTriple_frame_left code (base + 60) (base + 76) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L4
  -- ========== Limb 5: off_a=20=a5, off_b=52=b5 ==========
  let acc4_val := acc3_val ||| (a4 ^^^ b4)
  have L5 := eq_or_limb_spec code 20 52 sp a5 b5 (a4 ^^^ b4) b4 acc4_val (base + 76)
    hc19
    (by rw [show (base + 76) + 4 = base + 80 from by bv_addr]; exact hc20)
    (by rw [show (base + 76) + 8 = base + 84 from by bv_addr]; exact hc21)
    (by rw [show (base + 76) + 12 = base + 88 from by bv_addr]; exact hc22)
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_52]; exact hv52)
  simp only [signExtend12_20, signExtend12_52] at L5
  rw [show (base + 76) + 16 = base + 92 from by bv_addr] at L5
  have L5f := cpsTriple_frame_left code (base + 76) (base + 92) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L5
  -- ========== Limb 6: off_a=24=a6, off_b=56=b6 ==========
  let acc5_val := acc4_val ||| (a5 ^^^ b5)
  have L6 := eq_or_limb_spec code 24 56 sp a6 b6 (a5 ^^^ b5) b5 acc5_val (base + 92)
    hc23
    (by rw [show (base + 92) + 4 = base + 96 from by bv_addr]; exact hc24)
    (by rw [show (base + 92) + 8 = base + 100 from by bv_addr]; exact hc25)
    (by rw [show (base + 92) + 12 = base + 104 from by bv_addr]; exact hc26)
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_56]; exact hv56)
  simp only [signExtend12_24, signExtend12_56] at L6
  rw [show (base + 92) + 16 = base + 108 from by bv_addr] at L6
  have L6f := cpsTriple_frame_left code (base + 92) (base + 108) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L6
  -- ========== Limb 7: off_a=28=a7, off_b=60=b7 ==========
  let acc6_val := acc5_val ||| (a6 ^^^ b6)
  have L7 := eq_or_limb_spec code 28 60 sp a7 b7 (a6 ^^^ b6) b6 acc6_val (base + 108)
    hc27
    (by rw [show (base + 108) + 4 = base + 112 from by bv_addr]; exact hc28)
    (by rw [show (base + 108) + 8 = base + 116 from by bv_addr]; exact hc29)
    (by rw [show (base + 108) + 12 = base + 120 from by bv_addr]; exact hc30)
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_60]; exact hv60)
  simp only [signExtend12_28, signExtend12_60] at L7
  rw [show (base + 108) + 16 = base + 124 from by bv_addr] at L7
  have L7f := cpsTriple_frame_left code (base + 108) (base + 124) _ _
    ((.x11 ↦ᵣ v11) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6))
    pcFree15 L7
  -- ========== Store phase: eq_result_store_spec (base+124 → base+164) ==========
  let acc7_val := acc6_val ||| (a7 ^^^ b7)
  have LS := eq_result_store_spec code sp acc7_val (a7 ^^^ b7) b7 v11
    b0 b1 b2 b3 b4 b5 b6 b7 (base + 124)
    hc31
    (by rw [show (base + 124) + 4 = base + 128 from by bv_addr]; exact hc32)
    (by rw [show (base + 124) + 8 = base + 132 from by bv_addr]; exact hc33)
    (by rw [show (base + 124) + 12 = base + 136 from by bv_addr]; exact hc34)
    (by rw [show (base + 124) + 16 = base + 140 from by bv_addr]; exact hc35)
    (by rw [show (base + 124) + 20 = base + 144 from by bv_addr]; exact hc36)
    (by rw [show (base + 124) + 24 = base + 148 from by bv_addr]; exact hc37)
    (by rw [show (base + 124) + 28 = base + 152 from by bv_addr]; exact hc38)
    (by rw [show (base + 124) + 32 = base + 156 from by bv_addr]; exact hc39)
    (by rw [show (base + 124) + 36 = base + 160 from by bv_addr]; exact hc40)
    hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  simp only at LS
  rw [show (base + 124) + 40 = base + 164 from by bv_addr] at LS
  have LSf := cpsTriple_frame_left code (base + 124) (base + 164) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7))
    pcFree8 LS
  -- ========== Compose all phases ==========
  clear hse0 hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28 hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10
  clear hc11 hc12 hc13 hc14 hc15 hc16 hc17 hc18 hc19 hc20
  clear hc21 hc22 hc23 hc24 hc25 hc26 hc27 hc28 hc29 hc30
  clear hc31 hc32 hc33 hc34 hc35 hc36 hc37 hc38 hc39 hc40
  clear L0 L1 L2 L3 L4 L5 L6 L7 LS
  have c01 := cpsTriple_seq_with_perm code base (base + 12) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) L0f L1f
  clear L0f L1f
  have c012 := cpsTriple_seq_with_perm code base (base + 28) (base + 44) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 L2f
  clear c01 L2f
  have c0123 := cpsTriple_seq_with_perm code base (base + 44) (base + 60) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012 L3f
  clear c012 L3f
  have c01234 := cpsTriple_seq_with_perm code base (base + 60) (base + 76) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123 L4f
  clear c0123 L4f
  have c012345 := cpsTriple_seq_with_perm code base (base + 76) (base + 92) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234 L5f
  clear c01234 L5f
  have c0123456 := cpsTriple_seq_with_perm code base (base + 92) (base + 108) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345 L6f
  clear c012345 L6f
  have c01234567 := cpsTriple_seq_with_perm code base (base + 108) (base + 124) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123456 L7f
  clear c0123456 L7f
  have cfull := cpsTriple_seq_with_perm code base (base + 124) (base + 164) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234567 LSf
  clear c01234567 LSf
  exact cpsTriple_consequence code base (base + 164) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

end EvmAsm
