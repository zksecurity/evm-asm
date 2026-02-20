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
theorem evm_add_spec (code : CodeMem) (sp : Addr) (base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 v5 v11 : Word)
    -- Limb 0 code (base + 0/4/8/12/16)
    (hc0 : code base = some (.LW .x7 .x12 0))
    (hc1 : code (base + 4) = some (.LW .x6 .x12 32))
    (hc2 : code (base + 8) = some (.ADD .x7 .x7 .x6))
    (hc3 : code (base + 12) = some (.SLTU .x5 .x7 .x6))
    (hc4 : code (base + 16) = some (.SW .x12 .x7 32))
    -- Limb 1 code (base + 20/24/28/32/36/40/44/48)
    (hc5 : code (base + 20) = some (.LW .x7 .x12 4))
    (hc6 : code (base + 24) = some (.LW .x6 .x12 36))
    (hc7 : code (base + 28) = some (.ADD .x7 .x7 .x6))
    (hc8 : code (base + 32) = some (.SLTU .x11 .x7 .x6))
    (hc9 : code (base + 36) = some (.ADD .x7 .x7 .x5))
    (hc10 : code (base + 40) = some (.SLTU .x6 .x7 .x5))
    (hc11 : code (base + 44) = some (.OR .x5 .x11 .x6))
    (hc12 : code (base + 48) = some (.SW .x12 .x7 36))
    -- Limb 2 code (base + 52/56/60/64/68/72/76/80)
    (hc13 : code (base + 52) = some (.LW .x7 .x12 8))
    (hc14 : code (base + 56) = some (.LW .x6 .x12 40))
    (hc15 : code (base + 60) = some (.ADD .x7 .x7 .x6))
    (hc16 : code (base + 64) = some (.SLTU .x11 .x7 .x6))
    (hc17 : code (base + 68) = some (.ADD .x7 .x7 .x5))
    (hc18 : code (base + 72) = some (.SLTU .x6 .x7 .x5))
    (hc19 : code (base + 76) = some (.OR .x5 .x11 .x6))
    (hc20 : code (base + 80) = some (.SW .x12 .x7 40))
    -- Limb 3 code (base + 84/88/92/96/100/104/108/112)
    (hc21 : code (base + 84) = some (.LW .x7 .x12 12))
    (hc22 : code (base + 88) = some (.LW .x6 .x12 44))
    (hc23 : code (base + 92) = some (.ADD .x7 .x7 .x6))
    (hc24 : code (base + 96) = some (.SLTU .x11 .x7 .x6))
    (hc25 : code (base + 100) = some (.ADD .x7 .x7 .x5))
    (hc26 : code (base + 104) = some (.SLTU .x6 .x7 .x5))
    (hc27 : code (base + 108) = some (.OR .x5 .x11 .x6))
    (hc28 : code (base + 112) = some (.SW .x12 .x7 44))
    -- Limb 4 code (base + 116/120/124/128/132/136/140/144)
    (hc29 : code (base + 116) = some (.LW .x7 .x12 16))
    (hc30 : code (base + 120) = some (.LW .x6 .x12 48))
    (hc31 : code (base + 124) = some (.ADD .x7 .x7 .x6))
    (hc32 : code (base + 128) = some (.SLTU .x11 .x7 .x6))
    (hc33 : code (base + 132) = some (.ADD .x7 .x7 .x5))
    (hc34 : code (base + 136) = some (.SLTU .x6 .x7 .x5))
    (hc35 : code (base + 140) = some (.OR .x5 .x11 .x6))
    (hc36 : code (base + 144) = some (.SW .x12 .x7 48))
    -- Limb 5 code (base + 148/152/156/160/164/168/172/176)
    (hc37 : code (base + 148) = some (.LW .x7 .x12 20))
    (hc38 : code (base + 152) = some (.LW .x6 .x12 52))
    (hc39 : code (base + 156) = some (.ADD .x7 .x7 .x6))
    (hc40 : code (base + 160) = some (.SLTU .x11 .x7 .x6))
    (hc41 : code (base + 164) = some (.ADD .x7 .x7 .x5))
    (hc42 : code (base + 168) = some (.SLTU .x6 .x7 .x5))
    (hc43 : code (base + 172) = some (.OR .x5 .x11 .x6))
    (hc44 : code (base + 176) = some (.SW .x12 .x7 52))
    -- Limb 6 code (base + 180/184/188/192/196/200/204/208)
    (hc45 : code (base + 180) = some (.LW .x7 .x12 24))
    (hc46 : code (base + 184) = some (.LW .x6 .x12 56))
    (hc47 : code (base + 188) = some (.ADD .x7 .x7 .x6))
    (hc48 : code (base + 192) = some (.SLTU .x11 .x7 .x6))
    (hc49 : code (base + 196) = some (.ADD .x7 .x7 .x5))
    (hc50 : code (base + 200) = some (.SLTU .x6 .x7 .x5))
    (hc51 : code (base + 204) = some (.OR .x5 .x11 .x6))
    (hc52 : code (base + 208) = some (.SW .x12 .x7 56))
    -- Limb 7 code (base + 212/216/220/224/228/232/236/240)
    (hc53 : code (base + 212) = some (.LW .x7 .x12 28))
    (hc54 : code (base + 216) = some (.LW .x6 .x12 60))
    (hc55 : code (base + 220) = some (.ADD .x7 .x7 .x6))
    (hc56 : code (base + 224) = some (.SLTU .x11 .x7 .x6))
    (hc57 : code (base + 228) = some (.ADD .x7 .x7 .x5))
    (hc58 : code (base + 232) = some (.SLTU .x6 .x7 .x5))
    (hc59 : code (base + 236) = some (.OR .x5 .x11 .x6))
    (hc60 : code (base + 240) = some (.SW .x12 .x7 60))
    -- ADDI sp adjustment (base + 244)
    (hc61 : code (base + 244) = some (.ADDI .x12 .x12 32))
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
    cpsTriple code base (base + 248)
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
  simp only
  -- Helper: sp + signExtend12 0 = sp
  have hse0 : sp + signExtend12 (0 : BitVec 12) = sp := by
    simp only [signExtend12_0]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- ========== Limb 0 (5 instr, base to base+20) ==========
  have L0 := add_limb0_spec code 0 32 sp a0 b0 v7 v6 v5 base hc0 hc1 hc2 hc3 hc4
    (by rw [hse0]; exact hv0) (by simp only [signExtend12_32]; exact hv32)
  simp only [signExtend12_32] at L0; rw [hse0] at L0
  have L0f := cpsTriple_frame_left code base (base + 20) _ _
    ((.x11 ↦ᵣ v11) **
     ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree15 L0
  -- ========== Limb 1 (8 instr, base+20 to base+52) ==========
  have L1 := add_limb_carry_spec code 4 36 sp a1 b1 (a0 + b0) b0
    (if BitVec.ult (a0 + b0) b0 then (1 : Word) else 0) v11 (base + 20)
    hc5
    (by rw [show (base + 20) + 4 = base + 24 from by bv_addr]; exact hc6)
    (by rw [show (base + 20) + 8 = base + 28 from by bv_addr]; exact hc7)
    (by rw [show (base + 20) + 12 = base + 32 from by bv_addr]; exact hc8)
    (by rw [show (base + 20) + 16 = base + 36 from by bv_addr]; exact hc9)
    (by rw [show (base + 20) + 20 = base + 40 from by bv_addr]; exact hc10)
    (by rw [show (base + 20) + 24 = base + 44 from by bv_addr]; exact hc11)
    (by rw [show (base + 20) + 28 = base + 48 from by bv_addr]; exact hc12)
    (by simp only [signExtend12_4]; exact hv4) (by simp only [signExtend12_36]; exact hv36)
  simp only [signExtend12_4, signExtend12_36] at L1
  rw [show (base + 20) + 32 = base + 52 from by bv_addr] at L1
  have L1f := cpsTriple_frame_left code (base + 20) (base + 52) _ _
    ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L1
  -- ========== Set up abbreviations for carry chain ==========
  -- We introduce abbreviations early so all limb instantiations can use them.
  -- After simp only, all let bindings in the goal are expanded, so set matches them.
  let carry0_val := (if BitVec.ult (a0 + b0) b0 then (1 : Word) else 0)
  let result1_val := a1 + b1 + carry0_val
  let carry1a_val := (if BitVec.ult (a1 + b1) b1 then (1 : Word) else 0)
  let carry1b_val := (if BitVec.ult result1_val carry0_val then (1 : Word) else 0)
  let carry1_val := carry1a_val ||| carry1b_val
  -- ========== Limb 2 (8 instr, base+52 to base+84) ==========
  -- After limb 1: x7=result1_val, x6=carry1b_val, x5=carry1_val, x11=carry1a_val
  have L2 := add_limb_carry_spec code 8 40 sp a2 b2
    result1_val carry1b_val carry1_val carry1a_val (base + 52)
    hc13
    (by rw [show (base + 52) + 4 = base + 56 from by bv_addr]; exact hc14)
    (by rw [show (base + 52) + 8 = base + 60 from by bv_addr]; exact hc15)
    (by rw [show (base + 52) + 12 = base + 64 from by bv_addr]; exact hc16)
    (by rw [show (base + 52) + 16 = base + 68 from by bv_addr]; exact hc17)
    (by rw [show (base + 52) + 20 = base + 72 from by bv_addr]; exact hc18)
    (by rw [show (base + 52) + 24 = base + 76 from by bv_addr]; exact hc19)
    (by rw [show (base + 52) + 28 = base + 80 from by bv_addr]; exact hc20)
    (by simp only [signExtend12_8]; exact hv8) (by simp only [signExtend12_40]; exact hv40)
  simp only [signExtend12_8, signExtend12_40] at L2
  rw [show (base + 52) + 32 = base + 84 from by bv_addr] at L2
  have L2f := cpsTriple_frame_left code (base + 52) (base + 84) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) **
     ((sp + 36) ↦ₘ result1_val) **
     ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L2
  -- ========== Limb 3 (8 instr, base+84 to base+116) ==========
  let result2_val := a2 + b2 + carry1_val
  let carry2a_val := (if BitVec.ult (a2 + b2) b2 then (1 : Word) else 0)
  let carry2b_val := (if BitVec.ult result2_val carry1_val then (1 : Word) else 0)
  let carry2_val := carry2a_val ||| carry2b_val
  -- After limb 2: x7=result2_val, x6=carry2b_val, x5=carry2_val, x11=carry2a_val
  have L3 := add_limb_carry_spec code 12 44 sp a3 b3
    result2_val carry2b_val carry2_val carry2a_val (base + 84)
    hc21
    (by rw [show (base + 84) + 4 = base + 88 from by bv_addr]; exact hc22)
    (by rw [show (base + 84) + 8 = base + 92 from by bv_addr]; exact hc23)
    (by rw [show (base + 84) + 12 = base + 96 from by bv_addr]; exact hc24)
    (by rw [show (base + 84) + 16 = base + 100 from by bv_addr]; exact hc25)
    (by rw [show (base + 84) + 20 = base + 104 from by bv_addr]; exact hc26)
    (by rw [show (base + 84) + 24 = base + 108 from by bv_addr]; exact hc27)
    (by rw [show (base + 84) + 28 = base + 112 from by bv_addr]; exact hc28)
    (by simp only [signExtend12_12]; exact hv12) (by simp only [signExtend12_44]; exact hv44)
  simp only [signExtend12_12, signExtend12_44] at L3
  rw [show (base + 84) + 32 = base + 116 from by bv_addr] at L3
  have L3f := cpsTriple_frame_left code (base + 84) (base + 116) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) **
     ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L3
  -- ========== Limb 4 (8 instr, base+116 to base+148) ==========
  let result3_val := a3 + b3 + carry2_val
  let carry3a_val := (if BitVec.ult (a3 + b3) b3 then (1 : Word) else 0)
  let carry3b_val := (if BitVec.ult result3_val carry2_val then (1 : Word) else 0)
  let carry3_val := carry3a_val ||| carry3b_val
  -- After limb 3: x7=result3_val, x6=carry3b_val, x5=carry3_val, x11=carry3a_val
  have L4 := add_limb_carry_spec code 16 48 sp a4 b4
    result3_val carry3b_val carry3_val carry3a_val (base + 116)
    hc29
    (by rw [show (base + 116) + 4 = base + 120 from by bv_addr]; exact hc30)
    (by rw [show (base + 116) + 8 = base + 124 from by bv_addr]; exact hc31)
    (by rw [show (base + 116) + 12 = base + 128 from by bv_addr]; exact hc32)
    (by rw [show (base + 116) + 16 = base + 132 from by bv_addr]; exact hc33)
    (by rw [show (base + 116) + 20 = base + 136 from by bv_addr]; exact hc34)
    (by rw [show (base + 116) + 24 = base + 140 from by bv_addr]; exact hc35)
    (by rw [show (base + 116) + 28 = base + 144 from by bv_addr]; exact hc36)
    (by simp only [signExtend12_16]; exact hv16) (by simp only [signExtend12_48]; exact hv48)
  simp only [signExtend12_16, signExtend12_48] at L4
  rw [show (base + 116) + 32 = base + 148 from by bv_addr] at L4
  have L4f := cpsTriple_frame_left code (base + 116) (base + 148) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) **
     ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) ** ((sp + 44) ↦ₘ result3_val) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L4
  -- ========== Limb 5 (8 instr, base+148 to base+180) ==========
  let result4_val := a4 + b4 + carry3_val
  let carry4a_val := (if BitVec.ult (a4 + b4) b4 then (1 : Word) else 0)
  let carry4b_val := (if BitVec.ult result4_val carry3_val then (1 : Word) else 0)
  let carry4_val := carry4a_val ||| carry4b_val
  -- After limb 4: x7=result4_val, x6=carry4b_val, x5=carry4_val, x11=carry4a_val
  have L5 := add_limb_carry_spec code 20 52 sp a5 b5 result4_val carry4b_val carry4_val carry4a_val (base + 148)
    hc37
    (by rw [show (base + 148) + 4 = base + 152 from by bv_addr]; exact hc38)
    (by rw [show (base + 148) + 8 = base + 156 from by bv_addr]; exact hc39)
    (by rw [show (base + 148) + 12 = base + 160 from by bv_addr]; exact hc40)
    (by rw [show (base + 148) + 16 = base + 164 from by bv_addr]; exact hc41)
    (by rw [show (base + 148) + 20 = base + 168 from by bv_addr]; exact hc42)
    (by rw [show (base + 148) + 24 = base + 172 from by bv_addr]; exact hc43)
    (by rw [show (base + 148) + 28 = base + 176 from by bv_addr]; exact hc44)
    (by simp only [signExtend12_20]; exact hv20) (by simp only [signExtend12_52]; exact hv52)
  simp only [signExtend12_20, signExtend12_52] at L5
  rw [show (base + 148) + 32 = base + 180 from by bv_addr] at L5
  have L5f := cpsTriple_frame_left code (base + 148) (base + 180) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) ** ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) ** ((sp + 44) ↦ₘ result3_val) **
     ((sp + 48) ↦ₘ result4_val) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L5
  -- ========== Limb 6 (8 instr, base+180 to base+212) ==========
  let result5_val := a5 + b5 + carry4_val
  let carry5a_val := (if BitVec.ult (a5 + b5) b5 then (1 : Word) else 0)
  let carry5b_val := (if BitVec.ult result5_val carry4_val then (1 : Word) else 0)
  let carry5_val := carry5a_val ||| carry5b_val
  -- After limb 5: x7=result5_val, x6=carry5b_val, x5=carry5_val, x11=carry5a_val
  have L6 := add_limb_carry_spec code 24 56 sp a6 b6 result5_val carry5b_val carry5_val carry5a_val (base + 180)
    hc45
    (by rw [show (base + 180) + 4 = base + 184 from by bv_addr]; exact hc46)
    (by rw [show (base + 180) + 8 = base + 188 from by bv_addr]; exact hc47)
    (by rw [show (base + 180) + 12 = base + 192 from by bv_addr]; exact hc48)
    (by rw [show (base + 180) + 16 = base + 196 from by bv_addr]; exact hc49)
    (by rw [show (base + 180) + 20 = base + 200 from by bv_addr]; exact hc50)
    (by rw [show (base + 180) + 24 = base + 204 from by bv_addr]; exact hc51)
    (by rw [show (base + 180) + 28 = base + 208 from by bv_addr]; exact hc52)
    (by simp only [signExtend12_24]; exact hv24) (by simp only [signExtend12_56]; exact hv56)
  simp only [signExtend12_24, signExtend12_56] at L6
  rw [show (base + 180) + 32 = base + 212 from by bv_addr] at L6
  have L6f := cpsTriple_frame_left code (base + 180) (base + 212) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) ** ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) ** ((sp + 44) ↦ₘ result3_val) **
     ((sp + 48) ↦ₘ result4_val) ** ((sp + 52) ↦ₘ result5_val) ** ((sp + 60) ↦ₘ b7))
    pcFree14 L6
  -- ========== Limb 7 (8 instr, base+212 to base+244) ==========
  let result6_val := a6 + b6 + carry5_val
  let carry6a_val := (if BitVec.ult (a6 + b6) b6 then (1 : Word) else 0)
  let carry6b_val := (if BitVec.ult result6_val carry5_val then (1 : Word) else 0)
  let carry6_val := carry6a_val ||| carry6b_val
  -- After limb 6: x7=result6_val, x6=carry6b_val, x5=carry6_val, x11=carry6a_val
  have L7 := add_limb_carry_spec code 28 60 sp a7 b7 result6_val carry6b_val carry6_val carry6a_val (base + 212)
    hc53
    (by rw [show (base + 212) + 4 = base + 216 from by bv_addr]; exact hc54)
    (by rw [show (base + 212) + 8 = base + 220 from by bv_addr]; exact hc55)
    (by rw [show (base + 212) + 12 = base + 224 from by bv_addr]; exact hc56)
    (by rw [show (base + 212) + 16 = base + 228 from by bv_addr]; exact hc57)
    (by rw [show (base + 212) + 20 = base + 232 from by bv_addr]; exact hc58)
    (by rw [show (base + 212) + 24 = base + 236 from by bv_addr]; exact hc59)
    (by rw [show (base + 212) + 28 = base + 240 from by bv_addr]; exact hc60)
    (by simp only [signExtend12_28]; exact hv28) (by simp only [signExtend12_60]; exact hv60)
  simp only [signExtend12_28, signExtend12_60] at L7
  rw [show (base + 212) + 32 = base + 244 from by bv_addr] at L7
  have L7f := cpsTriple_frame_left code (base + 212) (base + 244) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) **
     ((sp + 32) ↦ₘ (a0 + b0)) ** ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) ** ((sp + 44) ↦ₘ result3_val) **
     ((sp + 48) ↦ₘ result4_val) ** ((sp + 52) ↦ₘ result5_val) ** ((sp + 56) ↦ₘ result6_val))
    pcFree14 L7
  -- ========== ADDI sp adjustment (base+244 to base+248) ==========
  let result7_val := a7 + b7 + carry6_val
  let carry7a_val := (if BitVec.ult (a7 + b7) b7 then (1 : Word) else 0)
  let carry7b_val := (if BitVec.ult result7_val carry6_val then (1 : Word) else 0)
  let carry7_val := carry7a_val ||| carry7b_val
  have LA := addi_spec_gen_same code .x12 sp (32 : BitVec 12) (base + 244) (by nofun) hc61
  simp only [signExtend12_32] at LA
  rw [show (base + 244) + 4 = base + 248 from by bv_addr] at LA
  have LAf := cpsTriple_frame_left code (base + 244) (base + 248) _ _
    ((.x7 ↦ᵣ result7_val) ** (.x6 ↦ᵣ carry7b_val) ** (.x5 ↦ᵣ carry7_val) ** (.x11 ↦ᵣ carry7a_val) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ (a0 + b0)) ** ((sp + 36) ↦ₘ result1_val) **
     ((sp + 40) ↦ₘ result2_val) ** ((sp + 44) ↦ₘ result3_val) **
     ((sp + 48) ↦ₘ result4_val) ** ((sp + 52) ↦ₘ result5_val) **
     ((sp + 56) ↦ₘ result6_val) ** ((sp + 60) ↦ₘ result7_val))
    pcFreeAddi LA
  -- ========== Sequential composition ==========
  -- Using cpsTriple_seq_with_perm to compose specs with midpoint permutation.
  -- Both Q1 (from h1's post) and Q2 (from h2's pre) are fully determined,
  -- so xperm_hyp sees concrete assertion types (no unresolved metavars).
  clear hse0 hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28 hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12
  clear hc13 hc14 hc15 hc16 hc17 hc18 hc19 hc20 hc21 hc22 hc23 hc24
  clear hc25 hc26 hc27 hc28 hc29 hc30 hc31 hc32 hc33 hc34 hc35 hc36
  clear hc37 hc38 hc39 hc40 hc41 hc42 hc43 hc44 hc45 hc46 hc47 hc48
  clear hc49 hc50 hc51 hc52 hc53 hc54 hc55 hc56 hc57 hc58 hc59 hc60 hc61
  clear L0 L1 L2 L3 L4 L5 L6 L7 LA
  have c01 := cpsTriple_seq_with_perm code base (base + 20) (base + 52) _ _ _ _
    (fun _ hp => by xperm_hyp hp) L0f L1f
  clear L0f L1f
  have c012 := cpsTriple_seq_with_perm code base (base + 52) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 L2f
  clear c01 L2f
  have c0123 := cpsTriple_seq_with_perm code base (base + 84) (base + 116) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012 L3f
  clear c012 L3f
  have c01234 := cpsTriple_seq_with_perm code base (base + 116) (base + 148) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123 L4f
  clear c0123 L4f
  have c012345 := cpsTriple_seq_with_perm code base (base + 148) (base + 180) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234 L5f
  clear c01234 L5f
  have c0123456 := cpsTriple_seq_with_perm code base (base + 180) (base + 212) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c012345 L6f
  clear c012345 L6f
  have c01234567 := cpsTriple_seq_with_perm code base (base + 212) (base + 244) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c0123456 L7f
  clear c0123456 L7f
  have cfull := cpsTriple_seq_with_perm code base (base + 244) (base + 248) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01234567 LAf
  clear c01234567 LAf
  exact cpsTriple_consequence code base (base + 248) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

end EvmAsm
