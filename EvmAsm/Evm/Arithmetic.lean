/-
  EvmAsm.Evm.Arithmetic

  256-bit EVM arithmetic operations (ADD, SUB) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory,
  propagating carry/borrow across limbs.
-/

import EvmAsm.Evm.Stack
import EvmAsm.CPSSpec

namespace EvmAsm

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM ADD: binary, pops 2, pushes 1.
    Limb 0: LW, LW, ADD, SLTU (carry), SW (5 instructions).
    Limbs 1-7: LW, LW, ADD, SLTU (carry1), ADD (carry_in), SLTU (carry2), OR (carry_out), SW (8 instructions each).
    Then ADDI sp, sp, 32.
    Registers: x12=sp, x7=acc, x6=operand, x5=carry, x11=carry1. -/
def evm_add : Program :=
  -- Limb 0 (5 instructions): carry detection via SLTU after ADD
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x5 .x7 .x6) ;; SW .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 36 ;;
  -- Limb 2
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 40 ;;
  -- Limb 3
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 44 ;;
  -- Limb 4
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 48 ;;
  -- Limb 5
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 52 ;;
  -- Limb 6
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 56 ;;
  -- Limb 7
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;;
  single (.ADD .x7 .x7 .x6) ;; single (.SLTU .x11 .x7 .x6) ;;
  single (.ADD .x7 .x7 .x5) ;; single (.SLTU .x6 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 60 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

/-- 256-bit EVM SUB: binary, pops 2, pushes 1.
    Limb 0: LW, LW, SLTU (borrow), SUB, SW (5 instructions).
    Limbs 1-7: LW, LW, SLTU (borrow1), SUB, SLTU (borrow2), SUB (borrow_in), OR (borrow_out), SW (8 instructions each).
    Then ADDI sp, sp, 32. -/
def evm_sub : Program :=
  -- Limb 0 (5 instructions): borrow detection via SLTU before SUB
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;;
  single (.SLTU .x5 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 36 ;;
  -- Limb 2
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 40 ;;
  -- Limb 3
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 44 ;;
  -- Limb 4
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 48 ;;
  -- Limb 5
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 52 ;;
  -- Limb 6
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 56 ;;
  -- Limb 7
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SW .x12 .x7 60 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

-- ============================================================================
-- Per-limb Specs: ADD
-- ============================================================================

/-- ADD limb 0 spec (5 instructions): LW, LW, ADD, SLTU, SW.
    Computes sum = a + b (mod 2^32) and carry = (sum < b ? 1 : 0). -/
theorem add_limb0_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.ADD .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SLTU .x5 .x7 .x6))
    (hf5 : code (base + 16) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let sum := a_limb + b_limb
    let carry := if BitVec.ult sum b_limb then (1 : Word) else 0
    cpsTriple code base (base + 20)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ sum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ sum)) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1620 : base + 16 + 4 = base + 20 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 1: LW x7, off_a(x12) — x7 := a_limb
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s1
  -- Step 2: LW x6, off_b(x12) — x6 := b_limb
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** (.x5 ↦ᵣ v5) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s2
  -- Step 3: ADD x7, x7, x6 — x7 := a_limb + b_limb
  have s3 := add_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s3
  -- Step 4: SLTU x5, x7, x6 — x5 := carry (3-reg: rd=x5, rs1=x7, rs2=x6)
  have s4 := sltu_spec_gen code .x5 .x7 .x6 v5 (a_limb + b_limb) b_limb (base + 12) (by nofun) hf4
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s4
  -- Step 5: SW x12, x7, off_b — mem_b := sum
  have s5 := sw_spec_gen code .x12 .x7 sp (a_limb + b_limb) b_limb off_b (base + 16) hf5 hvalid_b
  rw [h1620] at s5
  have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ (if BitVec.ult (a_limb + b_limb) b_limb then (1 : Word) else 0)) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s5
  -- Compose all 5 steps
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s4f)
  have c12345 := cpsTriple_seq code base (base + 16) (base + 20) _ _ _ c1234
    (cpsTriple_consequence code (base + 16) (base + 20) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s5f)
  exact cpsTriple_consequence code base (base + 20) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c12345

-- ============================================================================
-- Per-limb Specs: ADD with carry (limbs 1-7)
-- ============================================================================

/-- ADD carry limb phase 1 (4 instructions): LW, LW, ADD, SLTU.
    Loads a_limb and b_limb, computes psum = a + b, carry1 = (psum < b ? 1 : 0). -/
theorem add_limb_carry_spec_phase1 (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.ADD .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SLTU .x11 .x7 .x6))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 1: LW x7, off_a(x12) — x7 := a_limb
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s1
  -- Step 2: LW x6, off_b(x12) — x6 := b_limb
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s2
  -- Step 3: ADD x7, x7, x6 — x7 := a_limb + b_limb
  have s3 := add_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))) s3
  -- Step 4: SLTU x11, x7, x6 — x11 := carry1 (3-reg)
  have s4 := sltu_spec_gen code .x11 .x7 .x6 v11 (a_limb + b_limb) b_limb (base + 12) (by nofun) hf4
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ carry_in) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s4
  -- Compose steps 1-4
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s4f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c1234

/-- ADD carry limb phase 2 (4 instructions): ADD, SLTU, OR, SW.
    Takes psum, carry1, carry_in, computes result = psum + carry_in,
    carry2 = (result < carry_in ? 1 : 0), carry_out = carry1 ||| carry2. -/
theorem add_limb_carry_spec_phase2 (code : CodeMem) (off_b : BitVec 12)
    (sp psum b_limb carry_in carry1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hf5 : code base = some (.ADD .x7 .x7 .x5))
    (hf6 : code (base + 4) = some (.SLTU .x6 .x7 .x5))
    (hf7 : code (base + 8) = some (.OR .x5 .x11 .x6))
    (hf8 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ psum) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 5: ADD x7, x7, x5 — x7 := psum + carry_in
  have s5 := add_spec_gen_rd_eq_rs1 code .x7 .x5 psum carry_in base (by nofun) (by nofun) hf5
  have s5f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ b_limb) **
     (.x11 ↦ᵣ carry1) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))) s5
  -- Step 6: SLTU x6, x7, x5 — x6 := carry2 (3-reg: rd=x6, rs1=x7, rs2=x5)
  have s6 := sltu_spec_gen code .x6 .x7 .x5 b_limb (psum + carry_in) carry_in (base + 4) (by nofun) hf6
  rw [h48] at s6
  have s6f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) **
     (.x11 ↦ᵣ carry1) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s6
  -- Step 7: OR x5, x11, x6 — x5 := carry_out (3-reg: rd=x5, rs1=x11, rs2=x6)
  have s7 := or_spec_gen code .x5 .x11 .x6
    carry_in
    carry1
    (if BitVec.ult (psum + carry_in) carry_in then (1 : Word) else 0)
    (base + 8) (by nofun) hf7
  rw [h812] at s7
  have s7f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (psum + carry_in)) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s7
  -- Step 8: SW x12, x7, off_b — mem_b := result
  have s8 := sw_spec_gen code .x12 .x7 sp (psum + carry_in) b_limb off_b (base + 12) hf8 hvalid_b
  rw [h1216] at s8
  have s8f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ (if BitVec.ult (psum + carry_in) carry_in then (1 : Word) else 0)) **
     (.x5 ↦ᵣ (carry1 |||
               (if BitVec.ult (psum + carry_in) carry_in then (1 : Word) else 0))) **
     (.x11 ↦ᵣ carry1) **
     (mem_a ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s8
  -- Compose steps 5-8
  have c56 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s5f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s6f)
  have c567 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c56
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s7f)
  have c5678 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c567
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s8f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c5678

/-- ADD carry limb spec (8 instructions): LW, LW, ADD, SLTU, ADD, SLTU, OR, SW.
    Takes carry_in, produces carry_out = carry1 ||| carry2 where:
    - partial = a + b, carry1 = (partial < b ? 1 : 0)
    - result = partial + carry_in, carry2 = (result < carry_in ? 1 : 0)
    Composed from phase1 (steps 1-4) and phase2 (steps 5-8). -/
theorem add_limb_carry_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 carry_in v11 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.ADD .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SLTU .x11 .x7 .x6))
    (hf5 : code (base + 16) = some (.ADD .x7 .x7 .x5))
    (hf6 : code (base + 20) = some (.SLTU .x6 .x7 .x5))
    (hf7 : code (base + 24) = some (.OR .x5 .x11 .x6))
    (hf8 : code (base + 28) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let psum := a_limb + b_limb
    let carry1 := if BitVec.ult psum b_limb then (1 : Word) else 0
    let result := psum + carry_in
    let carry2 := if BitVec.ult result carry_in then (1 : Word) else 0
    let carry_out := carry1 ||| carry2
    cpsTriple code base (base + 32)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ carry_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ carry2) ** (.x5 ↦ᵣ carry_out) ** (.x11 ↦ᵣ carry1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  simp only
  -- Address normalization for phase2 base = base + 16
  have h164 : base + 16 + 4 = base + 20 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h168 : base + 16 + 8 = base + 24 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1612 : base + 16 + 12 = base + 28 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1616 : base + 16 + 16 = base + 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have p1 := add_limb_carry_spec_phase1 code off_a off_b sp a_limb b_limb v7 v6 carry_in v11 base
    hf1 hf2 hf3 hf4 hvalid_a hvalid_b
  have p2 := add_limb_carry_spec_phase2 code off_b sp (a_limb + b_limb) b_limb carry_in
    (if BitVec.ult (a_limb + b_limb) b_limb then (1 : Word) else 0) a_limb
    (sp + signExtend12 off_a) (base + 16)
    hf5 (h164 ▸ hf6) (h168 ▸ hf7) (h1612 ▸ hf8) hvalid_b
  rw [h1616] at p2
  exact cpsTriple_seq code base (base + 16) (base + 32) _ _ _ p1 p2

-- ============================================================================
-- Per-limb Specs: SUB
-- ============================================================================

/-- SUB limb 0 spec (5 instructions): LW, LW, SLTU, SUB, SW.
    Computes diff = a - b (mod 2^32) and borrow = (a < b ? 1 : 0). -/
theorem sub_limb0_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 v5 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.SLTU .x5 .x7 .x6))
    (hf4 : code (base + 12) = some (.SUB .x7 .x7 .x6))
    (hf5 : code (base + 16) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let diff := a_limb - b_limb
    cpsTriple code base (base + 20)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ diff) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ diff)) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1620 : base + 16 + 4 = base + 20 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 1: LW x7, off_a(x12)
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ v5) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s1
  -- Step 2: LW x6, off_b(x12)
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** (.x5 ↦ᵣ v5) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s2
  -- Step 3: SLTU x5, x7, x6 — borrow = (a < b) (3-reg)
  have s3 := sltu_spec_gen code .x5 .x7 .x6 v5 a_limb b_limb (base + 8) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s3
  -- Step 4: SUB x7, x7, x6 — diff = a - b
  have s4 := sub_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 12) (by nofun) (by nofun) hf4
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (if BitVec.ult a_limb b_limb then (1 : Word) else 0)) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s4
  -- Step 5: SW x12, x7, off_b
  have s5 := sw_spec_gen code .x12 .x7 sp (a_limb - b_limb) b_limb off_b (base + 16) hf5 hvalid_b
  rw [h1620] at s5
  have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ (if BitVec.ult a_limb b_limb then (1 : Word) else 0)) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _))) s5
  -- Compose
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s4f)
  have c12345 := cpsTriple_seq code base (base + 16) (base + 20) _ _ _ c1234
    (cpsTriple_consequence code (base + 16) (base + 20) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s5f)
  exact cpsTriple_consequence code base (base + 20) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c12345

/-- SUB carry limb phase 1 (4 instructions): LW, LW, SLTU, SUB.
    Loads a_limb and b_limb, computes borrow1 = (a < b ? 1 : 0), temp = a - b. -/
theorem sub_limb_carry_spec_phase1 (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.SLTU .x11 .x7 .x6))
    (hf4 : code (base + 12) = some (.SUB .x7 .x7 .x6))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb)) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 1: LW x7, off_a(x12)
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s1
  -- Step 2: LW x6, off_b(x12)
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s2
  -- Step 3: SLTU x11, x7, x6 — borrow1 = (a < b) (3-reg)
  have s3 := sltu_spec_gen code .x11 .x7 .x6 v11 a_limb b_limb (base + 8) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ borrow_in) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s3
  -- Step 4: SUB x7, x7, x6 — temp = a - b
  have s4 := sub_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 12) (by nofun) (by nofun) hf4
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ borrow_in) **
     (.x11 ↦ᵣ (if BitVec.ult a_limb b_limb then (1 : Word) else 0)) **
     ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))) s4
  -- Compose steps 1-4
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s4f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c1234

/-- SUB carry limb phase 2 (4 instructions): SLTU, SUB, OR, SW.
    Takes temp, borrow1, borrow_in, computes borrow2 = (temp < borrow_in ? 1 : 0),
    result = temp - borrow_in, borrow_out = borrow1 ||| borrow2. -/
theorem sub_limb_carry_spec_phase2 (code : CodeMem) (off_b : BitVec 12)
    (sp temp b_limb borrow_in borrow1 a_limb : Word) (mem_a : Addr) (base : Addr)
    (hf5 : code base = some (.SLTU .x6 .x7 .x5))
    (hf6 : code (base + 4) = some (.SUB .x7 .x7 .x5))
    (hf7 : code (base + 8) = some (.OR .x5 .x11 .x6))
    (hf8 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_b := sp + signExtend12 off_b
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ temp) ** (.x6 ↦ᵣ b_limb) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 5: SLTU x6, x7, x5 — borrow2 = (temp < borrow_in) (3-reg: rd=x6, rs1=x7, rs2=x5)
  have s5 := sltu_spec_gen code .x6 .x7 .x5 b_limb temp borrow_in base (by nofun) hf5
  have s5f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x12 ↦ᵣ sp) **
     (.x11 ↦ᵣ borrow1) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s5
  -- Step 6: SUB x7, x7, x5 — result = temp - borrow_in
  have s6 := sub_spec_gen_rd_eq_rs1 code .x7 .x5 temp borrow_in (base + 4) (by nofun) (by nofun) hf6
  rw [h48] at s6
  have s6f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ (if BitVec.ult temp borrow_in then (1 : Word) else 0)) **
     (.x11 ↦ᵣ borrow1) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))) s6
  -- Step 7: OR x5, x11, x6 — borrow_out (3-reg)
  have s7 := or_spec_gen code .x5 .x11 .x6
    borrow_in
    borrow1
    (if BitVec.ult temp borrow_in then (1 : Word) else 0)
    (base + 8) (by nofun) hf7
  rw [h812] at s7
  have s7f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (temp - borrow_in)) **
     (mem_a ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))) s7
  -- Step 8: SW x12, x7, off_b
  have s8 := sw_spec_gen code .x12 .x7 sp (temp - borrow_in) b_limb off_b (base + 12) hf8 hvalid_b
  rw [h1216] at s8
  have s8f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ (if BitVec.ult temp borrow_in then (1 : Word) else 0)) **
     (.x5 ↦ᵣ (borrow1 |||
               (if BitVec.ult temp borrow_in then (1 : Word) else 0))) **
     (.x11 ↦ᵣ borrow1) **
     (mem_a ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)))) s8
  -- Compose steps 5-8
  have c56 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp) s5f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s6f)
  have c567 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c56
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s7f)
  have c5678 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c567
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp)
      (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) s8f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by exact (congrFun (by ac_rfl : _ = _) _).mpr hp) c5678

/-- SUB carry limb spec (8 instructions): LW, LW, SLTU, SUB, SLTU, SUB, OR, SW.
    Takes borrow_in, produces borrow_out = borrow1 ||| borrow2 where:
    - borrow1 = (a < b ? 1 : 0), temp = a - b
    - borrow2 = (temp < borrow_in ? 1 : 0), result = temp - borrow_in
    Composed from phase1 (steps 1-4) and phase2 (steps 5-8). -/
theorem sub_limb_carry_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 borrow_in v11 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.SLTU .x11 .x7 .x6))
    (hf4 : code (base + 12) = some (.SUB .x7 .x7 .x6))
    (hf5 : code (base + 16) = some (.SLTU .x6 .x7 .x5))
    (hf6 : code (base + 20) = some (.SUB .x7 .x7 .x5))
    (hf7 : code (base + 24) = some (.OR .x5 .x11 .x6))
    (hf8 : code (base + 28) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let borrow1 := if BitVec.ult a_limb b_limb then (1 : Word) else 0
    let temp := a_limb - b_limb
    let borrow2 := if BitVec.ult temp borrow_in then (1 : Word) else 0
    let result := temp - borrow_in
    let borrow_out := borrow1 ||| borrow2
    cpsTriple code base (base + 32)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) ** (.x5 ↦ᵣ borrow_in) ** (.x11 ↦ᵣ v11) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ result) ** (.x6 ↦ᵣ borrow2) ** (.x5 ↦ᵣ borrow_out) ** (.x11 ↦ᵣ borrow1) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ result)) := by
  simp only
  -- Address normalization for phase2 base = base + 16
  have h164 : base + 16 + 4 = base + 20 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h168 : base + 16 + 8 = base + 24 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1612 : base + 16 + 12 = base + 28 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1616 : base + 16 + 16 = base + 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have p1 := sub_limb_carry_spec_phase1 code off_a off_b sp a_limb b_limb v7 v6 borrow_in v11 base
    hf1 hf2 hf3 hf4 hvalid_a hvalid_b
  have p2 := sub_limb_carry_spec_phase2 code off_b sp (a_limb - b_limb) b_limb borrow_in
    (if BitVec.ult a_limb b_limb then (1 : Word) else 0) a_limb
    (sp + signExtend12 off_a) (base + 16)
    hf5 (h164 ▸ hf6) (h168 ▸ hf7) (h1612 ▸ hf8) hvalid_b
  rw [h1616] at p2
  exact cpsTriple_seq code base (base + 16) (base + 32) _ _ _ p1 p2

end EvmAsm
