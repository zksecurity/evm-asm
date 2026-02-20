/-
  EvmAsm.Evm.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory.
-/

import EvmAsm.Evm.Stack
import EvmAsm.CPSSpec

namespace EvmAsm

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM AND: binary, pops 2, pushes 1.
    For each of 8 limbs: load A[i] and B[i], AND them, store to B[i].
    Then advance sp by 32. -/
def evm_and : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.AND .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM OR. -/
def evm_or : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.OR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM XOR. -/
def evm_xor : Program :=
  LW .x7 .x12 0 ;; LW .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4 ;; LW .x6 .x12 36 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8 ;; LW .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; single (.XOR .x7 .x7 .x6) ;; SW .x12 .x7 60 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LW .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 0 ;;
  LW .x7 .x12 4 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 4 ;;
  LW .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 8 ;;
  LW .x7 .x12 12 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 12 ;;
  LW .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 16 ;;
  LW .x7 .x12 20 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 20 ;;
  LW .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 24 ;;
  LW .x7 .x12 28 ;; XORI .x7 .x7 (-1) ;; SW .x12 .x7 28

-- ============================================================================
-- Per-limb Specs: Binary Bitwise
-- ============================================================================

/-- Per-limb AND spec (4 instructions).
    Loads A[i] and B[i], computes AND, stores result at B[i]'s location. -/
theorem and_limb_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.AND .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  simp only
  -- Compose from single-instruction specs using cpsTriple_seq + frame + consequence
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
    ((.x6 ↦ᵣ v6) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s1
  -- Step 2: LW x6, off_b(x12) with frame x7, mem_a
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s2
  -- Step 3: AND x7, x7, x6 with frame x12, mem_a, mem_b
  have s3 := and_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s3
  -- Step 4: SW x12, x7, off_b with frame x6, mem_a
  have s4 := sw_spec_gen code .x12 .x7 sp (a_limb &&& b_limb) b_limb off_b (base + 12) hf4 hvalid_b
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ b_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s4
  -- Compose: s1f ; s2f ; s3f ; s4f (with assertion rearrangements)
  -- We use cpsTriple_consequence to permute assertions between steps
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _
    c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _
    c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      s4f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by
      simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by
      simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
    c1234

/-- Per-limb OR spec (4 instructions). -/
theorem or_limb_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.OR .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s1
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s2
  have s3 := or_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s3
  have s4 := sw_spec_gen code .x12 .x7 sp (a_limb ||| b_limb) b_limb off_b (base + 12) hf4 hvalid_b
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ b_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s4
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp) (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s4f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) c1234

/-- Per-limb XOR spec (4 instructions). -/
theorem xor_limb_spec (code : CodeMem) (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.XOR .x7 .x7 .x6))
    (hf4 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1216 : base + 12 + 4 = base + 16 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have s1 := lw_spec_gen code .x7 .x12 sp v7 a_limb off_a base (by nofun) hf1 hvalid_a
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s1
  have s2 := lw_spec_gen code .x6 .x12 sp v6 b_limb off_b (base + 4) (by nofun) hf2 hvalid_b
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s2
  have s3 := xor_spec_gen_rd_eq_rs1 code .x7 .x6 a_limb b_limb (base + 8) (by nofun) (by nofun) hf3
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s3
  have s4 := sw_spec_gen code .x12 .x7 sp (a_limb ^^^ b_limb) b_limb off_b (base + 12) hf4 hvalid_b
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ b_limb) ** ((sp + signExtend12 off_a) ↦ₘ a_limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s4
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp) (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s1f)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s2f)
  have c123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ c12
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s3f)
  have c1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ c123
    (cpsTriple_consequence code (base + 12) (base + 16) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s4f)
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
    (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) c1234

/-- Per-limb NOT spec (3 instructions): LW, XORI with -1, SW.
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (code : CodeMem) (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off))
    (hf2 : code (base + 4) = some (.XORI .x7 .x7 (-1)))
    (hf3 : code (base + 8) = some (.SW .x12 .x7 off))
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h812 : base + 8 + 4 = base + 12 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  -- Step 1: LW x7, off(x12) — x7 := limb
  have s1 := lw_spec_gen code .x7 .x12 sp v7 limb off base (by nofun) hf1 hvalid
  -- Step 2: XORI x7, x7, -1 — x7 := limb XOR signExtend12(-1)
  have s2 := xori_spec_gen_same code .x7 limb (-1) (base + 4) (by nofun) hf2
  rw [h48] at s2
  -- Step 3: SW x12, x7, off — mem[sp + sext(off)] := complemented limb
  let result := limb ^^^ signExtend12 (-1)
  have s3 := sw_spec_gen code .x12 .x7 sp result limb off (base + 8) hf3 hvalid
  rw [h812] at s3
  -- Frame step 1 with nothing extra (already has all 3 conjuncts: x12, x7, mem)
  -- Compose: s1 goes base → base+4, need to match with s2
  -- s1: (x12 ** x7 ** mem) → (x12 ** x7=limb ** mem)
  -- s2: (x7=limb) → (x7=result) — needs framing with x12 and mem
  have s2f := cpsTriple_frame_right code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 off) ↦ₘ limb))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s2
  -- s3: (x12 ** x7=result ** mem=limb) → (x12 ** x7=result ** mem=result)
  -- Compose s1 ; s2f
  have c12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _
    (cpsTriple_consequence code base (base + 4) _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) s1)
    (cpsTriple_consequence code (base + 4) (base + 8) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s2f)
  -- Compose (s1;s2f) ; s3
  exact cpsTriple_seq code base (base + 8) (base + 12) _ _ _
    (cpsTriple_consequence code base (base + 8) _ _ _ _
      (fun _ hp => hp) (fun _ hp => hp) c12)
    (cpsTriple_consequence code (base + 8) (base + 12) _ _ _ _
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp)
      (fun _ hp => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢; exact hp) s3)

-- ============================================================================
-- Helpers
-- ============================================================================

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Individual limb canonicalizers
-- Each lifts a 5-conjunct per-limb spec to the full 19-conjunct canonical form.
-- Only 2 sep_perm calls per theorem, well within heartbeat limits.
-- ============================================================================

private theorem bw_limb0 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    (((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb1 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ b1))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ op a1 b1))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ op a1 b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb2 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ b2))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ op a2 b2))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ op a2 b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb3 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ op a3 b3))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ op a3 b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb4 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ b4))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ op a4 b4))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ op a4 b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb5 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ b5))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ op a5 b5))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ op a5 b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb6 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ b6))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ op a6 b6))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ op a6 b6) ** ((sp + 60) ↦ₘ b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

private theorem bw_limb7 (code : CodeMem) (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ op a7 b7))) :
    cpsTriple code base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ op a7 b7)) := by
  have Lf := cpsTriple_frame_left code base_k (base_k + 16) _ _
    ((sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6))
    (by pcFree) L
  exact cpsTriple_consequence code base_k (base_k + 16) _ _ _ _
    (fun _ hp => by sep_perm hp) (fun _ hp => by sep_perm hp) Lf

-- ============================================================================
-- ADDI canonicalizer: changes x12 from sp to sp+32, no sep_perm needed
-- ============================================================================

private theorem bw_addi (code : CodeMem) (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (hc : code (base + 128) = some (.ADDI .x12 .x12 32)) :
    cpsTriple code (base + 128) (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7)) := by
  have LA := addi_spec_gen_same code .x12 sp (32 : BitVec 12) (base + 128) (by nofun) hc
  simp only [signExtend12_32] at LA
  rw [show (base + 128) + 4 = base + 132 from by bv_addr] at LA
  exact cpsTriple_frame_left code (base + 128) (base + 132) _ _
    ((.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
     (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) LA

-- ============================================================================
-- Full binary bitwise spec: composes 8 limb canonicalizers + ADDI.
-- Zero sep_perm calls — all permutation work is in the individual canonicalizers.
-- Uses ValidMemRange for clean validity hypotheses.
-- ============================================================================

theorem binary_bitwise_spec (code : CodeMem) (sp base : Addr)
    (op : Word → Word → Word) (alu_instr : Instr)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (limb_spec : ∀ (off_a off_b : BitVec 12)
      (a_limb b_limb v7_in v6_in : Word) (base' : Addr)
      (hf1 : code base' = some (.LW .x7 .x12 off_a))
      (hf2 : code (base' + 4) = some (.LW .x6 .x12 off_b))
      (hf3 : code (base' + 8) = some alu_instr)
      (hf4 : code (base' + 12) = some (.SW .x12 .x7 off_b))
      (hva : isValidMemAccess (sp + signExtend12 off_a) = true)
      (hvb : isValidMemAccess (sp + signExtend12 off_b) = true),
      cpsTriple code base' (base' + 16)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7_in) ** (.x6 ↦ᵣ v6_in) **
         ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a_limb b_limb) ** (.x6 ↦ᵣ b_limb) **
         ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ op a_limb b_limb)))
    (hc0 : code base = some (.LW .x7 .x12 0))
    (hc1 : code (base + 4) = some (.LW .x6 .x12 32))
    (hc2 : code (base + 8) = some alu_instr)
    (hc3 : code (base + 12) = some (.SW .x12 .x7 32))
    (hc4 : code (base + 16) = some (.LW .x7 .x12 4))
    (hc5 : code (base + 20) = some (.LW .x6 .x12 36))
    (hc6 : code (base + 24) = some alu_instr)
    (hc7 : code (base + 28) = some (.SW .x12 .x7 36))
    (hc8 : code (base + 32) = some (.LW .x7 .x12 8))
    (hc9 : code (base + 36) = some (.LW .x6 .x12 40))
    (hc10 : code (base + 40) = some alu_instr)
    (hc11 : code (base + 44) = some (.SW .x12 .x7 40))
    (hc12 : code (base + 48) = some (.LW .x7 .x12 12))
    (hc13 : code (base + 52) = some (.LW .x6 .x12 44))
    (hc14 : code (base + 56) = some alu_instr)
    (hc15 : code (base + 60) = some (.SW .x12 .x7 44))
    (hc16 : code (base + 64) = some (.LW .x7 .x12 16))
    (hc17 : code (base + 68) = some (.LW .x6 .x12 48))
    (hc18 : code (base + 72) = some alu_instr)
    (hc19 : code (base + 76) = some (.SW .x12 .x7 48))
    (hc20 : code (base + 80) = some (.LW .x7 .x12 20))
    (hc21 : code (base + 84) = some (.LW .x6 .x12 52))
    (hc22 : code (base + 88) = some alu_instr)
    (hc23 : code (base + 92) = some (.SW .x12 .x7 52))
    (hc24 : code (base + 96) = some (.LW .x7 .x12 24))
    (hc25 : code (base + 100) = some (.LW .x6 .x12 56))
    (hc26 : code (base + 104) = some alu_instr)
    (hc27 : code (base + 108) = some (.SW .x12 .x7 56))
    (hc28 : code (base + 112) = some (.LW .x7 .x12 28))
    (hc29 : code (base + 116) = some (.LW .x6 .x12 60))
    (hc30 : code (base + 120) = some alu_instr)
    (hc31 : code (base + 124) = some (.SW .x12 .x7 60))
    (hc32 : code (base + 128) = some (.ADDI .x12 .x12 32))
    (hvalid : ValidMemRange sp 16) :
    cpsTriple code base (base + 132)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 36) ↦ₘ op a1 b1) ** ((sp + 40) ↦ₘ op a2 b2) ** ((sp + 44) ↦ₘ op a3 b3) **
       ((sp + 48) ↦ₘ op a4 b4) ** ((sp + 52) ↦ₘ op a5 b5) ** ((sp + 56) ↦ₘ op a6 b6) ** ((sp + 60) ↦ₘ op a7 b7)) := by
  -- Extract validity from ValidMemRange
  have hv0  := hvalid.fetch 0  sp        (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1  (sp + 4)  (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2  (sp + 8)  (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3  (sp + 12) (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4  (sp + 16) (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5  (sp + 20) (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6  (sp + 24) (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7  (sp + 28) (by omega) (by bv_addr)
  have hv32 := hvalid.fetch 8  (sp + 32) (by omega) (by bv_addr)
  have hv36 := hvalid.fetch 9  (sp + 36) (by omega) (by bv_addr)
  have hv40 := hvalid.fetch 10 (sp + 40) (by omega) (by bv_addr)
  have hv44 := hvalid.fetch 11 (sp + 44) (by omega) (by bv_addr)
  have hv48 := hvalid.fetch 12 (sp + 48) (by omega) (by bv_addr)
  have hv52 := hvalid.fetch 13 (sp + 52) (by omega) (by bv_addr)
  have hv56 := hvalid.fetch 14 (sp + 56) (by omega) (by bv_addr)
  have hv60 := hvalid.fetch 15 (sp + 60) (by omega) (by bv_addr)
  -- signExtend12(0) = 0, sp + 0 = sp
  have hse0 : sp + signExtend12 (0 : BitVec 12) = sp := by
    simp only [signExtend12_0]; bv_addr
  -- Limb 0: offsets 0, 32
  have L0 := limb_spec 0 32 a0 b0 v7 v6 base hc0 hc1 hc2 hc3
    (by rw [hse0]; exact hv0) (by simp only [signExtend12_32]; exact hv32)
  simp only [signExtend12_32] at L0; rw [hse0] at L0
  have C0 := bw_limb0 code sp base op a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 L0
  -- Limb 1: offsets 4, 36
  have L1 := limb_spec 4 36 a1 b1 (op a0 b0) b0 (base + 16) hc4
    (by rw [show (base + 16) + 4 = base + 20 from by bv_addr]; exact hc5)
    (by rw [show (base + 16) + 8 = base + 24 from by bv_addr]; exact hc6)
    (by rw [show (base + 16) + 12 = base + 28 from by bv_addr]; exact hc7)
    (by simp only [signExtend12_4]; exact hv4) (by simp only [signExtend12_36]; exact hv36)
  simp only [signExtend12_4, signExtend12_36] at L1
  have C1 := bw_limb1 code sp (base + 16) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) b1 b2 b3 b4 b5 b6 b7 (op a0 b0) b0 L1
  rw [show (base + 16) + 16 = base + 32 from by bv_addr] at C1
  -- Limb 2: offsets 8, 40
  have L2 := limb_spec 8 40 a2 b2 (op a1 b1) b1 (base + 32) hc8
    (by rw [show (base + 32) + 4 = base + 36 from by bv_addr]; exact hc9)
    (by rw [show (base + 32) + 8 = base + 40 from by bv_addr]; exact hc10)
    (by rw [show (base + 32) + 12 = base + 44 from by bv_addr]; exact hc11)
    (by simp only [signExtend12_8]; exact hv8) (by simp only [signExtend12_40]; exact hv40)
  simp only [signExtend12_8, signExtend12_40] at L2
  have C2 := bw_limb2 code sp (base + 32) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) b2 b3 b4 b5 b6 b7 (op a1 b1) b1 L2
  rw [show (base + 32) + 16 = base + 48 from by bv_addr] at C2
  -- Limb 3: offsets 12, 44
  have L3 := limb_spec 12 44 a3 b3 (op a2 b2) b2 (base + 48) hc12
    (by rw [show (base + 48) + 4 = base + 52 from by bv_addr]; exact hc13)
    (by rw [show (base + 48) + 8 = base + 56 from by bv_addr]; exact hc14)
    (by rw [show (base + 48) + 12 = base + 60 from by bv_addr]; exact hc15)
    (by simp only [signExtend12_12]; exact hv12) (by simp only [signExtend12_44]; exact hv44)
  simp only [signExtend12_12, signExtend12_44] at L3
  have C3 := bw_limb3 code sp (base + 48) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) b3 b4 b5 b6 b7 (op a2 b2) b2 L3
  rw [show (base + 48) + 16 = base + 64 from by bv_addr] at C3
  -- Limb 4: offsets 16, 48
  have L4 := limb_spec 16 48 a4 b4 (op a3 b3) b3 (base + 64) hc16
    (by rw [show (base + 64) + 4 = base + 68 from by bv_addr]; exact hc17)
    (by rw [show (base + 64) + 8 = base + 72 from by bv_addr]; exact hc18)
    (by rw [show (base + 64) + 12 = base + 76 from by bv_addr]; exact hc19)
    (by simp only [signExtend12_16]; exact hv16) (by simp only [signExtend12_48]; exact hv48)
  simp only [signExtend12_16, signExtend12_48] at L4
  have C4 := bw_limb4 code sp (base + 64) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) b4 b5 b6 b7 (op a3 b3) b3 L4
  rw [show (base + 64) + 16 = base + 80 from by bv_addr] at C4
  -- Limb 5: offsets 20, 52
  have L5 := limb_spec 20 52 a5 b5 (op a4 b4) b4 (base + 80) hc20
    (by rw [show (base + 80) + 4 = base + 84 from by bv_addr]; exact hc21)
    (by rw [show (base + 80) + 8 = base + 88 from by bv_addr]; exact hc22)
    (by rw [show (base + 80) + 12 = base + 92 from by bv_addr]; exact hc23)
    (by simp only [signExtend12_20]; exact hv20) (by simp only [signExtend12_52]; exact hv52)
  simp only [signExtend12_20, signExtend12_52] at L5
  have C5 := bw_limb5 code sp (base + 80) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) b5 b6 b7 (op a4 b4) b4 L5
  rw [show (base + 80) + 16 = base + 96 from by bv_addr] at C5
  -- Limb 6: offsets 24, 56
  have L6 := limb_spec 24 56 a6 b6 (op a5 b5) b5 (base + 96) hc24
    (by rw [show (base + 96) + 4 = base + 100 from by bv_addr]; exact hc25)
    (by rw [show (base + 96) + 8 = base + 104 from by bv_addr]; exact hc26)
    (by rw [show (base + 96) + 12 = base + 108 from by bv_addr]; exact hc27)
    (by simp only [signExtend12_24]; exact hv24) (by simp only [signExtend12_56]; exact hv56)
  simp only [signExtend12_24, signExtend12_56] at L6
  have C6 := bw_limb6 code sp (base + 96) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) b6 b7 (op a5 b5) b5 L6
  rw [show (base + 96) + 16 = base + 112 from by bv_addr] at C6
  -- Limb 7: offsets 28, 60
  have L7 := limb_spec 28 60 a7 b7 (op a6 b6) b6 (base + 112) hc28
    (by rw [show (base + 112) + 4 = base + 116 from by bv_addr]; exact hc29)
    (by rw [show (base + 112) + 8 = base + 120 from by bv_addr]; exact hc30)
    (by rw [show (base + 112) + 12 = base + 124 from by bv_addr]; exact hc31)
    (by simp only [signExtend12_28]; exact hv28) (by simp only [signExtend12_60]; exact hv60)
  simp only [signExtend12_28, signExtend12_60] at L7
  have C7 := bw_limb7 code sp (base + 112) op a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) (op a6 b6) b7 (op a6 b6) b6 L7
  rw [show (base + 112) + 16 = base + 128 from by bv_addr] at C7
  -- ADDI: sp += 32
  have CA := bw_addi code sp base a0 a1 a2 a3 a4 a5 a6 a7
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3) (op a4 b4) (op a5 b5) (op a6 b6) (op a7 b7) (op a7 b7) b7 hc32
  -- Compose: C0 ; C1 ; ... ; C7 ; CA
  -- Each step's post matches the next step's pre (same canonical 19-conjunct form)
  have c01 := cpsTriple_seq code base (base + 16) (base + 32) _ _ _ C0 C1
  have c012 := cpsTriple_seq code base (base + 32) (base + 48) _ _ _ c01 C2
  have c0123 := cpsTriple_seq code base (base + 48) (base + 64) _ _ _ c012 C3
  have c01234 := cpsTriple_seq code base (base + 64) (base + 80) _ _ _ c0123 C4
  have c012345 := cpsTriple_seq code base (base + 80) (base + 96) _ _ _ c01234 C5
  have c0123456 := cpsTriple_seq code base (base + 96) (base + 112) _ _ _ c012345 C6
  have c01234567 := cpsTriple_seq code base (base + 112) (base + 128) _ _ _ c0123456 C7
  exact cpsTriple_seq code base (base + 128) (base + 132) _ _ _ c01234567 CA

end EvmAsm
