/-
  RiscVMacroAsm.Evm.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RISC-V programs.
  Each operates on 8 little-endian 32-bit limbs stored in memory.
-/

import RiscVMacroAsm.Evm.Stack
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm

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

end RiscVMacroAsm
