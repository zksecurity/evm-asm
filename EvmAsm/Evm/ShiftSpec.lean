/-
  EvmAsm.Evm.ShiftSpec

  CPS specifications for the 256-bit EVM SHR (logical shift right) program.
  Modular decomposition:
  - Per-limb helpers: shr_merge_limb_spec (7 instrs), shr_last_limb_spec (3 instrs)
  - Zero-fill helper: shr_sw_zero_spec (1 instr)
  - Zero path: shr_zero_path_spec (9 instrs, shift >= 256)
  - Shift bodies: shr_body_L_spec for L = 0..7
  - Full composition: evm_shr_spec
-/

import EvmAsm.Evm.Shift
import EvmAsm.SyscallSpecs
import EvmAsm.Tactics.XSimp

namespace EvmAsm

set_option maxHeartbeats 800000

local macro "bv_addr" : tactic =>
  `(tactic| (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]))

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb (7 instructions)
-- ============================================================================

/-- SHR merge limb spec (7 instructions):
    LW x5, src_off(x12); SRL x5,x5,x6; LW x10, next_off(x12);
    SLL x10,x10,x7; AND x10,x10,x11; OR x5,x5,x10; SW x12,x5,dst_off

    Computes: result = (src >>> bit_shift) ||| ((next <<< anti_shift) &&& mask)
    and stores at dst_off.

    Preserves: x12, x6, x7, x11, memory at src and next.
    Modifies: x5 (= result), x10 (= (next <<< anti_shift) &&& mask), memory at dst. -/
theorem shr_merge_limb_spec (code : CodeMem) (src_off next_off dst_off : BitVec 12)
    (sp src next dst_old v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hf0 : code base = some (.LW .x5 .x12 src_off))
    (hf1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 8) = some (.LW .x10 .x12 next_off))
    (hf3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hf4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hf5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hf6 : code (base + 24) = some (.SW .x12 .x5 dst_off))
    (hvalid_src : isValidMemAccess (sp + signExtend12 src_off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 src_off
    let mem_next := sp + signExtend12 next_off
    let mem_dst := sp + signExtend12 dst_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple code base (base + 28)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ result)) := by
  simp only
  -- Address normalization lemmas
  have h48 : base + 4 + 4 = base + 8 := by bv_addr
  have h812 : base + 8 + 4 = base + 12 := by bv_addr
  have h1216 : base + 12 + 4 = base + 16 := by bv_addr
  have h1620 : base + 16 + 4 = base + 20 := by bv_addr
  have h2024 : base + 20 + 4 = base + 24 := by bv_addr
  have h2428 : base + 24 + 4 = base + 28 := by bv_addr
  -- Step 1: LW x5, src_off(x12) — loads src into x5
  have s1 := lw_spec_gen code .x5 .x12 sp v5 src src_off base (by nofun) hf0 hvalid_src
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s1
  -- Step 2: SRL x5, x5, x6 — x5 = src >>> bit_shift
  have s2 := srl_spec_gen_rd_eq_rs1 code .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun) hf1
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) **
     ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))) s2
  -- Step 3: LW x10, next_off(x12) — loads next into x10
  have s3 := lw_spec_gen code .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hf2 hvalid_next
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s3
  -- Step 4: SLL x10, x10, x7 — x10 = next <<< anti_shift
  have s4 := sll_spec_gen_rd_eq_rs1 code .x10 .x7 next anti_shift (base + 12) (by nofun) (by nofun) hf3
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) **
     ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))) s4
  -- Step 5: AND x10, x10, x11 — x10 = (next <<< anti_shift) &&& mask
  have s5 := and_spec_gen_rd_eq_rs1 code .x10 .x11 (next <<< (anti_shift.toNat % 32)) mask (base + 16) (by nofun) (by nofun) hf4
  rw [h1620] at s5
  have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) **
     ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))) s5
  -- Step 6: OR x5, x5, x10 — x5 = result
  have s6 := or_spec_gen_rd_eq_rs1 code .x5 .x10 (src >>> (bit_shift.toNat % 32))
    ((next <<< (anti_shift.toNat % 32)) &&& mask) (base + 20) (by nofun) (by nofun) hf5
  rw [h2024] at s6
  have s6f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next) **
     ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))))))) s6
  -- Step 7: SW x12, x5, dst_off — store result
  have s7 := sw_spec_gen code .x12 .x5 sp
    ((src >>> (bit_shift.toNat % 32)) ||| ((next <<< (anti_shift.toNat % 32)) &&& mask))
    dst_old dst_off (base + 24) hf6 hvalid_dst
  rw [h2428] at s7
  have s7f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((next <<< (anti_shift.toNat % 32)) &&& mask)) **
     (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 src_off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s7
  -- Compose all 7 steps
  clear hf0 hf1 hf2 hf3 hf4 hf5 hf6
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1f s2f; clear s1f s2f
  have c123 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 s3f; clear c12 s3f
  have c1234 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c123 s4f; clear c123 s4f
  have c12345 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c1234 s5f; clear c1234 s5f
  have c123456 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12345 s6f; clear c12345 s6f
  have cfull := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c123456 s7f; clear c123456 s7f
  exact cpsTriple_consequence code base (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Per-limb Specs: SHR Last Limb (3 instructions)
-- ============================================================================

/-- SHR last limb spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,dst_off

    Computes: result = value[7] >>> bit_shift
    and stores at dst_off. This is the highest non-zero limb in a shift body.

    Preserves: x12, x6, x7, x10, x11, memory at value[7].
    Modifies: x5 (= result), memory at dst. -/
theorem shr_last_limb_spec (code : CodeMem) (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Addr)
    (hf0 : code base = some (.LW .x5 .x12 28))
    (hf1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 8) = some (.SW .x12 .x5 dst_off))
    (hvalid_src : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 (28 : BitVec 12)
    let mem_dst := sp + signExtend12 dst_off
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by bv_addr
  have h812 : base + 8 + 4 = base + 12 := by bv_addr
  -- Step 1: LW x5, 28(x12)
  have s1 := lw_spec_gen code .x5 .x12 sp v5 src 28 base (by nofun) hf0 hvalid_src
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ bit_shift) ** ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s1
  -- Step 2: SRL x5, x5, x6
  have s2 := srl_spec_gen_rd_eq_rs1 code .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun) hf1
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src) **
     ((sp + signExtend12 dst_off) ↦ₘ dst_old))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _))) s2
  -- Step 3: SW x12, x5, dst_off
  have s3 := sw_spec_gen code .x12 .x5 sp (src >>> (bit_shift.toNat % 32)) dst_old dst_off (base + 8) hf2 hvalid_dst
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x6 ↦ᵣ bit_shift) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s3
  -- Compose
  clear hf0 hf1 hf2
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1f s2f; clear s1f s2f
  have cfull := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 s3f; clear c12 s3f
  exact cpsTriple_consequence code base (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

/-- SHR merge limb in-place spec (7 instructions):
    Same as shr_merge_limb_spec but src_off = dst_off. The source value is
    read then overwritten in place. Only 2 memory cells needed (no separate dst). -/
theorem shr_merge_limb_inplace_spec (code : CodeMem) (off next_off : BitVec 12)
    (sp src next v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hf0 : code base = some (.LW .x5 .x12 off))
    (hf1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 8) = some (.LW .x10 .x12 next_off))
    (hf3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hf4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hf5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hf6 : code (base + 24) = some (.SW .x12 .x5 off))
    (hvalid_loc : isValidMemAccess (sp + signExtend12 off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true) :
    let mem_loc := sp + signExtend12 off
    let mem_next := sp + signExtend12 next_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple code base (base + 28)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ src) ** (mem_next ↦ₘ next))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ result) ** (mem_next ↦ₘ next)) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by bv_addr
  have h812 : base + 8 + 4 = base + 12 := by bv_addr
  have h1216 : base + 12 + 4 = base + 16 := by bv_addr
  have h1620 : base + 16 + 4 = base + 20 := by bv_addr
  have h2024 : base + 20 + 4 = base + 24 := by bv_addr
  have h2428 : base + 24 + 4 = base + 28 := by bv_addr
  -- Step 1: LW x5, off(x12)
  have s1 := lw_spec_gen code .x5 .x12 sp v5 src off base (by nofun) hf0 hvalid_loc
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_memIs _ _))))) s1
  -- Step 2: SRL x5, x5, x6
  have s2 := srl_spec_gen_rd_eq_rs1 code .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun) hf1
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s2
  -- Step 3: LW x10, next_off(x12)
  have s3 := lw_spec_gen code .x10 .x12 sp v10 next next_off (base + 8) (by nofun) hf2 hvalid_next
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_memIs _ _))))) s3
  -- Step 4: SLL x10, x10, x7
  have s4 := sll_spec_gen_rd_eq_rs1 code .x10 .x7 next anti_shift (base + 12) (by nofun) (by nofun) hf3
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s4
  -- Step 5: AND x10, x10, x11
  have s5 := and_spec_gen_rd_eq_rs1 code .x10 .x11 (next <<< (anti_shift.toNat % 32)) mask (base + 16) (by nofun) (by nofun) hf4
  rw [h1620] at s5
  have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (src >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s5
  -- Step 6: OR x5, x5, x10
  have s6 := or_spec_gen_rd_eq_rs1 code .x5 .x10 (src >>> (bit_shift.toNat % 32))
    ((next <<< (anti_shift.toNat % 32)) &&& mask) (base + 20) (by nofun) (by nofun) hf5
  rw [h2024] at s6
  have s6f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 off) ↦ₘ src) ** ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_sepConj (pcFree_memIs _ _) (pcFree_memIs _ _)))))) s6
  -- Step 7: SW x12, x5, off — overwrite source in-place
  have s7 := sw_spec_gen code .x12 .x5 sp
    ((src >>> (bit_shift.toNat % 32)) ||| ((next <<< (anti_shift.toNat % 32)) &&& mask))
    src off (base + 24) hf6 hvalid_loc
  rw [h2428] at s7
  have s7f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x6 ↦ᵣ bit_shift) ** (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((next <<< (anti_shift.toNat % 32)) &&& mask)) **
     (.x11 ↦ᵣ mask) **
     ((sp + signExtend12 next_off) ↦ₘ next))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _)
     (pcFree_sepConj (pcFree_regIs _ _)
      (pcFree_memIs _ _))))) s7
  -- Compose all 7 steps
  clear hf0 hf1 hf2 hf3 hf4 hf5 hf6
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1f s2f; clear s1f s2f
  have c123 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 s3f; clear c12 s3f
  have c1234 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c123 s4f; clear c123 s4f
  have c12345 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c1234 s5f; clear c1234 s5f
  have c123456 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12345 s6f; clear c12345 s6f
  have cfull := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c123456 s7f; clear c123456 s7f
  exact cpsTriple_consequence code base (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Per-limb Specs: SHR Last Limb In-place (3 instructions, dst_off = 28)
-- ============================================================================

/-- SHR last limb in-place spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,28
    Reads and writes the same memory cell at sp+28. -/
theorem shr_last_limb_inplace_spec (code : CodeMem)
    (sp src v5 bit_shift : Word) (base : Addr)
    (hf0 : code base = some (.LW .x5 .x12 28))
    (hf1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 8) = some (.SW .x12 .x5 28))
    (hvalid : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (28 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple code base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  simp only
  have h48 : base + 4 + 4 = base + 8 := by bv_addr
  have h812 : base + 8 + 4 = base + 12 := by bv_addr
  -- Step 1: LW x5, 28(x12)
  have s1 := lw_spec_gen code .x5 .x12 sp v5 src 28 base (by nofun) hf0 hvalid
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ bit_shift))
    (pcFree_regIs _ _) s1
  -- Step 2: SRL x5, x5, x6
  have s2 := srl_spec_gen_rd_eq_rs1 code .x5 .x6 src bit_shift (base + 4) (by nofun) (by nofun) hf1
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 (28 : BitVec 12)) ↦ₘ src))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memIs _ _)) s2
  -- Step 3: SW x12, x5, 28
  have s3 := sw_spec_gen code .x12 .x5 sp (src >>> (bit_shift.toNat % 32)) src 28 (base + 8) hf2 hvalid
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x6 ↦ᵣ bit_shift))
    (pcFree_regIs _ _) s3
  -- Compose
  clear hf0 hf1 hf2
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1f s2f; clear s1f s2f
  have cfull := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 s3f; clear c12 s3f
  exact cpsTriple_consequence code base (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Zero-fill helper: SW x12, x0, offset (1 instruction)
-- ============================================================================

/-- Store zero at offset: SW x12, x0, offset.
    Writes 0 to memory at sp + sext(offset). -/
theorem shr_sw_zero_spec (code : CodeMem) (offset : BitVec 12)
    (sp old_val : Word) (base : Addr)
    (hf : code base = some (.SW .x12 .x0 offset))
    (hvalid : isValidMemAccess (sp + signExtend12 offset) = true) :
    cpsTriple code base (base + 4)
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ old_val))
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ 0)) := by
  exact sw_x0_spec_gen code .x12 sp old_val offset base hf hvalid

-- ============================================================================
-- Zero path spec (9 instructions): shift >= 256, result is all zeros
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Zero path spec: ADDI x12, x12, 32 followed by 8 SW x12, x0, N.
    This is used when shift >= 256. Advances sp by 32 and zeros all 8 result limbs. -/
theorem shr_zero_path_spec (code : CodeMem) (sp : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)   -- old values at result locations
    (base : Addr)
    (hf0 : code base = some (.ADDI .x12 .x12 32))
    (hf1 : code (base + 4)  = some (.SW .x12 .x0 0))
    (hf2 : code (base + 8)  = some (.SW .x12 .x0 4))
    (hf3 : code (base + 12) = some (.SW .x12 .x0 8))
    (hf4 : code (base + 16) = some (.SW .x12 .x0 12))
    (hf5 : code (base + 20) = some (.SW .x12 .x0 16))
    (hf6 : code (base + 24) = some (.SW .x12 .x0 20))
    (hf7 : code (base + 28) = some (.SW .x12 .x0 24))
    (hf8 : code (base + 32) = some (.SW .x12 .x0 28))
    (hvalid : ValidMemRange (sp + 32) 8) :
    let nsp := sp + 32
    cpsTriple code base (base + 36)
      ((.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  simp only
  -- Extract memory validity — use nsp = sp + 32
  have hv0  := hvalid.fetch 0 (sp + 32)       (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 32 + 4)   (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 32 + 8)   (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 32 + 12)  (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 32 + 16)  (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 32 + 20)  (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 32 + 24)  (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 32 + 28)  (by omega) (by bv_addr)
  -- ADDI x12, x12, 32: x12 goes sp → sp+32
  have LA := addi_spec_gen_same code .x12 sp 32 base (by nofun) hf0
  simp only [signExtend12_32] at LA
  have LAf := cpsTriple_frame_left code base (base + 4) _ _
    (((sp + 32) ↦ₘ d0) ** ((sp + 32 + 4) ↦ₘ d1) ** ((sp + 32 + 8) ↦ₘ d2) ** ((sp + 32 + 12) ↦ₘ d3) **
     ((sp + 32 + 16) ↦ₘ d4) ** ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) LA
  -- SW x12, x0, 0: mem[nsp] := 0
  have S0 := sw_x0_spec_gen code .x12 (sp + 32) d0 0 (base + 4) hf1
    (by simp only [signExtend12_0]; rw [show (sp + 32) + (0 : Word) = sp + 32 from by bv_addr]; exact hv0)
  simp only [signExtend12_0] at S0
  rw [show (sp + 32) + (0 : Word) = sp + 32 from by bv_addr,
      show (base + 4) + 4 = base + 8 from by bv_addr] at S0
  have S0f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    (((sp + 32 + 4) ↦ₘ d1) ** ((sp + 32 + 8) ↦ₘ d2) ** ((sp + 32 + 12) ↦ₘ d3) **
     ((sp + 32 + 16) ↦ₘ d4) ** ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S0
  -- SW x12, x0, 4: mem[nsp+4] := 0
  have S1 := sw_x0_spec_gen code .x12 (sp + 32) d1 4 (base + 8) hf2
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4] at S1
  rw [show (base + 8) + 4 = base + 12 from by bv_addr] at S1
  have S1f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ d2) ** ((sp + 32 + 12) ↦ₘ d3) **
     ((sp + 32 + 16) ↦ₘ d4) ** ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S1
  -- SW x12, x0, 8: mem[nsp+8] := 0
  have S2 := sw_x0_spec_gen code .x12 (sp + 32) d2 8 (base + 12) hf3
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at S2
  rw [show (base + 12) + 4 = base + 16 from by bv_addr] at S2
  have S2f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 12) ↦ₘ d3) **
     ((sp + 32 + 16) ↦ₘ d4) ** ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S2
  -- SW x12, x0, 12: mem[nsp+12] := 0
  have S3 := sw_x0_spec_gen code .x12 (sp + 32) d3 12 (base + 16) hf4
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at S3
  rw [show (base + 16) + 4 = base + 20 from by bv_addr] at S3
  have S3f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ (0 : Word)) **
     ((sp + 32 + 16) ↦ₘ d4) ** ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S3
  -- SW x12, x0, 16: mem[nsp+16] := 0
  have S4 := sw_x0_spec_gen code .x12 (sp + 32) d4 16 (base + 20) hf5
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at S4
  rw [show (base + 20) + 4 = base + 24 from by bv_addr] at S4
  have S4f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ (0 : Word)) ** ((sp + 32 + 12) ↦ₘ (0 : Word)) **
     ((sp + 32 + 20) ↦ₘ d5) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S4
  -- SW x12, x0, 20: mem[nsp+20] := 0
  have S5 := sw_x0_spec_gen code .x12 (sp + 32) d5 20 (base + 24) hf6
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at S5
  rw [show (base + 24) + 4 = base + 28 from by bv_addr] at S5
  have S5f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ (0 : Word)) ** ((sp + 32 + 12) ↦ₘ (0 : Word)) **
     ((sp + 32 + 16) ↦ₘ (0 : Word)) ** ((sp + 32 + 24) ↦ₘ d6) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S5
  -- SW x12, x0, 24: mem[nsp+24] := 0
  have S6 := sw_x0_spec_gen code .x12 (sp + 32) d6 24 (base + 28) hf7
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at S6
  rw [show (base + 28) + 4 = base + 32 from by bv_addr] at S6
  have S6f := cpsTriple_frame_left code (base + 28) (base + 32) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ (0 : Word)) ** ((sp + 32 + 12) ↦ₘ (0 : Word)) **
     ((sp + 32 + 16) ↦ₘ (0 : Word)) ** ((sp + 32 + 20) ↦ₘ (0 : Word)) ** ((sp + 32 + 28) ↦ₘ d7))
    (by pcFree) S6
  -- SW x12, x0, 28: mem[nsp+28] := 0
  have S7 := sw_x0_spec_gen code .x12 (sp + 32) d7 28 (base + 32) hf8
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at S7
  rw [show (base + 32) + 4 = base + 36 from by bv_addr] at S7
  have S7f := cpsTriple_frame_left code (base + 32) (base + 36) _ _
    (((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 32 + 4) ↦ₘ (0 : Word)) ** ((sp + 32 + 8) ↦ₘ (0 : Word)) ** ((sp + 32 + 12) ↦ₘ (0 : Word)) **
     ((sp + 32 + 16) ↦ₘ (0 : Word)) ** ((sp + 32 + 20) ↦ₘ (0 : Word)) ** ((sp + 32 + 24) ↦ₘ (0 : Word)))
    (by pcFree) S7
  -- Compose all 9 steps
  clear hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear LA S0 S1 S2 S3 S4 S5 S6 S7
  have c01 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) LAf S0f; clear LAf S0f
  have c02 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 S1f; clear c01 S1f
  have c03 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 S2f; clear c02 S2f
  have c04 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 S3f; clear c03 S3f
  have c05 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 S4f; clear c04 S4f
  have c06 := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 S5f; clear c05 S5f
  have c07 := cpsTriple_seq_with_perm code base (base + 28) (base + 32) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 S6f; clear c06 S6f
  have cfull := cpsTriple_seq_with_perm code base (base + 32) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 S7f; clear c07 S7f
  exact cpsTriple_consequence code base (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Phase B spec: Extract parameters (7 instructions)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase B spec: Extract bit_shift, limb_shift, mask, anti_shift from shift0.
    ANDI x6,x5,31; SRLI x5,x5,5; SLTU x11,x0,x6; SUB x11,x0,x11;
    LI x7,32; SUB x7,x7,x6; ADDI x12,x12,32.
    Requires .x0 ↦ᵣ 0 for SLTU and SUB instructions using x0. -/
theorem shr_phase_b_spec (code : CodeMem) (shift0 sp r6 r7 r11 : Word) (base : Addr)
    (hf0 : code base = some (.ANDI .x6 .x5 31))
    (hf1 : code (base + 4) = some (.SRLI .x5 .x5 5))
    (hf2 : code (base + 8) = some (.SLTU .x11 .x0 .x6))
    (hf3 : code (base + 12) = some (.SUB .x11 .x0 .x11))
    (hf4 : code (base + 16) = some (.LI .x7 32))
    (hf5 : code (base + 20) = some (.SUB .x7 .x7 .x6))
    (hf6 : code (base + 24) = some (.ADDI .x12 .x12 32)) :
    let bit_shift := shift0 &&& signExtend12 31
    let limb_shift := shift0 >>> (5 : BitVec 5).toNat
    let cond := if BitVec.ult (0 : Word) bit_shift then (1 : Word) else 0
    let mask := (0 : Word) - cond
    let anti_shift := (32 : Word) - bit_shift
    cpsTriple code base (base + 28)
      ((.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      ((.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  simp only
  -- Address normalization
  have h48 : base + 4 + 4 = base + 8 := by bv_addr
  have h812 : base + 8 + 4 = base + 12 := by bv_addr
  have h1216 : base + 12 + 4 = base + 16 := by bv_addr
  have h1620 : base + 16 + 4 = base + 20 := by bv_addr
  have h2024 : base + 20 + 4 = base + 24 := by bv_addr
  have h2428 : base + 24 + 4 = base + 28 := by bv_addr
  -- Step 1: ANDI x6, x5, 31 — x6 = shift0 & 31
  have s1 := andi_spec_gen code .x6 .x5 r6 shift0 31 base (by nofun) (by nofun) hf0
  have s1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x0 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s1
  -- Step 2: SRLI x5, x5, 5 — x5 = shift0 >>> 5
  have s2 := srli_spec_gen_same code .x5 shift0 5 (base + 4) (by nofun) hf1
  rw [h48] at s2
  have s2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x6 ↦ᵣ (shift0 &&& signExtend12 31)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s2
  -- Step 3: SLTU x11, x0, x6 — x11 = (0 < bit_shift ? 1 : 0)
  have s3 := sltu_spec_gen code .x11 .x0 .x6 r11 (0 : Word)
    (shift0 &&& signExtend12 31) (base + 8) (by nofun) hf2
  rw [h812] at s3
  have s3f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s3
  -- Step 4: SUB x11, x0, x11 — x11 = 0 - cond = mask
  have s4 := sub_spec_gen_rd_eq_rs2 code .x11 .x0 (0 : Word)
    (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31) then (1 : Word) else 0)
    (base + 12) (by nofun) (by nofun) hf3
  rw [h1216] at s4
  have s4f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) **
     (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
    (by pcFree) s4
  -- Step 5: LI x7, 32
  have s5 := li_spec_gen code .x7 r7 (32 : Word) (base + 16) (by nofun) hf4
  rw [h1620] at s5
  have s5f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) **
     (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31)
       then (1 : Word) else 0))) ** (.x12 ↦ᵣ sp))
    (by pcFree) s5
  -- Step 6: SUB x7, x7, x6 — x7 = 32 - bit_shift
  have s6 := sub_spec_gen_rd_eq_rs1 code .x7 .x6 (32 : Word)
    (shift0 &&& signExtend12 31) (base + 20) (by nofun) (by nofun) hf5
  rw [h2024] at s6
  have s6f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31)
       then (1 : Word) else 0))) ** (.x12 ↦ᵣ sp))
    (by pcFree) s6
  -- Step 7: ADDI x12, x12, 32 — pop shift word
  have s7 := addi_spec_gen_same code .x12 sp 32 (base + 24) (by nofun) hf6
  rw [h2428] at s7
  have s7f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x5 ↦ᵣ (shift0 >>> (5 : BitVec 5).toNat)) **
     (.x6 ↦ᵣ (shift0 &&& signExtend12 31)) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x11 ↦ᵣ ((0 : Word) - (if BitVec.ult (0 : Word) (shift0 &&& signExtend12 31)
       then (1 : Word) else 0))) **
     (.x7 ↦ᵣ ((32 : Word) - (shift0 &&& signExtend12 31))))
    (by pcFree) s7
  -- Compose all steps
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) s1f s2f; clear s1f s2f
  have c13 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 s3f; clear c12 s3f
  have c14 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c13 s4f; clear c13 s4f
  have c15 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c14 s5f; clear c14 s5f
  have c16 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c15 s6f; clear c15 s6f
  have c17 := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c16 s7f; clear c16 s7f
  exact cpsTriple_consequence code base (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) c17

-- ============================================================================
-- Shift body spec: body_7 (limb_shift=7, 11 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 7: limb_shift=7. Result[0] = value[7] >>> bit_shift, rest = 0.
    Comprises: shr_last_limb 0, 7× SW x12 x0 N, JAL x0 to exit.
    11 instructions from base to exit (via JAL). -/
theorem shr_body_7_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- shr_last_limb 0: LW x5,28(x12); SRL x5,x5,x6; SW x12,x5,0
    (hf0 : code base = some (.LW .x5 .x12 28))
    (hf1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 8) = some (.SW .x12 .x5 0))
    -- 7 SW zeros
    (hf3 : code (base + 12) = some (.SW .x12 .x0 4))
    (hf4 : code (base + 16) = some (.SW .x12 .x0 8))
    (hf5 : code (base + 20) = some (.SW .x12 .x0 12))
    (hf6 : code (base + 24) = some (.SW .x12 .x0 16))
    (hf7 : code (base + 28) = some (.SW .x12 .x0 20))
    (hf8 : code (base + 32) = some (.SW .x12 .x0 24))
    (hf9 : code (base + 36) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hf10 : code (base + 40) = some (.JAL .x0 jal_off))
    (hexit : (base + 40) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  -- Extract memory validity
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: shr_last_limb with dst_off = 0
  -- shr_last_limb_spec: base to base+12, uses x12, x5, x6, mem_src(sp+28), mem_dst(sp+0)
  have LL := shr_last_limb_spec code 0 sp v7 v0 v5 bit_shift base hf0 hf1 hf2 hv28
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_0] at LL
  rw [show sp + (0 : Word) = sp from by bv_addr] at LL
  have LLf := cpsTriple_frame_left code base (base + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  -- Steps 2-8: 7 SW x12, x0, N for offsets 4,8,...,28
  have S0 := sw_x0_spec_gen code .x12 sp v1 4 (base + 12) hf3
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4] at S0
  rw [show (base + 12) + 4 = base + 16 from by bv_addr] at S0
  have S0f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S0
  have S1 := sw_x0_spec_gen code .x12 sp v2 8 (base + 16) hf4
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at S1
  rw [show (base + 16) + 4 = base + 20 from by bv_addr] at S1
  have S1f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S1
  have S2 := sw_x0_spec_gen code .x12 sp v3 12 (base + 20) hf5
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at S2
  rw [show (base + 20) + 4 = base + 24 from by bv_addr] at S2
  have S2f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S2
  have S3 := sw_x0_spec_gen code .x12 sp v4 16 (base + 24) hf6
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at S3
  rw [show (base + 24) + 4 = base + 28 from by bv_addr] at S3
  have S3f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S3
  have S4 := sw_x0_spec_gen code .x12 sp v5v 20 (base + 28) hf7
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at S4
  rw [show (base + 28) + 4 = base + 32 from by bv_addr] at S4
  have S4f := cpsTriple_frame_left code (base + 28) (base + 32) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S4
  have S5 := sw_x0_spec_gen code .x12 sp v6 24 (base + 32) hf8
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at S5
  rw [show (base + 32) + 4 = base + 36 from by bv_addr] at S5
  have S5f := cpsTriple_frame_left code (base + 32) (base + 36) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) S5
  have S6 := sw_x0_spec_gen code .x12 sp v7 28 (base + 36) hf9
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at S6
  rw [show (base + 36) + 4 = base + 40 from by bv_addr] at S6
  have S6f := cpsTriple_frame_left code (base + 36) (base + 40) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) S6
  -- Step 9: JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 40) hf10
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 4) ↦ₘ (0 : Word)) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 12) ↦ₘ (0 : Word)) ** ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hf10
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear LL S0 S1 S2 S3 S4 S5 S6
  have c01 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) LLf S0f; clear LLf S0f
  have c02 := cpsTriple_seq_with_perm code base (base + 16) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 S1f; clear c01 S1f
  have c03 := cpsTriple_seq_with_perm code base (base + 20) (base + 24) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 S2f; clear c02 S2f
  have c04 := cpsTriple_seq_with_perm code base (base + 24) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 S3f; clear c03 S3f
  have c05 := cpsTriple_seq_with_perm code base (base + 28) (base + 32) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 S4f; clear c04 S4f
  have c06 := cpsTriple_seq_with_perm code base (base + 32) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 S5f; clear c05 S5f
  have c07 := cpsTriple_seq_with_perm code base (base + 36) (base + 40) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 S6f; clear c06 S6f
  have cfull := cpsTriple_seq_with_perm code base (base + 40) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_6 (limb_shift=6, 17 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 6: limb_shift=6.
    Result[0] = (value[6] >>> bs) ||| ((value[7] <<< as) &&& mask),
    Result[1] = value[7] >>> bs, rest = 0.
    Comprises: shr_merge_limb(24,28,0), shr_last_limb(4), 6× SW, JAL.
    17 instructions from base to exit (via JAL). -/
theorem shr_body_6_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- shr_merge_limb(24,28,0): 7 instructions at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 24))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 28))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- shr_last_limb(4): 3 instructions at base+28..base+36
    (hl0 : code (base + 28) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 36) = some (.SW .x12 .x5 4))
    -- 6 SW zeros at base+40..base+60
    (hs0 : code (base + 40) = some (.SW .x12 .x0 8))
    (hs1 : code (base + 44) = some (.SW .x12 .x0 12))
    (hs2 : code (base + 48) = some (.SW .x12 .x0 16))
    (hs3 : code (base + 52) = some (.SW .x12 .x0 20))
    (hs4 : code (base + 56) = some (.SW .x12 .x0 24))
    (hs5 : code (base + 60) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 64) = some (.JAL .x0 jal_off))
    (hexit : (base + 64) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  -- Extract memory validity
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: shr_merge_limb(24, 28, 0): base → base+28
  have MM := shr_merge_limb_spec code 24 28 0 sp v6 v7 v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv24 hv28
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_24, signExtend12_28, signExtend12_0] at MM
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM
  have MMf := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM
  -- Step 2: shr_last_limb(4): base+28 → base+40
  -- Rewrite fetch addresses: base+32 = (base+28)+4, base+36 = (base+28)+8
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hl1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 4 sp v7 v1
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 28) hl0 hl1 hl2 hv28 (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 28) ((base + 28) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 28) + 12 = base + 40 from by bv_addr] at LLf
  -- Steps 3-8: 6 SW x12, x0, N for offsets 8,12,16,20,24,28
  have T0 := sw_x0_spec_gen code .x12 sp v2 8 (base + 40) hs0
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at T0
  rw [show (base + 40) + 4 = base + 44 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 40) (base + 44) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen code .x12 sp v3 12 (base + 44) hs1
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at T1
  rw [show (base + 44) + 4 = base + 48 from by bv_addr] at T1
  have T1f := cpsTriple_frame_left code (base + 44) (base + 48) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen code .x12 sp v4 16 (base + 48) hs2
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T2
  rw [show (base + 48) + 4 = base + 52 from by bv_addr] at T2
  have T2f := cpsTriple_frame_left code (base + 48) (base + 52) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen code .x12 sp v5v 20 (base + 52) hs3
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T3
  rw [show (base + 52) + 4 = base + 56 from by bv_addr] at T3
  have T3f := cpsTriple_frame_left code (base + 52) (base + 56) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T3
  have T4 := sw_x0_spec_gen code .x12 sp v6 24 (base + 56) hs4
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T4
  rw [show (base + 56) + 4 = base + 60 from by bv_addr] at T4
  have T4f := cpsTriple_frame_left code (base + 56) (base + 60) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T4
  have T5 := sw_x0_spec_gen code .x12 sp v7 28 (base + 60) hs5
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T5
  rw [show (base + 60) + 4 = base + 64 from by bv_addr] at T5
  have T5f := cpsTriple_frame_left code (base + 60) (base + 64) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T5
  -- Step 9: JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 64) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 8) ↦ₘ (0 : Word)) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hl0 hl1 hl2 hs0 hs1 hs2 hs3 hs4 hs5 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM LL T0 T1 T2 T3 T4 T5
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 40) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MMf LLf; clear MMf LLf
  have c02 := cpsTriple_seq_with_perm code base (base + 40) (base + 44) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 T0f; clear c01 T0f
  have c03 := cpsTriple_seq_with_perm code base (base + 44) (base + 48) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 T1f; clear c02 T1f
  have c04 := cpsTriple_seq_with_perm code base (base + 48) (base + 52) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T2f; clear c03 T2f
  have c05 := cpsTriple_seq_with_perm code base (base + 52) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T3f; clear c04 T3f
  have c06 := cpsTriple_seq_with_perm code base (base + 56) (base + 60) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T4f; clear c05 T4f
  have c07 := cpsTriple_seq_with_perm code base (base + 60) (base + 64) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T5f; clear c06 T5f
  have cfull := cpsTriple_seq_with_perm code base (base + 64) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_5 (limb_shift=5, 23 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 5: limb_shift=5.
    Result[0] = (v5 >>> bs) ||| ((v6 <<< as) &&& mask),
    Result[1] = (v6 >>> bs) ||| ((v7 <<< as) &&& mask),
    Result[2] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(20,24,0), merge_limb(24,28,4), last_limb(8), 5× SW, JAL.
    23 instructions from base to exit (via JAL). -/
theorem shr_body_5_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_limb(20,24,0): 7 instructions at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 20))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 24))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_limb(24,28,4): 7 instructions at base+28..base+52
    (hn0 : code (base + 28) = some (.LW .x5 .x12 24))
    (hn1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hn2 : code (base + 36) = some (.LW .x10 .x12 28))
    (hn3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hn4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hn5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hn6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- last_limb(8): 3 instructions at base+56..base+64
    (hl0 : code (base + 56) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 64) = some (.SW .x12 .x5 8))
    -- 5 SW zeros at base+68..base+84
    (hs0 : code (base + 68) = some (.SW .x12 .x0 12))
    (hs1 : code (base + 72) = some (.SW .x12 .x0 16))
    (hs2 : code (base + 76) = some (.SW .x12 .x0 20))
    (hs3 : code (base + 80) = some (.SW .x12 .x0 24))
    (hs4 : code (base + 84) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 88) = some (.JAL .x0 jal_off))
    (hexit : (base + 88) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  -- Extract memory validity
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_limb(20,24,0): base → base+28
  have MM1 := shr_merge_limb_spec code 20 24 0 sp v5v v6 v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv20 hv24
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_20, signExtend12_24, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(24,28,4): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hn1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hn2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hn3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hn4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hn5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hn6
  have MM2 := shr_merge_limb_spec code 24 28 4 sp v6 v7 v1
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hn0 hn1 hn2 hn3 hn4 hn5 hn6 hv24 hv28
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_24, signExtend12_28, signExtend12_4] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: last_limb(8): base+56 → base+68
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hl1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 8 sp v7 v2
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 56) hl0 hl1 hl2 hv28 (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 56) ((base + 56) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 56) + 12 = base + 68 from by bv_addr] at LLf
  -- Steps 4-8: 5 SW x12, x0, N for offsets 12,16,20,24,28
  have T0 := sw_x0_spec_gen code .x12 sp v3 12 (base + 68) hs0
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at T0
  rw [show (base + 68) + 4 = base + 72 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 68) (base + 72) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen code .x12 sp v4 16 (base + 72) hs1
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T1
  rw [show (base + 72) + 4 = base + 76 from by bv_addr] at T1
  have T1f := cpsTriple_frame_left code (base + 72) (base + 76) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen code .x12 sp v5v 20 (base + 76) hs2
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T2
  rw [show (base + 76) + 4 = base + 80 from by bv_addr] at T2
  have T2f := cpsTriple_frame_left code (base + 76) (base + 80) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen code .x12 sp v6 24 (base + 80) hs3
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T3
  rw [show (base + 80) + 4 = base + 84 from by bv_addr] at T3
  have T3f := cpsTriple_frame_left code (base + 80) (base + 84) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T3
  have T4 := sw_x0_spec_gen code .x12 sp v7 28 (base + 84) hs4
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T4
  rw [show (base + 84) + 4 = base + 88 from by bv_addr] at T4
  have T4f := cpsTriple_frame_left code (base + 84) (base + 88) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T4
  -- Step 9: JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 88) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 12) ↦ₘ (0 : Word)) **
     ((sp + 16) ↦ₘ (0 : Word)) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hn0 hn1 hn2 hn3 hn4 hn5 hn6
  clear hl0 hl1 hl2 hs0 hs1 hs2 hs3 hs4 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 LL T0 T1 T2 T3 T4
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 68) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 LLf; clear c01 LLf
  have c03 := cpsTriple_seq_with_perm code base (base + 68) (base + 72) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 T0f; clear c02 T0f
  have c04 := cpsTriple_seq_with_perm code base (base + 72) (base + 76) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T1f; clear c03 T1f
  have c05 := cpsTriple_seq_with_perm code base (base + 76) (base + 80) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T2f; clear c04 T2f
  have c06 := cpsTriple_seq_with_perm code base (base + 80) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T3f; clear c05 T3f
  have c07 := cpsTriple_seq_with_perm code base (base + 84) (base + 88) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T4f; clear c06 T4f
  have cfull := cpsTriple_seq_with_perm code base (base + 88) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_4 (limb_shift=4, 29 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 4: limb_shift=4.
    Result[0] = (v4 >>> bs) ||| ((v5 <<< as) &&& mask),
    Result[1] = (v5 >>> bs) ||| ((v6 <<< as) &&& mask),
    Result[2] = (v6 >>> bs) ||| ((v7 <<< as) &&& mask),
    Result[3] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(16,20,0), merge_limb(20,24,4), merge_limb(24,28,8),
    last_limb(12), 4× SW, JAL. 29 instructions. -/
theorem shr_body_4_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_limb(16,20,0): 7 at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 16))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 20))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_limb(20,24,4): 7 at base+28..base+52
    (hn0 : code (base + 28) = some (.LW .x5 .x12 20))
    (hn1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hn2 : code (base + 36) = some (.LW .x10 .x12 24))
    (hn3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hn4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hn5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hn6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- merge_limb(24,28,8): 7 at base+56..base+80
    (hp0 : code (base + 56) = some (.LW .x5 .x12 24))
    (hp1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hp2 : code (base + 64) = some (.LW .x10 .x12 28))
    (hp3 : code (base + 68) = some (.SLL .x10 .x10 .x7))
    (hp4 : code (base + 72) = some (.AND .x10 .x10 .x11))
    (hp5 : code (base + 76) = some (.OR .x5 .x5 .x10))
    (hp6 : code (base + 80) = some (.SW .x12 .x5 8))
    -- last_limb(12): 3 at base+84..base+92
    (hl0 : code (base + 84) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 88) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 92) = some (.SW .x12 .x5 12))
    -- 4 SW zeros at base+96..base+108
    (hs0 : code (base + 96) = some (.SW .x12 .x0 16))
    (hs1 : code (base + 100) = some (.SW .x12 .x0 20))
    (hs2 : code (base + 104) = some (.SW .x12 .x0 24))
    (hs3 : code (base + 108) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 112) = some (.JAL .x0 jal_off))
    (hexit : (base + 112) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  -- Extract memory validity
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_limb(16,20,0): base → base+28
  have MM1 := shr_merge_limb_spec code 16 20 0 sp v4 v5v v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv16 hv20
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_16, signExtend12_20, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(20,24,4): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hn1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hn2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hn3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hn4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hn5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hn6
  have MM2 := shr_merge_limb_spec code 20 24 4 sp v5v v6 v1
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hn0 hn1 hn2 hn3 hn4 hn5 hn6 hv20 hv24
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_20, signExtend12_24, signExtend12_4] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: merge_limb(24,28,8): base+56 → base+84
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hp1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hp2
  rw [show (base + 68 : Addr) = (base + 56) + 12 from by bv_addr] at hp3
  rw [show (base + 72 : Addr) = (base + 56) + 16 from by bv_addr] at hp4
  rw [show (base + 76 : Addr) = (base + 56) + 20 from by bv_addr] at hp5
  rw [show (base + 80 : Addr) = (base + 56) + 24 from by bv_addr] at hp6
  have MM3 := shr_merge_limb_spec code 24 28 8 sp v6 v7 v2
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hv24 hv28
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_24, signExtend12_28, signExtend12_8] at MM3
  have MM3f := cpsTriple_frame_left code (base + 56) ((base + 56) + 28) _ _
    ((sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_addr] at MM3f
  -- Step 4: last_limb(12): base+84 → base+96
  rw [show (base + 88 : Addr) = (base + 84) + 4 from by bv_addr] at hl1
  rw [show (base + 92 : Addr) = (base + 84) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 12 sp v7 v3
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 84) hl0 hl1 hl2 hv28 (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 84) ((base + 84) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 84) + 12 = base + 96 from by bv_addr] at LLf
  -- Steps 5-8: 4 SW zeros
  have T0 := sw_x0_spec_gen code .x12 sp v4 16 (base + 96) hs0
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at T0
  rw [show (base + 96) + 4 = base + 100 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 96) (base + 100) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen code .x12 sp v5v 20 (base + 100) hs1
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T1
  rw [show (base + 100) + 4 = base + 104 from by bv_addr] at T1
  have T1f := cpsTriple_frame_left code (base + 100) (base + 104) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen code .x12 sp v6 24 (base + 104) hs2
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T2
  rw [show (base + 104) + 4 = base + 108 from by bv_addr] at T2
  have T2f := cpsTriple_frame_left code (base + 104) (base + 108) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T2
  have T3 := sw_x0_spec_gen code .x12 sp v7 28 (base + 108) hs3
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T3
  rw [show (base + 108) + 4 = base + 112 from by bv_addr] at T3
  have T3f := cpsTriple_frame_left code (base + 108) (base + 112) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T3
  -- JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 112) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 16) ↦ₘ (0 : Word)) **
     ((sp + 20) ↦ₘ (0 : Word)) ** ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hn0 hn1 hn2 hn3 hn4 hn5 hn6
  clear hp0 hp1 hp2 hp3 hp4 hp5 hp6 hl0 hl1 hl2 hs0 hs1 hs2 hs3 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 MM3 LL T0 T1 T2 T3
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm code base (base + 84) (base + 96) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 LLf; clear c02 LLf
  have c04 := cpsTriple_seq_with_perm code base (base + 96) (base + 100) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 T0f; clear c03 T0f
  have c05 := cpsTriple_seq_with_perm code base (base + 100) (base + 104) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T1f; clear c04 T1f
  have c06 := cpsTriple_seq_with_perm code base (base + 104) (base + 108) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T2f; clear c05 T2f
  have c07 := cpsTriple_seq_with_perm code base (base + 108) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T3f; clear c06 T3f
  have cfull := cpsTriple_seq_with_perm code base (base + 112) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_3 (limb_shift=3, 35 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 3: limb_shift=3.
    Result[0..3] = merge results, Result[4] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(12,16,0), merge_limb(16,20,4), merge_limb(20,24,8),
    merge_limb(24,28,12), last_limb(16), 3× SW, JAL. 35 instructions. -/
theorem shr_body_3_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_limb(12,16,0): 7 at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 12))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 16))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_limb(16,20,4): 7 at base+28..base+52
    (hn0 : code (base + 28) = some (.LW .x5 .x12 16))
    (hn1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hn2 : code (base + 36) = some (.LW .x10 .x12 20))
    (hn3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hn4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hn5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hn6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- merge_limb(20,24,8): 7 at base+56..base+80
    (hp0 : code (base + 56) = some (.LW .x5 .x12 20))
    (hp1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hp2 : code (base + 64) = some (.LW .x10 .x12 24))
    (hp3 : code (base + 68) = some (.SLL .x10 .x10 .x7))
    (hp4 : code (base + 72) = some (.AND .x10 .x10 .x11))
    (hp5 : code (base + 76) = some (.OR .x5 .x5 .x10))
    (hp6 : code (base + 80) = some (.SW .x12 .x5 8))
    -- merge_limb(24,28,12): 7 at base+84..base+108
    (hq0 : code (base + 84) = some (.LW .x5 .x12 24))
    (hq1 : code (base + 88) = some (.SRL .x5 .x5 .x6))
    (hq2 : code (base + 92) = some (.LW .x10 .x12 28))
    (hq3 : code (base + 96) = some (.SLL .x10 .x10 .x7))
    (hq4 : code (base + 100) = some (.AND .x10 .x10 .x11))
    (hq5 : code (base + 104) = some (.OR .x5 .x5 .x10))
    (hq6 : code (base + 108) = some (.SW .x12 .x5 12))
    -- last_limb(16): 3 at base+112..base+120
    (hl0 : code (base + 112) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 116) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 120) = some (.SW .x12 .x5 16))
    -- 3 SW zeros at base+124..base+132
    (hs0 : code (base + 124) = some (.SW .x12 .x0 20))
    (hs1 : code (base + 128) = some (.SW .x12 .x0 24))
    (hs2 : code (base + 132) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 136) = some (.JAL .x0 jal_off))
    (hexit : (base + 136) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result4) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_limb(12,16,0): base → base+28
  have MM1 := shr_merge_limb_spec code 12 16 0 sp v3 v4 v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv12 hv16
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_12, signExtend12_16, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(16,20,4): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hn1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hn2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hn3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hn4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hn5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hn6
  have MM2 := shr_merge_limb_spec code 16 20 4 sp v4 v5v v1
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hn0 hn1 hn2 hn3 hn4 hn5 hn6 hv16 hv20
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_16, signExtend12_20, signExtend12_4] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: merge_limb(20,24,8): base+56 → base+84
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hp1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hp2
  rw [show (base + 68 : Addr) = (base + 56) + 12 from by bv_addr] at hp3
  rw [show (base + 72 : Addr) = (base + 56) + 16 from by bv_addr] at hp4
  rw [show (base + 76 : Addr) = (base + 56) + 20 from by bv_addr] at hp5
  rw [show (base + 80 : Addr) = (base + 56) + 24 from by bv_addr] at hp6
  have MM3 := shr_merge_limb_spec code 20 24 8 sp v5v v6 v2
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hv20 hv24
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_20, signExtend12_24, signExtend12_8] at MM3
  have MM3f := cpsTriple_frame_left code (base + 56) ((base + 56) + 28) _ _
    ((sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_addr] at MM3f
  -- Step 4: merge_limb(24,28,12): base+84 → base+112
  rw [show (base + 88 : Addr) = (base + 84) + 4 from by bv_addr] at hq1
  rw [show (base + 92 : Addr) = (base + 84) + 8 from by bv_addr] at hq2
  rw [show (base + 96 : Addr) = (base + 84) + 12 from by bv_addr] at hq3
  rw [show (base + 100 : Addr) = (base + 84) + 16 from by bv_addr] at hq4
  rw [show (base + 104 : Addr) = (base + 84) + 20 from by bv_addr] at hq5
  rw [show (base + 108 : Addr) = (base + 84) + 24 from by bv_addr] at hq6
  have MM4 := shr_merge_limb_spec code 24 28 12 sp v6 v7 v3
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    hq0 hq1 hq2 hq3 hq4 hq5 hq6 hv24 hv28
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_24, signExtend12_28, signExtend12_12] at MM4
  have MM4f := cpsTriple_frame_left code (base + 84) ((base + 84) + 28) _ _
    ((sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_addr] at MM4f
  -- Step 5: last_limb(16): base+112 → base+124
  rw [show (base + 116 : Addr) = (base + 112) + 4 from by bv_addr] at hl1
  rw [show (base + 120 : Addr) = (base + 112) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 16 sp v7 v4
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 112) hl0 hl1 hl2 hv28 (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 112) ((base + 112) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 112) + 12 = base + 124 from by bv_addr] at LLf
  -- Steps 6-8: 3 SW zeros
  have T0 := sw_x0_spec_gen code .x12 sp v5v 20 (base + 124) hs0
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at T0
  rw [show (base + 124) + 4 = base + 128 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 124) (base + 128) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen code .x12 sp v6 24 (base + 128) hs1
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T1
  rw [show (base + 128) + 4 = base + 132 from by bv_addr] at T1
  have T1f := cpsTriple_frame_left code (base + 128) (base + 132) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) T1
  have T2 := sw_x0_spec_gen code .x12 sp v7 28 (base + 132) hs2
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T2
  rw [show (base + 132) + 4 = base + 136 from by bv_addr] at T2
  have T2f := cpsTriple_frame_left code (base + 132) (base + 136) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T2
  -- JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 136) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 20) ↦ₘ (0 : Word)) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hn0 hn1 hn2 hn3 hn4 hn5 hn6
  clear hp0 hp1 hp2 hp3 hp4 hp5 hp6 hq0 hq1 hq2 hq3 hq4 hq5 hq6
  clear hl0 hl1 hl2 hs0 hs1 hs2 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 MM3 MM4 LL T0 T1 T2
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm code base (base + 84) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm code base (base + 112) (base + 124) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 LLf; clear c03 LLf
  have c05 := cpsTriple_seq_with_perm code base (base + 124) (base + 128) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 T0f; clear c04 T0f
  have c06 := cpsTriple_seq_with_perm code base (base + 128) (base + 132) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T1f; clear c05 T1f
  have c07 := cpsTriple_seq_with_perm code base (base + 132) (base + 136) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T2f; clear c06 T2f
  have cfull := cpsTriple_seq_with_perm code base (base + 136) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_2 (limb_shift=2, 41 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 2: limb_shift=2.
    Result[0..4] = merge results, Result[5] = v7 >>> bs, rest = 0.
    Comprises: 5× merge_limb, last_limb(20), 2× SW, JAL. 41 instructions. -/
theorem shr_body_2_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_limb(8,12,0): 7 at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 8))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 12))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_limb(12,16,4): 7 at base+28..base+52
    (hn0 : code (base + 28) = some (.LW .x5 .x12 12))
    (hn1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hn2 : code (base + 36) = some (.LW .x10 .x12 16))
    (hn3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hn4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hn5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hn6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- merge_limb(16,20,8): 7 at base+56..base+80
    (hp0 : code (base + 56) = some (.LW .x5 .x12 16))
    (hp1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hp2 : code (base + 64) = some (.LW .x10 .x12 20))
    (hp3 : code (base + 68) = some (.SLL .x10 .x10 .x7))
    (hp4 : code (base + 72) = some (.AND .x10 .x10 .x11))
    (hp5 : code (base + 76) = some (.OR .x5 .x5 .x10))
    (hp6 : code (base + 80) = some (.SW .x12 .x5 8))
    -- merge_limb(20,24,12): 7 at base+84..base+108
    (hq0 : code (base + 84) = some (.LW .x5 .x12 20))
    (hq1 : code (base + 88) = some (.SRL .x5 .x5 .x6))
    (hq2 : code (base + 92) = some (.LW .x10 .x12 24))
    (hq3 : code (base + 96) = some (.SLL .x10 .x10 .x7))
    (hq4 : code (base + 100) = some (.AND .x10 .x10 .x11))
    (hq5 : code (base + 104) = some (.OR .x5 .x5 .x10))
    (hq6 : code (base + 108) = some (.SW .x12 .x5 12))
    -- merge_limb(24,28,16): 7 at base+112..base+136
    (hr0 : code (base + 112) = some (.LW .x5 .x12 24))
    (hr1 : code (base + 116) = some (.SRL .x5 .x5 .x6))
    (hr2 : code (base + 120) = some (.LW .x10 .x12 28))
    (hr3 : code (base + 124) = some (.SLL .x10 .x10 .x7))
    (hr4 : code (base + 128) = some (.AND .x10 .x10 .x11))
    (hr5 : code (base + 132) = some (.OR .x5 .x5 .x10))
    (hr6 : code (base + 136) = some (.SW .x12 .x5 16))
    -- last_limb(20): 3 at base+140..base+148
    (hl0 : code (base + 140) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 144) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 148) = some (.SW .x12 .x5 20))
    -- 2 SW zeros at base+152..base+156
    (hs0 : code (base + 152) = some (.SW .x12 .x0 24))
    (hs1 : code (base + 156) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 160) = some (.JAL .x0 jal_off))
    (hexit : (base + 160) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_limb(8,12,0): base → base+28
  have MM1 := shr_merge_limb_spec code 8 12 0 sp v2 v3 v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv8 hv12
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_8, signExtend12_12, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 4) ↦ₘ v1) ** ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(12,16,4): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hn1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hn2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hn3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hn4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hn5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hn6
  have MM2 := shr_merge_limb_spec code 12 16 4 sp v3 v4 v1
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hn0 hn1 hn2 hn3 hn4 hn5 hn6 hv12 hv16
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_12, signExtend12_16, signExtend12_4] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ v2) ** ((sp + 20) ↦ₘ v5v) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: merge_limb(16,20,8): base+56 → base+84
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hp1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hp2
  rw [show (base + 68 : Addr) = (base + 56) + 12 from by bv_addr] at hp3
  rw [show (base + 72 : Addr) = (base + 56) + 16 from by bv_addr] at hp4
  rw [show (base + 76 : Addr) = (base + 56) + 20 from by bv_addr] at hp5
  rw [show (base + 80 : Addr) = (base + 56) + 24 from by bv_addr] at hp6
  have MM3 := shr_merge_limb_spec code 16 20 8 sp v4 v5v v2
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hv16 hv20
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_16, signExtend12_20, signExtend12_8] at MM3
  have MM3f := cpsTriple_frame_left code (base + 56) ((base + 56) + 28) _ _
    ((sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_addr] at MM3f
  -- Step 4: merge_limb(20,24,12): base+84 → base+112
  rw [show (base + 88 : Addr) = (base + 84) + 4 from by bv_addr] at hq1
  rw [show (base + 92 : Addr) = (base + 84) + 8 from by bv_addr] at hq2
  rw [show (base + 96 : Addr) = (base + 84) + 12 from by bv_addr] at hq3
  rw [show (base + 100 : Addr) = (base + 84) + 16 from by bv_addr] at hq4
  rw [show (base + 104 : Addr) = (base + 84) + 20 from by bv_addr] at hq5
  rw [show (base + 108 : Addr) = (base + 84) + 24 from by bv_addr] at hq6
  have MM4 := shr_merge_limb_spec code 20 24 12 sp v5v v6 v3
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    hq0 hq1 hq2 hq3 hq4 hq5 hq6 hv20 hv24
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_20, signExtend12_24, signExtend12_12] at MM4
  have MM4f := cpsTriple_frame_left code (base + 84) ((base + 84) + 28) _ _
    ((sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_addr] at MM4f
  -- Step 5: merge_limb(24,28,16): base+112 → base+140
  rw [show (base + 116 : Addr) = (base + 112) + 4 from by bv_addr] at hr1
  rw [show (base + 120 : Addr) = (base + 112) + 8 from by bv_addr] at hr2
  rw [show (base + 124 : Addr) = (base + 112) + 12 from by bv_addr] at hr3
  rw [show (base + 128 : Addr) = (base + 112) + 16 from by bv_addr] at hr4
  rw [show (base + 132 : Addr) = (base + 112) + 20 from by bv_addr] at hr5
  rw [show (base + 136 : Addr) = (base + 112) + 24 from by bv_addr] at hr6
  have MM5 := shr_merge_limb_spec code 24 28 16 sp v6 v7 v4
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hv24 hv28
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_24, signExtend12_28, signExtend12_16] at MM5
  have MM5f := cpsTriple_frame_left code (base + 112) ((base + 112) + 28) _ _
    ((sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_addr] at MM5f
  -- Step 6: last_limb(20): base+140 → base+152
  rw [show (base + 144 : Addr) = (base + 140) + 4 from by bv_addr] at hl1
  rw [show (base + 148 : Addr) = (base + 140) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 20 sp v7 v5v
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 140) hl0 hl1 hl2 hv28 (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 140) ((base + 140) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6))
    (by pcFree) LL
  rw [show (base + 140) + 12 = base + 152 from by bv_addr] at LLf
  -- Steps 7-8: 2 SW zeros
  have T0 := sw_x0_spec_gen code .x12 sp v6 24 (base + 152) hs0
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at T0
  rw [show (base + 152) + 4 = base + 156 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 152) (base + 156) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) T0
  have T1 := sw_x0_spec_gen code .x12 sp v7 28 (base + 156) hs1
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T1
  rw [show (base + 156) + 4 = base + 160 from by bv_addr] at T1
  have T1f := cpsTriple_frame_left code (base + 156) (base + 160) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 24) ↦ₘ (0 : Word)))
    (by pcFree) T1
  -- JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 160) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) **
     ((sp + 24) ↦ₘ (0 : Word)) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hn0 hn1 hn2 hn3 hn4 hn5 hn6
  clear hp0 hp1 hp2 hp3 hp4 hp5 hp6 hq0 hq1 hq2 hq3 hq4 hq5 hq6
  clear hr0 hr1 hr2 hr3 hr4 hr5 hr6 hl0 hl1 hl2 hs0 hs1 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 MM3 MM4 MM5 LL T0 T1
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm code base (base + 84) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm code base (base + 112) (base + 140) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm code base (base + 140) (base + 152) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 LLf; clear c04 LLf
  have c06 := cpsTriple_seq_with_perm code base (base + 152) (base + 156) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 T0f; clear c05 T0f
  have c07 := cpsTriple_seq_with_perm code base (base + 156) (base + 160) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T1f; clear c06 T1f
  have cfull := cpsTriple_seq_with_perm code base (base + 160) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_1 (limb_shift=1, 47 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 1: limb_shift=1.
    Result[0..5] = merge results, Result[6] = v7 >>> bs, Result[7] = 0.
    Comprises: 6× merge_limb, last_limb(24), 1× SW, JAL. 47 instructions. -/
theorem shr_body_1_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_limb(4,8,0): 7 at base..base+24
    (hm0 : code base = some (.LW .x5 .x12 4))
    (hm1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (hm2 : code (base + 8) = some (.LW .x10 .x12 8))
    (hm3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (hm4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (hm5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (hm6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_limb(8,12,4): 7 at base+28..base+52
    (hn0 : code (base + 28) = some (.LW .x5 .x12 8))
    (hn1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hn2 : code (base + 36) = some (.LW .x10 .x12 12))
    (hn3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hn4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hn5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hn6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- merge_limb(12,16,8): 7 at base+56..base+80
    (hp0 : code (base + 56) = some (.LW .x5 .x12 12))
    (hp1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hp2 : code (base + 64) = some (.LW .x10 .x12 16))
    (hp3 : code (base + 68) = some (.SLL .x10 .x10 .x7))
    (hp4 : code (base + 72) = some (.AND .x10 .x10 .x11))
    (hp5 : code (base + 76) = some (.OR .x5 .x5 .x10))
    (hp6 : code (base + 80) = some (.SW .x12 .x5 8))
    -- merge_limb(16,20,12): 7 at base+84..base+108
    (hq0 : code (base + 84) = some (.LW .x5 .x12 16))
    (hq1 : code (base + 88) = some (.SRL .x5 .x5 .x6))
    (hq2 : code (base + 92) = some (.LW .x10 .x12 20))
    (hq3 : code (base + 96) = some (.SLL .x10 .x10 .x7))
    (hq4 : code (base + 100) = some (.AND .x10 .x10 .x11))
    (hq5 : code (base + 104) = some (.OR .x5 .x5 .x10))
    (hq6 : code (base + 108) = some (.SW .x12 .x5 12))
    -- merge_limb(20,24,16): 7 at base+112..base+136
    (hr0 : code (base + 112) = some (.LW .x5 .x12 20))
    (hr1 : code (base + 116) = some (.SRL .x5 .x5 .x6))
    (hr2 : code (base + 120) = some (.LW .x10 .x12 24))
    (hr3 : code (base + 124) = some (.SLL .x10 .x10 .x7))
    (hr4 : code (base + 128) = some (.AND .x10 .x10 .x11))
    (hr5 : code (base + 132) = some (.OR .x5 .x5 .x10))
    (hr6 : code (base + 136) = some (.SW .x12 .x5 16))
    -- merge_limb(24,28,20): 7 at base+140..base+164
    (ht0 : code (base + 140) = some (.LW .x5 .x12 24))
    (ht1 : code (base + 144) = some (.SRL .x5 .x5 .x6))
    (ht2 : code (base + 148) = some (.LW .x10 .x12 28))
    (ht3 : code (base + 152) = some (.SLL .x10 .x10 .x7))
    (ht4 : code (base + 156) = some (.AND .x10 .x10 .x11))
    (ht5 : code (base + 160) = some (.OR .x5 .x5 .x10))
    (ht6 : code (base + 164) = some (.SW .x12 .x5 20))
    -- last_limb(24): 3 at base+168..base+176
    (hl0 : code (base + 168) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 172) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 176) = some (.SW .x12 .x5 24))
    -- 1 SW zero at base+180
    (hz0 : code (base + 180) = some (.SW .x12 .x0 28))
    -- JAL x0
    (hj : code (base + 184) = some (.JAL .x0 jal_off))
    (hexit : (base + 184) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result6 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result6) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ 0)) := by
  simp only
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_limb(4,8,0): base → base+28
  have MM1 := shr_merge_limb_spec code 4 8 0 sp v1 v2 v0 v5 v10 bit_shift anti_shift mask base
    hm0 hm1 hm2 hm3 hm4 hm5 hm6 hv4 hv8
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
  simp only [signExtend12_4, signExtend12_8, signExtend12_0] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_limb(8,12,4): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hn1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hn2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hn3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hn4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hn5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hn6
  have MM2 := shr_merge_limb_spec code 8 12 4 sp v2 v3 v1
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hn0 hn1 hn2 hn3 hn4 hn5 hn6 hv8 hv12
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_8, signExtend12_12, signExtend12_4] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: merge_limb(12,16,8): base+56 → base+84
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hp1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hp2
  rw [show (base + 68 : Addr) = (base + 56) + 12 from by bv_addr] at hp3
  rw [show (base + 72 : Addr) = (base + 56) + 16 from by bv_addr] at hp4
  rw [show (base + 76 : Addr) = (base + 56) + 20 from by bv_addr] at hp5
  rw [show (base + 80 : Addr) = (base + 56) + 24 from by bv_addr] at hp6
  have MM3 := shr_merge_limb_spec code 12 16 8 sp v3 v4 v2
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hv12 hv16
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_12, signExtend12_16, signExtend12_8] at MM3
  have MM3f := cpsTriple_frame_left code (base + 56) ((base + 56) + 28) _ _
    ((sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_addr] at MM3f
  -- Step 4: merge_limb(16,20,12): base+84 → base+112
  rw [show (base + 88 : Addr) = (base + 84) + 4 from by bv_addr] at hq1
  rw [show (base + 92 : Addr) = (base + 84) + 8 from by bv_addr] at hq2
  rw [show (base + 96 : Addr) = (base + 84) + 12 from by bv_addr] at hq3
  rw [show (base + 100 : Addr) = (base + 84) + 16 from by bv_addr] at hq4
  rw [show (base + 104 : Addr) = (base + 84) + 20 from by bv_addr] at hq5
  rw [show (base + 108 : Addr) = (base + 84) + 24 from by bv_addr] at hq6
  have MM4 := shr_merge_limb_spec code 16 20 12 sp v4 v5v v3
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    hq0 hq1 hq2 hq3 hq4 hq5 hq6 hv16 hv20
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_16, signExtend12_20, signExtend12_12] at MM4
  have MM4f := cpsTriple_frame_left code (base + 84) ((base + 84) + 28) _ _
    ((sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_addr] at MM4f
  -- Step 5: merge_limb(20,24,16): base+112 → base+140
  rw [show (base + 116 : Addr) = (base + 112) + 4 from by bv_addr] at hr1
  rw [show (base + 120 : Addr) = (base + 112) + 8 from by bv_addr] at hr2
  rw [show (base + 124 : Addr) = (base + 112) + 12 from by bv_addr] at hr3
  rw [show (base + 128 : Addr) = (base + 112) + 16 from by bv_addr] at hr4
  rw [show (base + 132 : Addr) = (base + 112) + 20 from by bv_addr] at hr5
  rw [show (base + 136 : Addr) = (base + 112) + 24 from by bv_addr] at hr6
  have MM5 := shr_merge_limb_spec code 20 24 16 sp v5v v6 v4
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hv20 hv24
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_20, signExtend12_24, signExtend12_16] at MM5
  have MM5f := cpsTriple_frame_left code (base + 112) ((base + 112) + 28) _ _
    ((sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_addr] at MM5f
  -- Step 6: merge_limb(24,28,20): base+140 → base+168
  rw [show (base + 144 : Addr) = (base + 140) + 4 from by bv_addr] at ht1
  rw [show (base + 148 : Addr) = (base + 140) + 8 from by bv_addr] at ht2
  rw [show (base + 152 : Addr) = (base + 140) + 12 from by bv_addr] at ht3
  rw [show (base + 156 : Addr) = (base + 140) + 16 from by bv_addr] at ht4
  rw [show (base + 160 : Addr) = (base + 140) + 20 from by bv_addr] at ht5
  rw [show (base + 164 : Addr) = (base + 140) + 24 from by bv_addr] at ht6
  have MM6 := shr_merge_limb_spec code 24 28 20 sp v6 v7 v5v
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140)
    ht0 ht1 ht2 ht3 ht4 ht5 ht6 hv24 hv28
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_24, signExtend12_28, signExtend12_20] at MM6
  have MM6f := cpsTriple_frame_left code (base + 140) ((base + 140) + 28) _ _
    ((sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) MM6
  rw [show (base + 140) + 28 = base + 168 from by bv_addr] at MM6f
  -- Step 7: last_limb(24): base+168 → base+180
  rw [show (base + 172 : Addr) = (base + 168) + 4 from by bv_addr] at hl1
  rw [show (base + 176 : Addr) = (base + 168) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_spec code 24 sp v7 v6
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 168) hl0 hl1 hl2 hv28 (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24, signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 168) ((base + 168) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) LL
  rw [show (base + 168) + 12 = base + 180 from by bv_addr] at LLf
  -- Step 8: 1 SW zero
  have T0 := sw_x0_spec_gen code .x12 sp v7 28 (base + 180) hz0
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at T0
  rw [show (base + 180) + 4 = base + 184 from by bv_addr] at T0
  have T0f := cpsTriple_frame_left code (base + 180) (base + 184) _ _
    ((.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ (v7 >>> (bit_shift.toNat % 32))))
    (by pcFree) T0
  -- JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 184) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ (v7 >>> (bit_shift.toNat % 32))) ** ((sp + 28) ↦ₘ (0 : Word)))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear hm0 hm1 hm2 hm3 hm4 hm5 hm6 hn0 hn1 hn2 hn3 hn4 hn5 hn6
  clear hp0 hp1 hp2 hp3 hp4 hp5 hp6 hq0 hq1 hq2 hq3 hq4 hq5 hq6
  clear hr0 hr1 hr2 hr3 hr4 hr5 hr6 ht0 ht1 ht2 ht3 ht4 ht5 ht6
  clear hl0 hl1 hl2 hz0 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 MM3 MM4 MM5 MM6 LL T0
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm code base (base + 84) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm code base (base + 112) (base + 140) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm code base (base + 140) (base + 168) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 MM6f; clear c04 MM6f
  have c06 := cpsTriple_seq_with_perm code base (base + 168) (base + 180) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 LLf; clear c05 LLf
  have c07 := cpsTriple_seq_with_perm code base (base + 180) (base + 184) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 T0f; clear c06 T0f
  have cfull := cpsTriple_seq_with_perm code base (base + 184) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

-- ============================================================================
-- Shift body spec: body_0 (limb_shift=0, 53 instructions)
-- ============================================================================

set_option maxHeartbeats 6400000 in
/-- Shift body 0: limb_shift=0. All merge limbs are in-place (src_off = dst_off).
    Result[i] = (v[i] >>> bs) ||| ((v[i+1] <<< as) &&& mask), Result[7] = v7 >>> bs.
    Comprises: 7× merge_limb_inplace, last_limb_inplace, JAL. 53 instructions. -/
theorem shr_body_0_spec (code : CodeMem) (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    -- merge_inplace(0,4): 7 at base..base+24
    (ha0 : code base = some (.LW .x5 .x12 0))
    (ha1 : code (base + 4) = some (.SRL .x5 .x5 .x6))
    (ha2 : code (base + 8) = some (.LW .x10 .x12 4))
    (ha3 : code (base + 12) = some (.SLL .x10 .x10 .x7))
    (ha4 : code (base + 16) = some (.AND .x10 .x10 .x11))
    (ha5 : code (base + 20) = some (.OR .x5 .x5 .x10))
    (ha6 : code (base + 24) = some (.SW .x12 .x5 0))
    -- merge_inplace(4,8): 7 at base+28..base+52
    (hb0 : code (base + 28) = some (.LW .x5 .x12 4))
    (hb1 : code (base + 32) = some (.SRL .x5 .x5 .x6))
    (hb2 : code (base + 36) = some (.LW .x10 .x12 8))
    (hb3 : code (base + 40) = some (.SLL .x10 .x10 .x7))
    (hb4 : code (base + 44) = some (.AND .x10 .x10 .x11))
    (hb5 : code (base + 48) = some (.OR .x5 .x5 .x10))
    (hb6 : code (base + 52) = some (.SW .x12 .x5 4))
    -- merge_inplace(8,12): 7 at base+56..base+80
    (hc0 : code (base + 56) = some (.LW .x5 .x12 8))
    (hc1 : code (base + 60) = some (.SRL .x5 .x5 .x6))
    (hc2 : code (base + 64) = some (.LW .x10 .x12 12))
    (hc3 : code (base + 68) = some (.SLL .x10 .x10 .x7))
    (hc4 : code (base + 72) = some (.AND .x10 .x10 .x11))
    (hc5 : code (base + 76) = some (.OR .x5 .x5 .x10))
    (hc6 : code (base + 80) = some (.SW .x12 .x5 8))
    -- merge_inplace(12,16): 7 at base+84..base+108
    (hd0 : code (base + 84) = some (.LW .x5 .x12 12))
    (hd1 : code (base + 88) = some (.SRL .x5 .x5 .x6))
    (hd2 : code (base + 92) = some (.LW .x10 .x12 16))
    (hd3 : code (base + 96) = some (.SLL .x10 .x10 .x7))
    (hd4 : code (base + 100) = some (.AND .x10 .x10 .x11))
    (hd5 : code (base + 104) = some (.OR .x5 .x5 .x10))
    (hd6 : code (base + 108) = some (.SW .x12 .x5 12))
    -- merge_inplace(16,20): 7 at base+112..base+136
    (he0 : code (base + 112) = some (.LW .x5 .x12 16))
    (he1 : code (base + 116) = some (.SRL .x5 .x5 .x6))
    (he2 : code (base + 120) = some (.LW .x10 .x12 20))
    (he3 : code (base + 124) = some (.SLL .x10 .x10 .x7))
    (he4 : code (base + 128) = some (.AND .x10 .x10 .x11))
    (he5 : code (base + 132) = some (.OR .x5 .x5 .x10))
    (he6 : code (base + 136) = some (.SW .x12 .x5 16))
    -- merge_inplace(20,24): 7 at base+140..base+164
    (hf0 : code (base + 140) = some (.LW .x5 .x12 20))
    (hf1 : code (base + 144) = some (.SRL .x5 .x5 .x6))
    (hf2 : code (base + 148) = some (.LW .x10 .x12 24))
    (hf3 : code (base + 152) = some (.SLL .x10 .x10 .x7))
    (hf4 : code (base + 156) = some (.AND .x10 .x10 .x11))
    (hf5 : code (base + 160) = some (.OR .x5 .x5 .x10))
    (hf6 : code (base + 164) = some (.SW .x12 .x5 20))
    -- merge_inplace(24,28): 7 at base+168..base+192
    (hg0 : code (base + 168) = some (.LW .x5 .x12 24))
    (hg1 : code (base + 172) = some (.SRL .x5 .x5 .x6))
    (hg2 : code (base + 176) = some (.LW .x10 .x12 28))
    (hg3 : code (base + 180) = some (.SLL .x10 .x10 .x7))
    (hg4 : code (base + 184) = some (.AND .x10 .x10 .x11))
    (hg5 : code (base + 188) = some (.OR .x5 .x5 .x10))
    (hg6 : code (base + 192) = some (.SW .x12 .x5 24))
    -- last_limb_inplace: 3 at base+196..base+204
    (hl0 : code (base + 196) = some (.LW .x5 .x12 28))
    (hl1 : code (base + 200) = some (.SRL .x5 .x5 .x6))
    (hl2 : code (base + 204) = some (.SW .x12 .x5 28))
    -- JAL x0
    (hj : code (base + 208) = some (.JAL .x0 jal_off))
    (hexit : (base + 208) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result6 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result7 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple code base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result7) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ result7)) := by
  simp only
  have hv0  := hvalid.fetch 0 sp           (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (sp + 4)     (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (sp + 8)     (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (sp + 12)    (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (sp + 16)    (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (sp + 20)    (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (sp + 24)    (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (sp + 28)    (by omega) (by bv_addr)
  -- Step 1: merge_inplace(0,4): base → base+28
  have MM1 := shr_merge_limb_inplace_spec code 0 4 sp v0 v1 v5 v10 bit_shift anti_shift mask base
    ha0 ha1 ha2 ha3 ha4 ha5 ha6
    (by simp only [signExtend12_0]; rw [show sp + (0 : Word) = sp from by bv_addr]; exact hv0)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_0, signExtend12_4] at MM1
  rw [show sp + (0 : Word) = sp from by bv_addr] at MM1
  have MM1f := cpsTriple_frame_left code base (base + 28) _ _
    (((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM1
  -- Step 2: merge_inplace(4,8): base+28 → base+56
  rw [show (base + 32 : Addr) = (base + 28) + 4 from by bv_addr] at hb1
  rw [show (base + 36 : Addr) = (base + 28) + 8 from by bv_addr] at hb2
  rw [show (base + 40 : Addr) = (base + 28) + 12 from by bv_addr] at hb3
  rw [show (base + 44 : Addr) = (base + 28) + 16 from by bv_addr] at hb4
  rw [show (base + 48 : Addr) = (base + 28) + 20 from by bv_addr] at hb5
  rw [show (base + 52 : Addr) = (base + 28) + 24 from by bv_addr] at hb6
  have MM2 := shr_merge_limb_inplace_spec code 4 8 sp v1 v2
    ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v1 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 28)
    hb0 hb1 hb2 hb3 hb4 hb5 hb6
    (by simp only [signExtend12_4]; exact hv4)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_4, signExtend12_8] at MM2
  have MM2f := cpsTriple_frame_left code (base + 28) ((base + 28) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ v3) ** ((sp + 16) ↦ₘ v4) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM2
  rw [show (base + 28) + 28 = base + 56 from by bv_addr] at MM2f
  -- Step 3: merge_inplace(8,12): base+56 → base+84
  rw [show (base + 60 : Addr) = (base + 56) + 4 from by bv_addr] at hc1
  rw [show (base + 64 : Addr) = (base + 56) + 8 from by bv_addr] at hc2
  rw [show (base + 68 : Addr) = (base + 56) + 12 from by bv_addr] at hc3
  rw [show (base + 72 : Addr) = (base + 56) + 16 from by bv_addr] at hc4
  rw [show (base + 76 : Addr) = (base + 56) + 20 from by bv_addr] at hc5
  rw [show (base + 80 : Addr) = (base + 56) + 24 from by bv_addr] at hc6
  have MM3 := shr_merge_limb_inplace_spec code 8 12 sp v2 v3
    ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 56)
    hc0 hc1 hc2 hc3 hc4 hc5 hc6
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_8, signExtend12_12] at MM3
  have MM3f := cpsTriple_frame_left code (base + 56) ((base + 56) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM3
  rw [show (base + 56) + 28 = base + 84 from by bv_addr] at MM3f
  -- Step 4: merge_inplace(12,16): base+84 → base+112
  rw [show (base + 88 : Addr) = (base + 84) + 4 from by bv_addr] at hd1
  rw [show (base + 92 : Addr) = (base + 84) + 8 from by bv_addr] at hd2
  rw [show (base + 96 : Addr) = (base + 84) + 12 from by bv_addr] at hd3
  rw [show (base + 100 : Addr) = (base + 84) + 16 from by bv_addr] at hd4
  rw [show (base + 104 : Addr) = (base + 84) + 20 from by bv_addr] at hd5
  rw [show (base + 108 : Addr) = (base + 84) + 24 from by bv_addr] at hd6
  have MM4 := shr_merge_limb_inplace_spec code 12 16 sp v3 v4
    ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 84)
    hd0 hd1 hd2 hd3 hd4 hd5 hd6
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_12, signExtend12_16] at MM4
  have MM4f := cpsTriple_frame_left code (base + 84) ((base + 84) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM4
  rw [show (base + 84) + 28 = base + 112 from by bv_addr] at MM4f
  -- Step 5: merge_inplace(16,20): base+112 → base+140
  rw [show (base + 116 : Addr) = (base + 112) + 4 from by bv_addr] at he1
  rw [show (base + 120 : Addr) = (base + 112) + 8 from by bv_addr] at he2
  rw [show (base + 124 : Addr) = (base + 112) + 12 from by bv_addr] at he3
  rw [show (base + 128 : Addr) = (base + 112) + 16 from by bv_addr] at he4
  rw [show (base + 132 : Addr) = (base + 112) + 20 from by bv_addr] at he5
  rw [show (base + 136 : Addr) = (base + 112) + 24 from by bv_addr] at he6
  have MM5 := shr_merge_limb_inplace_spec code 16 20 sp v4 v5v
    ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 112)
    he0 he1 he2 he3 he4 he5 he6
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_16, signExtend12_20] at MM5
  have MM5f := cpsTriple_frame_left code (base + 112) ((base + 112) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
    (by pcFree) MM5
  rw [show (base + 112) + 28 = base + 140 from by bv_addr] at MM5f
  -- Step 6: merge_inplace(20,24): base+140 → base+168
  rw [show (base + 144 : Addr) = (base + 140) + 4 from by bv_addr] at hf1
  rw [show (base + 148 : Addr) = (base + 140) + 8 from by bv_addr] at hf2
  rw [show (base + 152 : Addr) = (base + 140) + 12 from by bv_addr] at hf3
  rw [show (base + 156 : Addr) = (base + 140) + 16 from by bv_addr] at hf4
  rw [show (base + 160 : Addr) = (base + 140) + 20 from by bv_addr] at hf5
  rw [show (base + 164 : Addr) = (base + 140) + 24 from by bv_addr] at hf6
  have MM6 := shr_merge_limb_inplace_spec code 20 24 sp v5v v6
    ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))
    ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 140)
    hf0 hf1 hf2 hf3 hf4 hf5 hf6
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_20, signExtend12_24] at MM6
  have MM6f := cpsTriple_frame_left code (base + 140) ((base + 140) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ v7))
    (by pcFree) MM6
  rw [show (base + 140) + 28 = base + 168 from by bv_addr] at MM6f
  -- Step 7: merge_inplace(24,28): base+168 → base+196
  rw [show (base + 172 : Addr) = (base + 168) + 4 from by bv_addr] at hg1
  rw [show (base + 176 : Addr) = (base + 168) + 8 from by bv_addr] at hg2
  rw [show (base + 180 : Addr) = (base + 168) + 12 from by bv_addr] at hg3
  rw [show (base + 184 : Addr) = (base + 168) + 16 from by bv_addr] at hg4
  rw [show (base + 188 : Addr) = (base + 168) + 20 from by bv_addr] at hg5
  rw [show (base + 192 : Addr) = (base + 168) + 24 from by bv_addr] at hg6
  have MM7 := shr_merge_limb_inplace_spec code 24 28 sp v6 v7
    ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))
    ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    bit_shift anti_shift mask (base + 168)
    hg0 hg1 hg2 hg3 hg4 hg5 hg6
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_24, signExtend12_28] at MM7
  have MM7f := cpsTriple_frame_left code (base + 168) ((base + 168) + 28) _ _
    ((sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) MM7
  rw [show (base + 168) + 28 = base + 196 from by bv_addr] at MM7f
  -- Step 8: last_limb_inplace: base+196 → base+208
  rw [show (base + 200 : Addr) = (base + 196) + 4 from by bv_addr] at hl1
  rw [show (base + 204 : Addr) = (base + 196) + 8 from by bv_addr] at hl2
  have LL := shr_last_limb_inplace_spec code sp v7
    ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))
    bit_shift (base + 196) hl0 hl1 hl2 hv28
  simp only [signExtend12_28] at LL
  have LLf := cpsTriple_frame_left code (base + 196) ((base + 196) + 12) _ _
    ((.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))))
    (by pcFree) LL
  rw [show (base + 196) + 12 = base + 208 from by bv_addr] at LLf
  -- Step 9: JAL x0 to exit
  have JL := jal_x0_spec_gen code jal_off (base + 208) hj
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (v7 >>> (bit_shift.toNat % 32))) ** (.x6 ↦ᵣ bit_shift) **
     (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
     (sp ↦ₘ ((v0 >>> (bit_shift.toNat % 32)) ||| ((v1 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 4) ↦ₘ ((v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 8) ↦ₘ ((v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 12) ↦ₘ ((v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 16) ↦ₘ ((v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 20) ↦ₘ ((v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 24) ↦ₘ ((v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask))) **
     ((sp + 28) ↦ₘ (v7 >>> (bit_shift.toNat % 32))))
    (by pcFree)
  rw [hexit] at JL
  -- Compose all steps
  clear ha0 ha1 ha2 ha3 ha4 ha5 ha6 hb0 hb1 hb2 hb3 hb4 hb5 hb6
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hd0 hd1 hd2 hd3 hd4 hd5 hd6
  clear he0 he1 he2 he3 he4 he5 he6 hf0 hf1 hf2 hf3 hf4 hf5 hf6
  clear hg0 hg1 hg2 hg3 hg4 hg5 hg6 hl0 hl1 hl2 hj
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28
  clear MM1 MM2 MM3 MM4 MM5 MM6 MM7 LL
  have c01 := cpsTriple_seq_with_perm code base (base + 28) (base + 56) _ _ _ _
    (fun _ hp => by xperm_hyp hp) MM1f MM2f; clear MM1f MM2f
  have c02 := cpsTriple_seq_with_perm code base (base + 56) (base + 84) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 MM3f; clear c01 MM3f
  have c03 := cpsTriple_seq_with_perm code base (base + 84) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 MM4f; clear c02 MM4f
  have c04 := cpsTriple_seq_with_perm code base (base + 112) (base + 140) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 MM5f; clear c03 MM5f
  have c05 := cpsTriple_seq_with_perm code base (base + 140) (base + 168) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 MM6f; clear c04 MM6f
  have c06 := cpsTriple_seq_with_perm code base (base + 168) (base + 196) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 MM7f; clear c05 MM7f
  have c07 := cpsTriple_seq_with_perm code base (base + 196) (base + 208) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 LLf; clear c06 LLf
  have cfull := cpsTriple_seq_with_perm code base (base + 208) exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 JL; clear c07 JL
  exact cpsTriple_consequence code base exit _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

end EvmAsm
