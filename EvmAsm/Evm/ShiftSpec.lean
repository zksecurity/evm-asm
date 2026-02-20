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

end EvmAsm
