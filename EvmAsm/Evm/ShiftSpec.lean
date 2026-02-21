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
theorem shr_merge_limb_spec (src_off next_off dst_off : BitVec 12)
    (sp src next dst_old v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 src_off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 src_off
    let mem_next := sp + signExtend12 next_off
    let mem_dst := sp + signExtend12 dst_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple base (base + 28)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_src ↦ₘ src) ** (mem_next ↦ₘ next) ** (mem_dst ↦ₘ result)) := by
  sorry

-- ============================================================================
-- Per-limb Specs: SHR Last Limb (3 instructions)
-- ============================================================================

/-- SHR last limb spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,dst_off

    Computes: result = value[7] >>> bit_shift
    and stores at dst_off. This is the highest non-zero limb in a shift body.

    Preserves: x12, x6, x7, x10, x11, memory at value[7].
    Modifies: x5 (= result), memory at dst. -/
theorem shr_last_limb_spec (dst_off : BitVec 12)
    (sp src dst_old v5 bit_shift : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 dst_off) = true) :
    let mem_src := sp + signExtend12 (28 : BitVec 12)
    let mem_dst := sp + signExtend12 dst_off
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (mem_src ↦ₘ src) ** (mem_dst ↦ₘ result)) := by
  sorry

-- ============================================================================
-- Per-limb Specs: SHR Merge Limb In-place (7 instructions, src_off = dst_off)
-- ============================================================================

/-- SHR merge limb in-place spec (7 instructions):
    Same as shr_merge_limb_spec but src_off = dst_off. The source value is
    read then overwritten in place. Only 2 memory cells needed (no separate dst). -/
theorem shr_merge_limb_inplace_spec (off next_off : BitVec 12)
    (sp src next v5 v10 bit_shift anti_shift mask : Word) (base : Addr)
    (hvalid_loc : isValidMemAccess (sp + signExtend12 off) = true)
    (hvalid_next : isValidMemAccess (sp + signExtend12 next_off) = true) :
    let mem_loc := sp + signExtend12 off
    let mem_next := sp + signExtend12 next_off
    let shifted_src := src >>> (bit_shift.toNat % 32)
    let shifted_next := (next <<< (anti_shift.toNat % 32)) &&& mask
    let result := shifted_src ||| shifted_next
    cpsTriple base (base + 28)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ src) ** (mem_next ↦ₘ next))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ shifted_next) ** (.x11 ↦ᵣ mask) **
       (mem_loc ↦ₘ result) ** (mem_next ↦ₘ next)) := by
  sorry

-- ============================================================================
-- Per-limb Specs: SHR Last Limb In-place (3 instructions, dst_off = 28)
-- ============================================================================

/-- SHR last limb in-place spec (3 instructions):
    LW x5, 28(x12); SRL x5,x5,x6; SW x12,x5,28
    Reads and writes the same memory cell at sp+28. -/
theorem shr_last_limb_inplace_spec
    (sp src v5 bit_shift : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 (28 : BitVec 12)) = true) :
    let mem := sp + signExtend12 (28 : BitVec 12)
    let result := src >>> (bit_shift.toNat % 32)
    cpsTriple base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ src))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result) ** (.x6 ↦ᵣ bit_shift) ** (mem ↦ₘ result)) := by
  sorry

-- ============================================================================
-- Zero-fill helper: SW x12, x0, offset (1 instruction)
-- ============================================================================

/-- Store zero at offset: SW x12, x0, offset.
    Writes 0 to memory at sp + sext(offset). -/
theorem shr_sw_zero_spec (offset : BitVec 12)
    (sp old_val : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 offset) = true) :
    cpsTriple base (base + 4)
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ old_val))
      ((.x12 ↦ᵣ sp) ** ((sp + signExtend12 offset) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- Zero path spec (9 instructions): shift >= 256, result is all zeros
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Zero path spec: ADDI x12, x12, 32 followed by 8 SW x12, x0, N.
    This is used when shift >= 256. Advances sp by 32 and zeros all 8 result limbs. -/
theorem shr_zero_path_spec (sp : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)   -- old values at result locations
    (base : Addr)
    (hvalid : ValidMemRange (sp + 32) 8) :
    let nsp := sp + 32
    cpsTriple base (base + 36)
      ((.x12 ↦ᵣ sp) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- Phase B spec: Extract parameters (7 instructions)
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- Phase B spec: Extract bit_shift, limb_shift, mask, anti_shift from shift0.
    ANDI x6,x5,31; SRLI x5,x5,5; SLTU x11,x0,x6; SUB x11,x0,x11;
    LI x7,32; SUB x7,x7,x6; ADDI x12,x12,32.
    Requires .x0 ↦ᵣ 0 for SLTU and SUB instructions using x0. -/
theorem shr_phase_b_spec (shift0 sp r6 r7 r11 : Word) (base : Addr) :
    let bit_shift := shift0 &&& signExtend12 31
    let limb_shift := shift0 >>> (5 : BitVec 5).toNat
    let cond := if BitVec.ult (0 : Word) bit_shift then (1 : Word) else 0
    let mask := (0 : Word) - cond
    let anti_shift := (32 : Word) - bit_shift
    cpsTriple base (base + 28)
      ((.x5 ↦ᵣ shift0) ** (.x6 ↦ᵣ r6) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ r11) ** (.x7 ↦ᵣ r7) ** (.x12 ↦ᵣ sp))
      ((.x5 ↦ᵣ limb_shift) ** (.x6 ↦ᵣ bit_shift) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ mask) ** (.x7 ↦ᵣ anti_shift) ** (.x12 ↦ᵣ (sp + signExtend12 32))) := by
  sorry

-- ============================================================================
-- Cascade step helper: ADDI x10,x0,k; BEQ x5,x10,off (2 instructions)
-- ============================================================================

/-- Cascade step: ADDI x10,x0,k followed by BEQ x5,x10,off.
    Produces a cpsBranch with clean postconditions (no pure facts).
    Both taken and not-taken paths have the same register state;
    the branch is reflected only in which exit address is reached. -/
theorem shr_cascade_step_spec (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Addr)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    cpsBranch base
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val))
      (base + 8) ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val)) := by
  sorry

-- ============================================================================
-- Phase C spec: cascade dispatch (13 instructions, cpsNBranch with 8 exits)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Phase C spec: cascade dispatch on limb_shift (0-7).
    BEQ x5,x0 for ls0, then 6 × (ADDI x10,x0,k; BEQ x5,x10) for ls1-ls6,
    fall-through to ls7. 13 instructions total. -/
theorem shr_phase_c_spec (v5 v10 : Word) (base : Addr)
    (e0 e1 e2 e3 e4 e5 e6 e7 : Addr)
    (he0 : base + signExtend13 864 = e0)
    (he1 : (base + 8) + signExtend13 668 = e1)
    (he2 : (base + 16) + signExtend13 496 = e2)
    (he3 : (base + 24) + signExtend13 348 = e3)
    (he4 : (base + 32) + signExtend13 224 = e4)
    (he5 : (base + 40) + signExtend13 124 = e5)
    (he6 : (base + 48) + signExtend13 48 = e6)
    (he7 : base + 52 = e7) :
    cpsNBranch base
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      [(e0, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10)),
       (e1, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 1)),
       (e2, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 2)),
       (e3, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 3)),
       (e4, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 4)),
       (e5, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 5)),
       (e6, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 6)),
       (e7, (.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ 6))] := by
  sorry

-- ============================================================================
-- Shift body spec: body_7 (limb_shift=7, 11 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 7: limb_shift=7. Result[0] = value[7] >>> bit_shift, rest = 0.
    Comprises: shr_last_limb 0, 7× SW x12 x0 N, JAL x0 to exit.
    11 instructions from base to exit (via JAL). -/
theorem shr_body_7_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 40) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result0) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ 0) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
  /- proof removed
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
  -/

-- ============================================================================
-- Shift body spec: body_6 (limb_shift=6, 17 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 6: limb_shift=6.
    Result[0] = (value[6] >>> bs) ||| ((value[7] <<< as) &&& mask),
    Result[1] = value[7] >>> bs, rest = 0.
    Comprises: shr_merge_limb(24,28,0), shr_last_limb(4), 6× SW, JAL.
    17 instructions from base to exit (via JAL). -/
theorem shr_body_6_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 64) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result1) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ 0) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
  /- proof removed:
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
  -/

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
theorem shr_body_5_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 88) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result2) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ 0) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
  /- proof removed
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
  -/

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
theorem shr_body_4_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 112) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result3) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ 0) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
  /- proof removed
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
  -/

-- ============================================================================
-- Shift body spec: body_3 (limb_shift=3, 35 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 3: limb_shift=3.
    Result[0..3] = merge results, Result[4] = v7 >>> bs, rest = 0.
    Comprises: merge_limb(12,16,0), merge_limb(16,20,4), merge_limb(20,24,8),
    merge_limb(24,28,12), last_limb(16), 3× SW, JAL. 35 instructions. -/
theorem shr_body_3_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 136) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result4) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ 0) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry

-- ============================================================================
-- (body_3 proof removed during code→assertion refactoring)
-- ============================================================================
-- ============================================================================
-- Shift body spec: body_2 (limb_shift=2, 41 instructions)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Shift body 2: limb_shift=2.
    Result[0..4] = merge results, Result[5] = v7 >>> bs, rest = 0.
    Comprises: 5× merge_limb, last_limb(20), 2× SW, JAL. 41 instructions. -/
theorem shr_body_2_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 160) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ 0) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
set_option maxHeartbeats 3200000 in
/-- Shift body 1: limb_shift=1.
    Result[0..5] = merge results, Result[6] = v7 >>> bs, Result[7] = 0.
    Comprises: 6× merge_limb, last_limb(24), 1× SW, JAL. 47 instructions. -/
theorem shr_body_1_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
    (hexit : (base + 184) + signExtend21 jal_off = exit)
    (hvalid : ValidMemRange sp 8) :
    let result0 := (v1 >>> (bit_shift.toNat % 32)) ||| ((v2 <<< (anti_shift.toNat % 32)) &&& mask)
    let result1 := (v2 >>> (bit_shift.toNat % 32)) ||| ((v3 <<< (anti_shift.toNat % 32)) &&& mask)
    let result2 := (v3 >>> (bit_shift.toNat % 32)) ||| ((v4 <<< (anti_shift.toNat % 32)) &&& mask)
    let result3 := (v4 >>> (bit_shift.toNat % 32)) ||| ((v5v <<< (anti_shift.toNat % 32)) &&& mask)
    let result4 := (v5v >>> (bit_shift.toNat % 32)) ||| ((v6 <<< (anti_shift.toNat % 32)) &&& mask)
    let result5 := (v6 >>> (bit_shift.toNat % 32)) ||| ((v7 <<< (anti_shift.toNat % 32)) &&& mask)
    let result6 := v7 >>> (bit_shift.toNat % 32)
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result6) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ 0)) := by
  sorry
set_option maxHeartbeats 6400000 in
/-- Shift body 0: limb_shift=0. All merge limbs are in-place (src_off = dst_off).
    Result[i] = (v[i] >>> bs) ||| ((v[i+1] <<< as) &&& mask), Result[7] = v7 >>> bs.
    Comprises: 7× merge_limb_inplace, last_limb_inplace, JAL. 53 instructions. -/
theorem shr_body_0_spec (sp : Word)
    (v5 v10 bit_shift anti_shift mask : Word)
    (v0 v1 v2 v3 v4 v5v v6 v7 : Word)
    (base exit : Addr) (jal_off : BitVec 21)
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
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ v0) ** ((sp + 4) ↦ₘ v1) ** ((sp + 8) ↦ₘ v2) ** ((sp + 12) ↦ₘ v3) **
       ((sp + 16) ↦ₘ v4) ** ((sp + 20) ↦ₘ v5v) ** ((sp + 24) ↦ₘ v6) ** ((sp + 28) ↦ₘ v7))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ result7) ** (.x6 ↦ᵣ bit_shift) **
       (.x7 ↦ᵣ anti_shift) ** (.x10 ↦ᵣ ((v7 <<< (anti_shift.toNat % 32)) &&& mask)) ** (.x11 ↦ᵣ mask) **
       (sp ↦ₘ result0) ** ((sp + 4) ↦ₘ result1) ** ((sp + 8) ↦ₘ result2) ** ((sp + 12) ↦ₘ result3) **
       ((sp + 16) ↦ₘ result4) ** ((sp + 20) ↦ₘ result5) ** ((sp + 24) ↦ₘ result6) ** ((sp + 28) ↦ₘ result7)) := by
  sorry
/-- LW x10, off(x12); OR x5, x5, x10:
    Load a word from memory and OR it into x5. 2 instructions. -/
theorem shr_lw_or_acc_spec (sp acc prev_x10 val : Word) (off : BitVec 12)
    (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    cpsTriple base (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ acc) ** (.x10 ↦ᵣ prev_x10) ** ((sp + signExtend12 off) ↦ₘ val))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (acc ||| val)) ** (.x10 ↦ᵣ val) ** ((sp + signExtend12 off) ↦ₘ val)) := by
  sorry
private theorem regIs_to_regOwn (r : Reg) (v : Word) : ∀ h, (r ↦ᵣ v) h → (regOwn r) h :=
  fun _ hp => ⟨v, hp⟩

set_option maxHeartbeats 6400000 in
/-- Phase A spec: Check shift >= 256.
    OR-reduce high limbs (s1|..|s7), BNE to zero_path if nonzero.
    Then load s0, SLTIU, BEQ to zero_path if s0 >= 256.
    17 instructions, cpsBranch with 2 exits:
    - Taken (zero_path): shift >= 256, x5/x10 are regOwn (existential)
    - Not-taken (base+68): shift < 256, x5=s0, x10 is regOwn -/
theorem shr_phase_a_spec (sp r5 r10 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (base zero_path : Addr)
    (hzero : (base + 52) + signExtend13 1120 = zero_path)
    (hzero2 : (base + 64) + signExtend13 1108 = zero_path)
    (hvalid : ValidMemRange sp 8) :
    cpsBranch base
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ r10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
      zero_path
      ((.x12 ↦ᵣ sp) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
      (base + 68)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ s0) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7)) := by
  sorry
/-- Helper: convert memIs to memOwn. -/
private theorem memIs_to_memOwn (a : Addr) (v : Word) : ∀ h, (a ↦ₘ v) h → (memOwn a) h :=
  fun _ hp => ⟨v, hp⟩

/-- Weaken zero path postcondition: convert concrete regs to regOwn, concrete mems to memOwn. -/
private theorem weaken_zp_post (sp : Addr) (r6 r7 r11 : Word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word) : ∀ h,
    ((.x12 ↦ᵣ (sp + 32)) **
     ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 36) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 44) ↦ₘ (0 : Word)) **
     ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 52) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + 60) ↦ₘ (0 : Word)) **
     (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
     (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7)) h →
    ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
     (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
     ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
     (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
     (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) h := by
  intro h hp
  -- Step 1: Permute to move items-to-weaken to the front
  have hp' := (congrFun (show _ =
    ((.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) ** (.x11 ↦ᵣ r11) **
    ((sp + 32) ↦ₘ (0 : Word)) ** ((sp + 36) ↦ₘ (0 : Word)) ** ((sp + 40) ↦ₘ (0 : Word)) ** ((sp + 44) ↦ₘ (0 : Word)) **
    ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 52) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) ** ((sp + 60) ↦ₘ (0 : Word)) **
    (.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (.x0 ↦ᵣ (0 : Word)) ** (regOwn .x10) **
    (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
    ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7))
    from by xperm) h).mp hp
  -- Step 2: Weaken positions 0-10 (left to right)
  have w0 := sepConj_mono_left (regIs_to_regOwn .x6 r6) h hp'
  have w1 := sepConj_mono_right (sepConj_mono_left (regIs_to_regOwn .x7 r7)) h w0
  have w2 := sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (regIs_to_regOwn .x11 r11))) h w1
  have w3 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 32) 0)))) h w2
  have w4 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 36) 0))))) h w3
  have w5 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 40) 0)))))) h w4
  have w6 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 44) 0))))))) h w5
  have w7 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 48) 0)))))))) h w6
  have w8 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 52) 0))))))))) h w7
  have w9 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 56) 0)))))))))) h w8
  have w10 := sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (memIs_to_memOwn (sp + 60) 0))))))))))) h w9
  -- Step 3: Permute to target order
  exact (congrFun (show _ = _ by xperm) h).mp w10

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 2048 in
/-- Full spec for the 256-bit EVM SHR program.
    SHR(shift, value) = value >> shift. 302 instructions.
    Pops shift (sp) and value (sp+32), pushes result (sp+32), advances sp by 32.
    Shift limbs at sp..sp+28 are preserved.
    Result limbs at sp+32..sp+60 are overwritten. -/
theorem evm_shr_spec (sp base : Addr)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Word)
    (r5 r6 r7 r10 r11 : Word)
    (hvS : ValidMemRange sp 8) (hvV : ValidMemRange (sp + 32) 8) :
    let exit := base + 1208
    cpsTriple base exit
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ r5) ** (.x6 ↦ᵣ r6) ** (.x7 ↦ᵣ r7) **
       (.x10 ↦ᵣ r10) ** (.x11 ↦ᵣ r11) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       ((sp + 32) ↦ₘ v0) ** ((sp + 36) ↦ₘ v1) ** ((sp + 40) ↦ₘ v2) ** ((sp + 44) ↦ₘ v3) **
       ((sp + 48) ↦ₘ v4) ** ((sp + 52) ↦ₘ v5) ** ((sp + 56) ↦ₘ v6) ** ((sp + 60) ↦ₘ v7))
      ((.x12 ↦ᵣ (sp + 32)) ** (regOwn .x5) ** (regOwn .x6) ** (regOwn .x7) **
       (regOwn .x10) ** (regOwn .x11) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp ↦ₘ s0) ** ((sp + 4) ↦ₘ s1) ** ((sp + 8) ↦ₘ s2) ** ((sp + 12) ↦ₘ s3) **
       ((sp + 16) ↦ₘ s4) ** ((sp + 20) ↦ₘ s5) ** ((sp + 24) ↦ₘ s6) ** ((sp + 28) ↦ₘ s7) **
       (memOwn (sp + 32)) ** (memOwn (sp + 36)) ** (memOwn (sp + 40)) ** (memOwn (sp + 44)) **
       (memOwn (sp + 48)) ** (memOwn (sp + 52)) ** (memOwn (sp + 56)) ** (memOwn (sp + 60))) := by
  sorry

end EvmAsm
