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
theorem and_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  sorry

/-- Per-limb OR spec (4 instructions). -/
theorem or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  sorry

/-- Per-limb XOR spec (4 instructions). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  sorry

/-- Per-limb NOT spec (3 instructions): LW, XORI with -1, SW.
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hvalid : isValidMemAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    cpsTriple base (base + 12)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  sorry

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

private theorem bw_limb0 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb1 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ b1))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 4) ↦ₘ a1) ** ((sp + 36) ↦ₘ op a1 b1))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb2 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ b2))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 8) ↦ₘ a2) ** ((sp + 40) ↦ₘ op a2 b2))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb3 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 12) ↦ₘ a3) ** ((sp + 44) ↦ₘ op a3 b3))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb4 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ b4))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a4 b4) ** (.x6 ↦ᵣ b4) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 48) ↦ₘ op a4 b4))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb5 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ b5))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a5 b5) ** (.x6 ↦ᵣ b5) **
       ((sp + 20) ↦ₘ a5) ** ((sp + 52) ↦ₘ op a5 b5))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb6 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ b6))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a6 b6) ** (.x6 ↦ᵣ b6) **
       ((sp + 24) ↦ₘ a6) ** ((sp + 56) ↦ₘ op a6 b6))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

private theorem bw_limb7 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (L : cpsTriple base_k (base_k + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a7 b7) ** (.x6 ↦ᵣ b7) **
       ((sp + 28) ↦ₘ a7) ** ((sp + 60) ↦ₘ op a7 b7))) :
    cpsTriple base_k (base_k + 16)
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
  sorry

-- ============================================================================
-- ADDI canonicalizer: changes x12 from sp to sp+32, no sep_perm needed
-- ============================================================================

private theorem bw_addi (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word) :
    cpsTriple (base + 128) (base + 132)
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
  sorry

-- ============================================================================
-- Full binary bitwise spec: composes 8 limb canonicalizers + ADDI.
-- Zero sep_perm calls — all permutation work is in the individual canonicalizers.
-- Uses ValidMemRange for clean validity hypotheses.
-- ============================================================================

theorem binary_bitwise_spec (sp base : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 v7 v6 : Word)
    (limb_spec : ∀ (off_a off_b : BitVec 12)
      (a_limb b_limb v7_in v6_in : Word) (base' : Addr)
      (_ : isValidMemAccess (sp + signExtend12 off_a) = true)
      (_ : isValidMemAccess (sp + signExtend12 off_b) = true),
      cpsTriple base' (base' + 16)
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7_in) ** (.x6 ↦ᵣ v6_in) **
         ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ b_limb))
        ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a_limb b_limb) ** (.x6 ↦ᵣ b_limb) **
         ((sp + signExtend12 off_a) ↦ₘ a_limb) ** ((sp + signExtend12 off_b) ↦ₘ op a_limb b_limb)))
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 132)
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
  sorry

end EvmAsm
