/-
  EvmAsm.Evm64.Bitwise

  256-bit EVM bitwise operations (AND, OR, XOR, NOT) as RV64 programs.
  Each operates on 4 little-endian 64-bit limbs stored in memory.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

-- ============================================================================
-- Program Definitions
-- ============================================================================

/-- 256-bit EVM AND: binary, pops 2, pushes 1.
    For each of 4 limbs: load A[i] and B[i], AND them, store to B[i].
    Then advance sp by 32. -/
def evm_and : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM OR. -/
def evm_or : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.OR .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM XOR. -/
def evm_xor : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.XOR .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LD .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 24

-- ============================================================================
-- Per-limb Specs: Binary Bitwise
-- ============================================================================

/-- Per-limb AND spec (4 instructions: LD x7, LD x6, AND x7 x7 x6, SD x12 x7).
    Loads A[i] and B[i], computes AND, stores result at B[i]'s location. -/
theorem and_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .AND .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb &&& b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb &&& b_limb))) := by
  runBlock

/-- Per-limb OR spec (4 instructions: LD x7, LD x6, OR x7 x7 x6, SD x12 x7). -/
theorem or_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .OR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ||| b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ||| b_limb))) := by
  runBlock

/-- Per-limb XOR spec (4 instructions: LD x7, LD x6, XOR x7 x7 x6, SD x12 x7). -/
theorem xor_limb_spec (off_a off_b : BitVec 12)
    (sp a_limb b_limb v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ b_limb))
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .XOR .x7 .x7 .x6) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (a_limb ^^^ b_limb)) ** (.x6 ↦ᵣ b_limb) **
       (mem_a ↦ₘ a_limb) ** (mem_b ↦ₘ (a_limb ^^^ b_limb))) := by
  runBlock

/-- Per-limb NOT spec (3 instructions: LD x7, XORI x7 x7 (-1), SD x12 x7).
    Unary: loads limb, complements it, stores back to same location. -/
theorem not_limb_spec (off : BitVec 12)
    (sp limb v7 : Word) (base : Addr)
    (hvalid : isValidDwordAccess (sp + signExtend12 off) = true) :
    let mem := sp + signExtend12 off
    cpsTriple base (base + 12)
      ((base ↦ᵢ .LD .x7 .x12 off) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) **
       ((base + 8) ↦ᵢ .SD .x12 .x7 off) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (mem ↦ₘ limb))
      ((base ↦ᵢ .LD .x7 .x12 off) ** ((base + 4) ↦ᵢ .XORI .x7 .x7 (-1)) **
       ((base + 8) ↦ᵢ .SD .x12 .x7 off) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (limb ^^^ signExtend12 (-1))) ** (mem ↦ₘ (limb ^^^ signExtend12 (-1)))) := by
  runBlock

-- ============================================================================
-- Individual limb canonicalizers (binary ops)
-- Each lifts a 5-conjunct per-limb spec to the full 11-conjunct canonical form.
-- ============================================================================

private theorem bw_limb0 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb1 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 8) ↦ₘ a1) ** ((sp + 40) ↦ₘ b1))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 8) ↦ₘ a1) ** ((sp + 40) ↦ₘ op a1 b1))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ op a1 b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb2 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 48) ↦ₘ b2))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 48) ↦ₘ op a2 b2))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ op a2 b2) ** ((sp + 56) ↦ₘ b3)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

private theorem bw_limb3 (sp base_k : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L : cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + 24) ↦ₘ a3) ** ((sp + 56) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 24) ↦ₘ a3) ** ((sp + 56) ↦ₘ op a3 b3))) :
    cpsTriple base_k (base_k + 16)
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      (F ** (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ op a3 b3)) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (by pcFree) L)

-- ============================================================================
-- ADDI canonicalizer: changes x12 from sp to sp+32
-- ============================================================================

private theorem bw_addi (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree) :
    cpsTriple (base + 64) (base + 68)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have ha : (base + 64 : Addr) + 4 = base + 68 := by bv_omega
  have s_raw := addi_spec_gen_same .x12 sp 32 (base + 64) (by nofun)
  rw [ha] at s_raw
  simp only [signExtend12_32] at s_raw
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ _ (pcFree_sepConj hF (by pcFree)) s_raw)

-- ============================================================================
-- Address recasting helper
-- ============================================================================

private theorem cpsTriple_addr_eq {P Q : Assertion}
    {s1 s2 e1 e2 : Addr} (hs : s1 = s2) (he : e1 = e2)
    (h : cpsTriple s1 e1 P Q) :
    cpsTriple s2 e2 P Q := by
  subst hs; subst he; exact h

-- ============================================================================
-- Full binary bitwise spec: composes 4 limb canonicalizers + ADDI.
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem binary_bitwise_spec (sp base : Addr)
    (op : Word → Word → Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (F : Assertion) (hF : F.pcFree)
    (L0 : cpsTriple base (base + 16)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ b0))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       (sp ↦ₘ a0) ** ((sp + 32) ↦ₘ op a0 b0)))
    (L1 : cpsTriple (base + 16) (base + 32)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a0 b0) ** (.x6 ↦ᵣ b0) **
       ((sp + 8) ↦ₘ a1) ** ((sp + 40) ↦ₘ b1))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 8) ↦ₘ a1) ** ((sp + 40) ↦ₘ op a1 b1)))
    (L2 : cpsTriple (base + 32) (base + 48)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a1 b1) ** (.x6 ↦ᵣ b1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 48) ↦ₘ b2))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 48) ↦ₘ op a2 b2)))
    (L3 : cpsTriple (base + 48) (base + 64)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a2 b2) ** (.x6 ↦ᵣ b2) **
       ((sp + 24) ↦ₘ a3) ** ((sp + 56) ↦ₘ b3))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       ((sp + 24) ↦ₘ a3) ** ((sp + 56) ↦ₘ op a3 b3)))
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 68)
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)) **
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ op a3 b3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ op a0 b0) ** ((sp + 40) ↦ₘ op a1 b1) ** ((sp + 48) ↦ₘ op a2 b2) ** ((sp + 56) ↦ₘ op a3 b3)) := by
  let G := F ** ((base + 64) ↦ᵢ .ADDI .x12 .x12 32)
  have hG : G.pcFree := pcFree_sepConj hF (by pcFree)
  -- Convert exit addresses to (base_k + 16) form
  have L1' := cpsTriple_addr_eq (rfl : (base + 16 : Addr) = base + 16)
    (by bv_omega : (base + 32 : Addr) = (base + 16) + 16) L1
  have L2' := cpsTriple_addr_eq (rfl : (base + 32 : Addr) = base + 32)
    (by bv_omega : (base + 48 : Addr) = (base + 32) + 16) L2
  have L3' := cpsTriple_addr_eq (rfl : (base + 48 : Addr) = base + 48)
    (by bv_omega : (base + 64 : Addr) = (base + 48) + 16) L3
  clear L1 L2 L3
  -- Expand each limb to full 8-mem level
  have S0 := bw_limb0 sp base op a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 G hG L0
  have S1 := bw_limb1 sp (base + 16) op a0 a1 a2 a3
    (op a0 b0) b1 b2 b3 (op a0 b0) b0 G hG L1'
  have S01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0 S1
  clear S0 S1 L0 L1'
  have S01' := cpsTriple_addr_eq rfl (by bv_omega : ((base + 16 : Addr) + 16) = base + 32) S01
  clear S01
  have S2 := bw_limb2 sp (base + 32) op a0 a1 a2 a3
    (op a0 b0) (op a1 b1) b2 b3 (op a1 b1) b1 G hG L2'
  have S012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S01' S2
  clear S01' S2 L2'
  have S012' := cpsTriple_addr_eq rfl (by bv_omega : ((base + 32 : Addr) + 16) = base + 48) S012
  clear S012
  have S3 := bw_limb3 sp (base + 48) op a0 a1 a2 a3
    (op a0 b0) (op a1 b1) (op a2 b2) b3 (op a2 b2) b2 G hG L3'
  have S0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S012' S3
  clear S012' S3 L3'
  have S0123' := cpsTriple_addr_eq rfl (by bv_omega : ((base + 48 : Addr) + 16) = base + 64) S0123
  clear S0123
  -- ADDI step
  have Saddi := bw_addi sp base a0 a1 a2 a3
    (op a0 b0) (op a1 b1) (op a2 b2) (op a3 b3)
    (op a3 b3) b3 F hF
  exact cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) S0123' Saddi

end EvmAsm.Rv64
