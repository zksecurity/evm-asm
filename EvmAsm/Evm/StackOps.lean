/-
  EvmAsm.Evm.StackOps

  Verified 256-bit EVM stack manipulation opcodes:
  - POP (Phase 2.1): discard top of stack, sp += 32. 1 instruction.
  - PUSH0 (Phase 2.2): push 0 onto stack, sp -= 32. 9 instructions.
  - DUP1 (Phase 2.3): duplicate top of stack, sp -= 32. 17 instructions.
  - SWAP1 (Phase 2.4): swap top two stack items, sp unchanged. 32 instructions.
-/

import EvmAsm.Evm.Stack
import EvmAsm.SyscallSpecs
import EvmAsm.Tactics.XSimp

open EvmAsm.Tactics

namespace EvmAsm

local macro "bv_addr" : tactic =>
  `(tactic| bv_omega)

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  native_decide

@[simp] theorem EvmWord.getLimb_zero (i : Fin 8) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 8, (0 : EvmWord).getLimb j = 0 := by native_decide
  exact h i

-- ============================================================================
-- Program definitions
-- ============================================================================

def evm_pop : Program := ADDI .x12 .x12 32

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SW .x12 .x0 0 ;; SW .x12 .x0 4 ;; SW .x12 .x0 8 ;; SW .x12 .x0 12 ;;
  SW .x12 .x0 16 ;; SW .x12 .x0 20 ;; SW .x12 .x0 24 ;; SW .x12 .x0 28

def evm_dup1 : Program :=
  ADDI .x12 .x12 (-32) ;;
  LW .x7 .x12 32 ;; SW .x12 .x7 0 ;;
  LW .x7 .x12 36 ;; SW .x12 .x7 4 ;;
  LW .x7 .x12 40 ;; SW .x12 .x7 8 ;;
  LW .x7 .x12 44 ;; SW .x12 .x7 12 ;;
  LW .x7 .x12 48 ;; SW .x12 .x7 16 ;;
  LW .x7 .x12 52 ;; SW .x12 .x7 20 ;;
  LW .x7 .x12 56 ;; SW .x12 .x7 24 ;;
  LW .x7 .x12 60 ;; SW .x12 .x7 28

def evm_swap1 : Program :=
  LW .x7 .x12 0  ;; LW .x6 .x12 32 ;; SW .x12 .x6 0  ;; SW .x12 .x7 32 ;;
  LW .x7 .x12 4  ;; LW .x6 .x12 36 ;; SW .x12 .x6 4  ;; SW .x12 .x7 36 ;;
  LW .x7 .x12 8  ;; LW .x6 .x12 40 ;; SW .x12 .x6 8  ;; SW .x12 .x7 40 ;;
  LW .x7 .x12 12 ;; LW .x6 .x12 44 ;; SW .x12 .x6 12 ;; SW .x12 .x7 44 ;;
  LW .x7 .x12 16 ;; LW .x6 .x12 48 ;; SW .x12 .x6 16 ;; SW .x12 .x7 48 ;;
  LW .x7 .x12 20 ;; LW .x6 .x12 52 ;; SW .x12 .x6 20 ;; SW .x12 .x7 52 ;;
  LW .x7 .x12 24 ;; LW .x6 .x12 56 ;; SW .x12 .x6 24 ;; SW .x12 .x7 56 ;;
  LW .x7 .x12 28 ;; LW .x6 .x12 60 ;; SW .x12 .x6 28 ;; SW .x12 .x7 60

-- ============================================================================
-- POP spec (Phase 2.1)
-- ============================================================================

theorem evm_pop_spec (sp base : Addr) :
    cpsTriple base (base + 4) (.x12 ↦ᵣ sp) (.x12 ↦ᵣ (sp + 32)) := by
  sorry

theorem evm_pop_stack_spec (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4)
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) := by
  sorry

-- ============================================================================
-- PUSH0 spec (Phase 2.2)
-- ============================================================================
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple base (base + 36)
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  sorry

theorem evm_push0_stack_spec (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple base (base + 36)
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) := by
  sorry

-- ============================================================================
-- DUP1 per-pair helper (Phase 2.3)
-- ============================================================================

/-- Two-instruction spec for DUP1: LW x7 from source, SW x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 off_dst) = true) :
    cpsTriple base (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  sorry

-- ============================================================================
-- DUP1 spec (Phase 2.3)
-- ============================================================================

theorem evm_dup1_spec (nsp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp 16) :
    cpsTriple base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a7) **
       (nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
       ((nsp + 16) ↦ₘ a4) ** ((nsp + 20) ↦ₘ a5) ** ((nsp + 24) ↦ₘ a6) ** ((nsp + 28) ↦ₘ a7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7)) := by
  sorry

theorem evm_dup1_stack_spec (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (v7 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 16) :
    cpsTriple base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a.getLimb 7) **
       evmWordIs nsp a ** evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest) := by
  sorry

-- ============================================================================
-- SWAP1 per-limb helper (Phase 2.4)
-- ============================================================================

/-- Four-instruction spec for SWAP1: loads a from off_a into x7, b from off_b into x6,
    writes b to off_a, writes a to off_b. Net effect: swaps the two memory cells. -/
theorem swap1_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a b v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    cpsTriple base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ a) ** ((sp + signExtend12 off_b) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) **
       ((sp + signExtend12 off_a) ↦ₘ b) ** ((sp + signExtend12 off_b) ↦ₘ a)) := by
  sorry

-- ============================================================================
-- SWAP1 spec (Phase 2.4)
-- ============================================================================

set_option maxHeartbeats 3200000 in
theorem evm_swap1_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
       ((sp + 16) ↦ₘ b4) ** ((sp + 20) ↦ₘ b5) ** ((sp + 24) ↦ₘ b6) ** ((sp + 28) ↦ₘ b7) **
       ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
       ((sp + 48) ↦ₘ a4) ** ((sp + 52) ↦ₘ a5) ** ((sp + 56) ↦ₘ a6) ** ((sp + 60) ↦ₘ a7)) := by
  sorry

theorem evm_swap1_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b ** evmStackIs (sp + 64) rest)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a.getLimb 7) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp b ** evmWordIs (sp + 32) a ** evmStackIs (sp + 64) rest) := by
  sorry

-- ============================================================================
-- Phase 2.5: Generic DUP (n : Nat) and SWAP (n : Nat)
-- ============================================================================

/-- Sign-extend a small non-negative 12-bit value to 32 bits.
    The MSB is clear when m < 2^11 = 2048, so signExtend = zeroExtend = identity. -/
theorem signExtend12_ofNat_small (m : Nat) (hm : m < 2048) :
    signExtend12 (BitVec.ofNat 12 m) = BitVec.ofNat 32 m := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

-- ============================================================================
-- Generic DUP program definition
-- ============================================================================

/-- One limb pair for DUP: LW x7 from source offset, SW x7 to destination offset. -/
private def dup_one_limb (n i : Nat) : Program :=
  LW .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 4)) ;;
  SW .x12 .x7 (BitVec.ofNat 12 (i * 4))

/-- Generic DUPn program (1-indexed): push copy of nth stack element on top.
    n=1 copies the top, n=2 copies the second element, etc.
    Uses 17 instructions: 1 ADDI + 8 × (LW + SW). -/
def evm_dup (n : Nat) : Program :=
  ADDI .x12 .x12 (-32) ;;
  dup_one_limb n 0 ;; dup_one_limb n 1 ;; dup_one_limb n 2 ;; dup_one_limb n 3 ;;
  dup_one_limb n 4 ;; dup_one_limb n 5 ;; dup_one_limb n 6 ;; dup_one_limb n 7

@[simp] theorem evm_dup_length (n : Nat) : (evm_dup n).length = 17 := by
  simp [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]

private theorem evm_dup_getElem_0 (n : Nat) :
    (show List Instr from evm_dup n)[0]? = some (Instr.ADDI .x12 .x12 (-32)) := by
  simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl

private theorem evm_dup_getElem_lw (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_dup n)[2 * i + 1]? = some (Instr.LW .x7 .x12 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl)

private theorem evm_dup_getElem_sw (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_dup n)[2 * i + 2]? = some (Instr.SW .x12 .x7 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_dup, dup_one_limb, ADDI, LW, SW, single, seq]; rfl)

-- ============================================================================
-- evmStackIs split lemma
-- ============================================================================

/-- Split evmStackIs at position k: extract the kth element (0-indexed). -/
theorem evmStackIs_split_at (sp : Addr) (stack : List EvmWord) (k : Nat)
    (hk : k < stack.length) :
    evmStackIs sp stack =
      (evmStackIs sp (stack.take k) **
       evmWordIs (sp + BitVec.ofNat 32 (k * 32)) (stack[k]'hk) **
       evmStackIs (sp + BitVec.ofNat 32 ((k + 1) * 32)) (stack.drop (k + 1))) := by
  induction k generalizing sp stack with
  | zero =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      simp only [Nat.zero_mul, List.take_zero,
                 List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero,
                 evmStackIs_cons, evmStackIs_nil, sepConj_emp_left', BitVec.add_zero]
      congr 1
  | succ k ih =>
    cases stack with
    | nil => simp at hk
    | cons v vs =>
      have hk' : k < vs.length := by simp at hk; omega
      have a1 : sp + (32 : Addr) + BitVec.ofNat 32 (k * 32) =
                sp + BitVec.ofNat 32 ((k + 1) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have a2 : sp + (32 : Addr) + BitVec.ofNat 32 ((k + 1) * 32) =
                sp + BitVec.ofNat 32 ((k + 2) * 32) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [evmStackIs_cons, ih (sp + 32) vs hk', a1, a2]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ]
      simp only [evmStackIs_cons, sepConj_assoc']

-- ============================================================================
-- Low-level DUP spec (explicit memory cells)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Generic DUPn spec (low level): copies 8 limbs from src (at nsp+n*32) to dst (at nsp).
    Requires 1 ≤ n ≤ 16 (valid EVM DUP range). -/
theorem evm_dup_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    cpsTriple base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp+4) ↦ₘ d1) ** ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
       ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
       ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
       ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
       ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
       ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
       ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ s7) **
       (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
       ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) ** ((nsp+24) ↦ₘ s6) ** ((nsp+28) ↦ₘ s7) **
       ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
       ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
       ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
       ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
       ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
       ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
       ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
       ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7)) := by
  sorry

-- ============================================================================
-- Stack-level DUP spec
-- ============================================================================

/-- DUPn spec at evmWordIs level: copies the nth stack element (0-indexed: element n-1)
    from evmStackIs to a new top position, leaving the rest unchanged. -/
theorem evm_dup_evmword_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (src dst : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    cpsTriple base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp dst **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ src.getLimb 7) **
       evmWordIs nsp src **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src) := by
  sorry

/-- DUPn stack spec: copies the (n-1)-th element (0-indexed) from the stack
    to a new top, leaving the stack unchanged. -/
theorem evm_dup_stack_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n ≤ stack.length)
    (d : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    let vn := stack[n - 1]'(by omega)
    cpsTriple base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp d **
       evmStackIs (nsp + 32) stack)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ vn.getLimb 7) **
       evmWordIs nsp vn **
       evmStackIs (nsp + 32) stack) := by
  sorry

-- ============================================================================
-- Generic SWAP program definition
-- ============================================================================

/-- One limb quad for SWAP: LW x7 from top, LW x6 from nth, SW x6 to top, SW x7 to nth. -/
private def swap_one_limb (n i : Nat) : Program :=
  LW .x7 .x12 (BitVec.ofNat 12 (i * 4)) ;;
  LW .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 4)) ;;
  SW .x12 .x6 (BitVec.ofNat 12 (i * 4)) ;;
  SW .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 4))

/-- Generic SWAPn program (1-indexed): swap the top element with the nth stack element.
    n=1 swaps top with 2nd, n=2 swaps top with 3rd, etc.
    Uses 32 instructions: 8 × (LW + LW + SW + SW). -/
def evm_swap (n : Nat) : Program :=
  swap_one_limb n 0 ;; swap_one_limb n 1 ;; swap_one_limb n 2 ;; swap_one_limb n 3 ;;
  swap_one_limb n 4 ;; swap_one_limb n 5 ;; swap_one_limb n 6 ;; swap_one_limb n 7

@[simp] theorem evm_swap_length (n : Nat) : (evm_swap n).length = 32 := by
  simp [evm_swap, swap_one_limb, LW, SW, single, seq]

private theorem evm_swap_getElem_lw1 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 0]? = some (Instr.LW .x7 .x12 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_lw2 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 1]? = some (Instr.LW .x6 .x12 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_sw1 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 2]? = some (Instr.SW .x12 .x6 (BitVec.ofNat 12 (i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

private theorem evm_swap_getElem_sw2 (n i : Nat) (hi : i < 8) :
    (show List Instr from evm_swap n)[4 * i + 3]? = some (Instr.SW .x12 .x7 (BitVec.ofNat 12 (n * 32 + i * 4))) := by
  have hi8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (simp only [evm_swap, swap_one_limb, LW, SW, single, seq]; rfl)

-- ============================================================================
-- Low-level SWAP spec (explicit memory cells)
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Generic SWAPn spec (low level): swaps 8 limbs at sp (top) with 8 limbs at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    cpsTriple base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp+4) ↦ₘ a1) ** ((sp+8) ↦ₘ a2) ** ((sp+12) ↦ₘ a3) **
       ((sp+16) ↦ₘ a4) ** ((sp+20) ↦ₘ a5) ** ((sp+24) ↦ₘ a6) ** ((sp+28) ↦ₘ a7) **
       ((sp + BitVec.ofNat 32 (n*32))    ↦ₘ b0) **
       ((sp + BitVec.ofNat 32 (n*32+4))  ↦ₘ b1) **
       ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ b2) **
       ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ b3) **
       ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ b4) **
       ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ b5) **
       ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ b6) **
       ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ b7))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ b0) ** ((sp+4) ↦ₘ b1) ** ((sp+8) ↦ₘ b2) ** ((sp+12) ↦ₘ b3) **
       ((sp+16) ↦ₘ b4) ** ((sp+20) ↦ₘ b5) ** ((sp+24) ↦ₘ b6) ** ((sp+28) ↦ₘ b7) **
       ((sp + BitVec.ofNat 32 (n*32))    ↦ₘ a0) **
       ((sp + BitVec.ofNat 32 (n*32+4))  ↦ₘ a1) **
       ((sp + BitVec.ofNat 32 (n*32+8))  ↦ₘ a2) **
       ((sp + BitVec.ofNat 32 (n*32+12)) ↦ₘ a3) **
       ((sp + BitVec.ofNat 32 (n*32+16)) ↦ₘ a4) **
       ((sp + BitVec.ofNat 32 (n*32+20)) ↦ₘ a5) **
       ((sp + BitVec.ofNat 32 (n*32+24)) ↦ₘ a6) **
       ((sp + BitVec.ofNat 32 (n*32+28)) ↦ₘ a7)) := by
  sorry

-- ============================================================================
-- Stack-level SWAP spec
-- ============================================================================

/-- SWAPn spec at evmWordIs level: swaps the top and nth stack elements. -/
theorem evm_swap_evmword_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (top nth : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    cpsTriple base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp top **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) nth)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 7) ** (.x6 ↦ᵣ nth.getLimb 7) **
       evmWordIs sp nth **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) top) := by
  sorry

/-- SWAPn stack spec: swaps top with the nth element (1-indexed) of the stack. -/
theorem evm_swap_stack_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n + 1 ≤ stack.length)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    let top := stack[0]'(by omega)
    let nth := stack[n]'(by omega)
    cpsTriple base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ top.getLimb 7) ** (.x6 ↦ᵣ nth.getLimb 7) **
       evmWordIs sp nth **
       evmStackIs (sp + 32) ((stack.drop 1).take (n - 1)) **
       evmWordIs (sp + BitVec.ofNat 32 (n * 32)) top **
       evmStackIs (sp + BitVec.ofNat 32 ((n + 1) * 32)) ((stack.drop 1).drop n)) := by
  sorry

end EvmAsm
