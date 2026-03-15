/-
  EvmAsm.Evm32.StackOps

  Verified 256-bit EVM stack manipulation opcodes:
  - POP (Phase 2.1): discard top of stack, sp += 32. 1 instruction.
  - PUSH0 (Phase 2.2): push 0 onto stack, sp -= 32. 9 instructions.
  - DUP1 (Phase 2.3): duplicate top of stack, sp -= 32. 17 instructions.
  - SWAP1 (Phase 2.4): swap top two stack items, sp unchanged. 32 instructions.
-/

import EvmAsm.Evm32.Stack
import EvmAsm.Rv32.SyscallSpecs
import EvmAsm.Rv32.Tactics.XSimp
import EvmAsm.Rv32.Tactics.RunBlock
import EvmAsm.Rv32.Tactics.LiftSpec

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
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.ADDI .x12 .x12 32))
      (.x12 ↦ᵣ sp)
      (.x12 ↦ᵣ (sp + 32)) := by
  have h := addi_spec_gen_same .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h; exact h

theorem evm_pop_stack_spec (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4)
      (CodeReq.singleton base (.ADDI .x12 .x12 32))
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) := by
  sorry

-- ============================================================================
-- PUSH0 spec (Phase 2.2)
-- ============================================================================
abbrev evm_push0_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.SW .x12 .x0 0))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x0 4))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SW .x12 .x0 8))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x0 12))
  (CodeReq.union (CodeReq.singleton (base + 20) (.SW .x12 .x0 16))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x0 20))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SW .x12 .x0 24))
   (CodeReq.singleton (base + 32) (.SW .x12 .x0 28)))))))))

set_option maxHeartbeats 4800000 in
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    let code := evm_push0_code base
    cpsTriple base (base + 36) code
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
    let code := evm_push0_code base
    cpsTriple base (base + 36) code
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) := by
  sorry

-- ============================================================================
-- DUP1 per-pair helper (Phase 2.3)
-- ============================================================================

abbrev copy_limb_code (base : Addr) (off_src off_dst : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off_src))
   (CodeReq.singleton (base + 4) (.SW .x12 .x7 off_dst))

/-- Two-instruction spec for DUP1: LW x7 from source, SW x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidMemAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 off_dst) = true) :
    let code := copy_limb_code base off_src off_dst
    cpsTriple base (base + 8) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  sorry

-- ============================================================================
-- DUP1 spec (Phase 2.3)
-- ============================================================================

abbrev evm_dup1_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x7 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x7 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.LW .x7 .x12 36))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x7 4))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LW .x7 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x7 8))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LW .x7 .x12 44))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SW .x12 .x7 12))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LW .x7 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SW .x12 .x7 16))
  (CodeReq.union (CodeReq.singleton (base + 44) (.LW .x7 .x12 52))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SW .x12 .x7 20))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LW .x7 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SW .x12 .x7 24))
  (CodeReq.union (CodeReq.singleton (base + 60) (.LW .x7 .x12 60))
   (CodeReq.singleton (base + 64) (.SW .x12 .x7 28)))))))))))))))))

set_option maxHeartbeats 6400000 in
theorem evm_dup1_spec (nsp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp 16) :
    let code := evm_dup1_code base
    cpsTriple base (base + 68) code
      -- Registers + memory
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
      -- Registers + memory (copied)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a7) **
       (nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
       ((nsp + 16) ↦ₘ a4) ** ((nsp + 20) ↦ₘ a5) ** ((nsp + 24) ↦ₘ a6) ** ((nsp + 28) ↦ₘ a7) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
       ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7)) := by
  sorry

theorem evm_dup1_stack_spec (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (v7 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 16) :
    let code := evm_dup1_code base
    cpsTriple base (base + 68) code
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

abbrev swap1_limb_code (base : Addr) (off_a off_b : BitVec 12) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 off_a))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 off_b))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x6 off_a))
   (CodeReq.singleton (base + 12) (.SW .x12 .x7 off_b))))

/-- Four-instruction spec for SWAP1: loads a from off_a into x7, b from off_b into x6,
    writes b to off_a, writes a to off_b. Net effect: swaps the two memory cells. -/
theorem swap1_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a b v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    let mem_a := sp + signExtend12 off_a
    let mem_b := sp + signExtend12 off_b
    let code := swap1_limb_code base off_a off_b
    cpsTriple base (base + 16) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (mem_a ↦ₘ a) ** (mem_b ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) **
       (mem_a ↦ₘ b) ** (mem_b ↦ₘ a)) := by
  sorry

-- ============================================================================
-- SWAP1 spec (Phase 2.4)
-- ============================================================================

abbrev evm_swap1_code (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 0))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 32))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x6 0))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SW .x12 .x7 32))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LW .x7 .x12 4))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LW .x6 .x12 36))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x6 4))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SW .x12 .x7 36))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LW .x7 .x12 8))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LW .x6 .x12 40))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SW .x12 .x6 8))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SW .x12 .x7 40))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LW .x7 .x12 12))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LW .x6 .x12 44))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SW .x12 .x6 12))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SW .x12 .x7 44))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LW .x7 .x12 16))
  (CodeReq.union (CodeReq.singleton (base + 68) (.LW .x6 .x12 48))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SW .x12 .x6 16))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SW .x12 .x7 48))
  (CodeReq.union (CodeReq.singleton (base + 80) (.LW .x7 .x12 20))
  (CodeReq.union (CodeReq.singleton (base + 84) (.LW .x6 .x12 52))
  (CodeReq.union (CodeReq.singleton (base + 88) (.SW .x12 .x6 20))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SW .x12 .x7 52))
  (CodeReq.union (CodeReq.singleton (base + 96) (.LW .x7 .x12 24))
  (CodeReq.union (CodeReq.singleton (base + 100) (.LW .x6 .x12 56))
  (CodeReq.union (CodeReq.singleton (base + 104) (.SW .x12 .x6 24))
  (CodeReq.union (CodeReq.singleton (base + 108) (.SW .x12 .x7 56))
  (CodeReq.union (CodeReq.singleton (base + 112) (.LW .x7 .x12 28))
  (CodeReq.union (CodeReq.singleton (base + 116) (.LW .x6 .x12 60))
  (CodeReq.union (CodeReq.singleton (base + 120) (.SW .x12 .x6 28))
   (CodeReq.singleton (base + 124) (.SW .x12 .x7 60))))))))))))))))))))))))))))))))

set_option maxHeartbeats 6400000 in
theorem evm_swap1_spec (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp 16) :
    let code := evm_swap1_code base
    cpsTriple base (base + 128) code
      -- Registers + memory
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
       ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
       ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
      -- Registers + memory (swapped)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a7) ** (.x6 ↦ᵣ b7) **
       (sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
       ((sp + 16) ↦ₘ b4) ** ((sp + 20) ↦ₘ b5) ** ((sp + 24) ↦ₘ b6) ** ((sp + 28) ↦ₘ b7) **
       ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
       ((sp + 48) ↦ₘ a4) ** ((sp + 52) ↦ₘ a5) ** ((sp + 56) ↦ₘ a6) ** ((sp + 60) ↦ₘ a7)) := by
  sorry

set_option maxHeartbeats 3200000 in
theorem evm_swap1_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange sp 16) :
    let code := evm_swap1_code base
    cpsTriple base (base + 128) code
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

/-- Code requirement for generic DUPn: ADDI + 8 LW/SW pairs. -/
abbrev evm_dup_code (n : Nat) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.ADDI .x12 .x12 (-32)))
  (CodeReq.union (CodeReq.singleton (base + 4)  (.LW .x7 .x12 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 8)  (.SW .x12 .x7 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+4))))
  (CodeReq.union (CodeReq.singleton (base + 16) (.SW .x12 .x7 (BitVec.ofNat 12 4)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x7 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+12))))
  (CodeReq.union (CodeReq.singleton (base + 32) (.SW .x12 .x7 (BitVec.ofNat 12 12)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SW .x12 .x7 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+20))))
  (CodeReq.union (CodeReq.singleton (base + 48) (.SW .x12 .x7 (BitVec.ofNat 12 20)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+24))))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SW .x12 .x7 (BitVec.ofNat 12 24)))
  (CodeReq.union (CodeReq.singleton (base + 60) (.LW .x7 .x12 (BitVec.ofNat 12 (n*32+28))))
   (CodeReq.singleton (base + 64) (.SW .x12 .x7 (BitVec.ofNat 12 28))))))))))))))))))

set_option maxHeartbeats 6400000 in
/-- Generic DUPn spec (low level): copies 8 limbs from src (at nsp+n*32) to dst (at nsp).
    Requires 1 ≤ n ≤ 16 (valid EVM DUP range). -/
theorem evm_dup_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    let code := evm_dup_code n base
    cpsTriple base (base + 68) code
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
/-  -- ADDI result normalization
  have h_addi : (nsp + 32 : Word) + signExtend12 (-32 : BitVec 12) = nsp := by
    simp only [signExtend12_neg32]; bv_omega
  -- signExtend12 for source offsets (generic via signExtend12_ofNat_small)
  have hse_s0 : signExtend12 (BitVec.ofNat 12 (n*32)) = BitVec.ofNat 32 (n*32) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s1 : signExtend12 (BitVec.ofNat 12 (n*32+4)) = BitVec.ofNat 32 (n*32+4) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s2 : signExtend12 (BitVec.ofNat 12 (n*32+8)) = BitVec.ofNat 32 (n*32+8) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s3 : signExtend12 (BitVec.ofNat 12 (n*32+12)) = BitVec.ofNat 32 (n*32+12) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s4 : signExtend12 (BitVec.ofNat 12 (n*32+16)) = BitVec.ofNat 32 (n*32+16) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s5 : signExtend12 (BitVec.ofNat 12 (n*32+20)) = BitVec.ofNat 32 (n*32+20) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s6 : signExtend12 (BitVec.ofNat 12 (n*32+24)) = BitVec.ofNat 32 (n*32+24) :=
    signExtend12_ofNat_small _ (by omega)
  have hse_s7 : signExtend12 (BitVec.ofNat 12 (n*32+28)) = BitVec.ofNat 32 (n*32+28) :=
    signExtend12_ofNat_small _ (by omega)
  -- Memory address normalization for dst offsets (use signExtend12_ofNat_small)
  have hse_d0  : signExtend12 (BitVec.ofNat 12 0)  = BitVec.ofNat 32 0  := signExtend12_ofNat_small _ (by omega)
  have hse_d4  : signExtend12 (BitVec.ofNat 12 4)  = BitVec.ofNat 32 4  := signExtend12_ofNat_small _ (by omega)
  have hse_d8  : signExtend12 (BitVec.ofNat 12 8)  = BitVec.ofNat 32 8  := signExtend12_ofNat_small _ (by omega)
  have hse_d12 : signExtend12 (BitVec.ofNat 12 12) = BitVec.ofNat 32 12 := signExtend12_ofNat_small _ (by omega)
  have hse_d16 : signExtend12 (BitVec.ofNat 12 16) = BitVec.ofNat 32 16 := signExtend12_ofNat_small _ (by omega)
  have hse_d20 : signExtend12 (BitVec.ofNat 12 20) = BitVec.ofNat 32 20 := signExtend12_ofNat_small _ (by omega)
  have hse_d24 : signExtend12 (BitVec.ofNat 12 24) = BitVec.ofNat 32 24 := signExtend12_ofNat_small _ (by omega)
  have hse_d28 : signExtend12 (BitVec.ofNat 12 28) = BitVec.ofNat 32 28 := signExtend12_ofNat_small _ (by omega)
  have hm0 : nsp + signExtend12 (BitVec.ofNat 12 0) = nsp := by rw [hse_d0]; bv_omega
  have hm4 : nsp + signExtend12 (BitVec.ofNat 12 4) = nsp + 4 := by rw [hse_d4]; bv_omega
  have hm8 : nsp + signExtend12 (BitVec.ofNat 12 8) = nsp + 8 := by rw [hse_d8]; bv_omega
  have hm12 : nsp + signExtend12 (BitVec.ofNat 12 12) = nsp + 12 := by rw [hse_d12]; bv_omega
  have hm16 : nsp + signExtend12 (BitVec.ofNat 12 16) = nsp + 16 := by rw [hse_d16]; bv_omega
  have hm20 : nsp + signExtend12 (BitVec.ofNat 12 20) = nsp + 20 := by rw [hse_d20]; bv_omega
  have hm24 : nsp + signExtend12 (BitVec.ofNat 12 24) = nsp + 24 := by rw [hse_d24]; bv_omega
  have hm28 : nsp + signExtend12 (BitVec.ofNat 12 28) = nsp + 28 := by rw [hse_d28]; bv_omega
  -- Memory validity from ValidMemRange for dst locations (indices 0..7)
  have hv0 : isValidMemAccess nsp = true := by
    have := hvalid.get (i := 0) (by omega); simpa using this
  have hv4 : isValidMemAccess (nsp + 4) = true := by
    have := hvalid.get (i := 1) (by omega); simpa using this
  have hv8 : isValidMemAccess (nsp + 8) = true := by
    have := hvalid.get (i := 2) (by omega); simpa using this
  have hv12 : isValidMemAccess (nsp + 12) = true := by
    have := hvalid.get (i := 3) (by omega); simpa using this
  have hv16 : isValidMemAccess (nsp + 16) = true := by
    have := hvalid.get (i := 4) (by omega); simpa using this
  have hv20 : isValidMemAccess (nsp + 20) = true := by
    have := hvalid.get (i := 5) (by omega); simpa using this
  have hv24 : isValidMemAccess (nsp + 24) = true := by
    have := hvalid.get (i := 6) (by omega); simpa using this
  have hv28 : isValidMemAccess (nsp + 28) = true := by
    have := hvalid.get (i := 7) (by omega); simpa using this
  -- Memory validity from ValidMemRange for src locations (indices n*8..n*8+7)
  have hvs0 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32)) = true := by
    have := hvalid.get (i := n*8) (by omega)
    rwa [show 4 * (n * 8) = n * 32 from by omega] at this
  have hvs4 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+4)) = true := by
    have := hvalid.get (i := n*8+1) (by omega)
    rwa [show 4 * (n * 8 + 1) = n * 32 + 4 from by omega] at this
  have hvs8 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+8)) = true := by
    have := hvalid.get (i := n*8+2) (by omega)
    rwa [show 4 * (n * 8 + 2) = n * 32 + 8 from by omega] at this
  have hvs12 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+12)) = true := by
    have := hvalid.get (i := n*8+3) (by omega)
    rwa [show 4 * (n * 8 + 3) = n * 32 + 12 from by omega] at this
  have hvs16 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+16)) = true := by
    have := hvalid.get (i := n*8+4) (by omega)
    rwa [show 4 * (n * 8 + 4) = n * 32 + 16 from by omega] at this
  have hvs20 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+20)) = true := by
    have := hvalid.get (i := n*8+5) (by omega)
    rwa [show 4 * (n * 8 + 5) = n * 32 + 20 from by omega] at this
  have hvs24 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+24)) = true := by
    have := hvalid.get (i := n*8+6) (by omega)
    rwa [show 4 * (n * 8 + 6) = n * 32 + 24 from by omega] at this
  have hvs28 : isValidMemAccess (nsp + BitVec.ofNat 32 (n*32+28)) = true := by
    have := hvalid.get (i := n*8+7) (by omega)
    rwa [show 4 * (n * 8 + 7) = n * 32 + 28 from by omega] at this
  -- Step 1: ADDI x12 x12 (-32) at base
  have sA_raw := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  rw [h_addi] at sA_raw
  have sA := cpsTriple_frame_left _ _ _ _
    (((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (.x7 ↦ᵣ v7) **
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
    (by pcFree) sA_raw
  clear sA_raw
  -- Step 2: Pair 0 - LW from nsp + n*32, SW to nsp
  have P0_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32)) (BitVec.ofNat 12 0) s0 d0 v7 (base + 4)
    (by rw [hse_s0]; exact hvs0) (by rw [hm0]; exact hv0)
  rw [hse_s0, signExtend12_ofNat_small 0 (by omega)] at P0_raw
  rw [show nsp + BitVec.ofNat 32 0 = nsp from by bv_omega] at P0_raw
  simp only [copy_limb_code] at P0_raw
  rw [show (base + 4 : Addr) + 4 = base + 8 from by bv_addr,
      show (base + 4 : Addr) + 8 = base + 12 from by bv_addr] at P0_raw
  have P0 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     ((nsp+4) ↦ₘ d1) ** ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P0_raw
  clear P0_raw
  have sAP0 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sA P0
  clear sA P0
  -- Step 3: Pair 1 - LW from nsp + n*32+4, SW to nsp+4
  have P1_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+4)) (BitVec.ofNat 12 4) s1 d1 s0 (base + 12)
    (by rw [hse_s1]; exact hvs4) (by rw [hm4]; exact hv4)
  rw [hse_s1, signExtend12_ofNat_small 4 (by omega)] at P1_raw
  simp only [copy_limb_code] at P1_raw
  rw [show (base + 12 : Addr) + 4 = base + 16 from by bv_addr,
      show (base + 12 : Addr) + 8 = base + 20 from by bv_addr] at P1_raw
  have P1 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) **
     ((nsp+8) ↦ₘ d2) ** ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P1_raw
  clear P1_raw
  have sAP01 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP0 P1
  clear sAP0 P1
  -- Step 4: Pair 2 - LW from nsp + n*32+8, SW to nsp+8
  have P2_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+8)) (BitVec.ofNat 12 8) s2 d2 s1 (base + 20)
    (by rw [hse_s2]; exact hvs8) (by rw [hm8]; exact hv8)
  rw [hse_s2, signExtend12_ofNat_small 8 (by omega)] at P2_raw
  simp only [copy_limb_code] at P2_raw
  rw [show (base + 20 : Addr) + 4 = base + 24 from by bv_addr,
      show (base + 20 : Addr) + 8 = base + 28 from by bv_addr] at P2_raw
  have P2 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) **
     ((nsp+12) ↦ₘ d3) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P2_raw
  clear P2_raw
  have sAP012 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP01 P2
  clear sAP01 P2
  -- Step 5: Pair 3 - LW from nsp + n*32+12, SW to nsp+12
  have P3_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+12)) (BitVec.ofNat 12 12) s3 d3 s2 (base + 28)
    (by rw [hse_s3]; exact hvs12) (by rw [hm12]; exact hv12)
  rw [hse_s3, signExtend12_ofNat_small 12 (by omega)] at P3_raw
  simp only [copy_limb_code] at P3_raw
  rw [show (base + 28 : Addr) + 4 = base + 32 from by bv_addr,
      show (base + 28 : Addr) + 8 = base + 36 from by bv_addr] at P3_raw
  have P3 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) **
     ((nsp+16) ↦ₘ d4) ** ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P3_raw
  clear P3_raw
  have sAP0123 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP012 P3
  clear sAP012 P3
  -- Step 6: Pair 4 - LW from nsp + n*32+16, SW to nsp+16
  have P4_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+16)) (BitVec.ofNat 12 16) s4 d4 s3 (base + 36)
    (by rw [hse_s4]; exact hvs16) (by rw [hm16]; exact hv16)
  rw [hse_s4, signExtend12_ofNat_small 16 (by omega)] at P4_raw
  simp only [copy_limb_code] at P4_raw
  rw [show (base + 36 : Addr) + 4 = base + 40 from by bv_addr,
      show (base + 36 : Addr) + 8 = base + 44 from by bv_addr] at P4_raw
  have P4 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+20) ↦ₘ d5) ** ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P4_raw
  clear P4_raw
  have sAP01234 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP0123 P4
  clear sAP0123 P4
  -- Step 7: Pair 5 - LW from nsp + n*32+20, SW to nsp+20
  have P5_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+20)) (BitVec.ofNat 12 20) s5 d5 s4 (base + 44)
    (by rw [hse_s5]; exact hvs20) (by rw [hm20]; exact hv20)
  rw [hse_s5, signExtend12_ofNat_small 20 (by omega)] at P5_raw
  simp only [copy_limb_code] at P5_raw
  rw [show (base + 44 : Addr) + 4 = base + 48 from by bv_addr,
      show (base + 44 : Addr) + 8 = base + 52 from by bv_addr] at P5_raw
  have P5 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) **
     ((nsp+24) ↦ₘ d6) ** ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P5_raw
  clear P5_raw
  have sAP012345 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP01234 P5
  clear sAP01234 P5
  -- Step 8: Pair 6 - LW from nsp + n*32+24, SW to nsp+24
  have P6_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+24)) (BitVec.ofNat 12 24) s6 d6 s5 (base + 52)
    (by rw [hse_s6]; exact hvs24) (by rw [hm24]; exact hv24)
  rw [hse_s6, signExtend12_ofNat_small 24 (by omega)] at P6_raw
  simp only [copy_limb_code] at P6_raw
  rw [show (base + 52 : Addr) + 4 = base + 56 from by bv_addr,
      show (base + 52 : Addr) + 8 = base + 60 from by bv_addr] at P6_raw
  have P6 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 60) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+28)))  **
     ((base + 64) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 28))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) **
     ((nsp+28) ↦ₘ d7) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+28)) ↦ₘ s7))
    (by pcFree) P6_raw
  clear P6_raw
  have sAP0123456 := cpsTriple_seq_with_perm _ _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) sAP012345 P6
  clear sAP012345 P6
  -- Step 9: Pair 7 - LW from nsp + n*32+28, SW to nsp+28
  have P7_raw := dup1_pair_spec nsp
    (BitVec.ofNat 12 (n*32+28)) (BitVec.ofNat 12 28) s7 d7 s6 (base + 60)
    (by rw [hse_s7]; exact hvs28) (by rw [hm28]; exact hv28)
  rw [hse_s7, signExtend12_ofNat_small 28 (by omega)] at P7_raw
  simp only [copy_limb_code] at P7_raw
  rw [show (base + 60 : Addr) + 4 = base + 64 from by bv_addr,
      show (base + 60 : Addr) + 8 = base + 68 from by bv_addr] at P7_raw
  have P7 := cpsTriple_frame_left _ _ _ _
    ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
     ((base + 4)  ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32)))     **
     ((base + 8)  ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 0))          **
     ((base + 12) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+4)))   **
     ((base + 16) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 4))          **
     ((base + 20) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+8)))   **
     ((base + 24) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 8))          **
     ((base + 28) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+12)))  **
     ((base + 32) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 12))         **
     ((base + 36) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+16)))  **
     ((base + 40) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 16))         **
     ((base + 44) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+20)))  **
     ((base + 48) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 20))         **
     ((base + 52) ↦ᵢ .LW .x7 .x12 (BitVec.ofNat 12 (n*32+24)))  **
     ((base + 56) ↦ᵢ .SW .x12 .x7 (BitVec.ofNat 12 24))         **
     (nsp ↦ₘ s0) ** ((nsp+4) ↦ₘ s1) ** ((nsp+8) ↦ₘ s2) ** ((nsp+12) ↦ₘ s3) **
     ((nsp+16) ↦ₘ s4) ** ((nsp+20) ↦ₘ s5) ** ((nsp+24) ↦ₘ s6) **
     ((nsp + BitVec.ofNat 32 (n*32))    ↦ₘ s0) **
     ((nsp + BitVec.ofNat 32 (n*32+4))  ↦ₘ s1) **
     ((nsp + BitVec.ofNat 32 (n*32+8))  ↦ₘ s2) **
     ((nsp + BitVec.ofNat 32 (n*32+12)) ↦ₘ s3) **
     ((nsp + BitVec.ofNat 32 (n*32+16)) ↦ₘ s4) **
     ((nsp + BitVec.ofNat 32 (n*32+20)) ↦ₘ s5) **
     ((nsp + BitVec.ofNat 32 (n*32+24)) ↦ₘ s6))
    (by pcFree) P7_raw
  clear P7_raw
  -- Final composition and permutation to match goal
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp) (fun h hq => by xperm_hyp hq)
    (cpsTriple_seq_with_perm _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp) sAP0123456 P7)
-/

-- ============================================================================
-- Stack-level DUP spec
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- DUPn spec at evmWordIs level: copies the nth stack element (0-indexed: element n-1)
    from evmStackIs to a new top position, leaving the rest unchanged. -/
theorem evm_dup_evmword_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (src dst : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    let code := evm_dup_code n base
    cpsTriple base (base + 68) code
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       evmWordIs nsp dst **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ src.getLimb 7) **
       evmWordIs nsp src **
       evmWordIs (nsp + BitVec.ofNat 32 (n * 32)) src) := by
  sorry

set_option maxHeartbeats 3200000 in
/-- DUPn stack spec: copies the (n-1)-th element (0-indexed) from the stack
    to a new top, leaving the stack unchanged. -/
theorem evm_dup_stack_spec (nsp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (stack : List EvmWord) (hlen : n ≤ stack.length)
    (d : EvmWord) (v7 : Word)
    (hvalid : ValidMemRange nsp ((n + 1) * 8)) :
    let vn := stack[n - 1]'(by omega)
    let code := evm_dup_code n base
    cpsTriple base (base + 68) code
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

/-- Code requirement for generic SWAPn: 8 x (LW + LW + SW + SW) = 32 instructions. -/
abbrev evm_swap_code (n : Nat) (base : Addr) : CodeReq :=
  CodeReq.union (CodeReq.singleton base (.LW .x7 .x12 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 4) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 8) (.SW .x12 .x6 (BitVec.ofNat 12 0)))
  (CodeReq.union (CodeReq.singleton (base + 12) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32))))
  (CodeReq.union (CodeReq.singleton (base + 16) (.LW .x7 .x12 (BitVec.ofNat 12 4)))
  (CodeReq.union (CodeReq.singleton (base + 20) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+4))))
  (CodeReq.union (CodeReq.singleton (base + 24) (.SW .x12 .x6 (BitVec.ofNat 12 4)))
  (CodeReq.union (CodeReq.singleton (base + 28) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+4))))
  (CodeReq.union (CodeReq.singleton (base + 32) (.LW .x7 .x12 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 36) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 40) (.SW .x12 .x6 (BitVec.ofNat 12 8)))
  (CodeReq.union (CodeReq.singleton (base + 44) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+8))))
  (CodeReq.union (CodeReq.singleton (base + 48) (.LW .x7 .x12 (BitVec.ofNat 12 12)))
  (CodeReq.union (CodeReq.singleton (base + 52) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+12))))
  (CodeReq.union (CodeReq.singleton (base + 56) (.SW .x12 .x6 (BitVec.ofNat 12 12)))
  (CodeReq.union (CodeReq.singleton (base + 60) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+12))))
  (CodeReq.union (CodeReq.singleton (base + 64) (.LW .x7 .x12 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 68) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 72) (.SW .x12 .x6 (BitVec.ofNat 12 16)))
  (CodeReq.union (CodeReq.singleton (base + 76) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+16))))
  (CodeReq.union (CodeReq.singleton (base + 80) (.LW .x7 .x12 (BitVec.ofNat 12 20)))
  (CodeReq.union (CodeReq.singleton (base + 84) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+20))))
  (CodeReq.union (CodeReq.singleton (base + 88) (.SW .x12 .x6 (BitVec.ofNat 12 20)))
  (CodeReq.union (CodeReq.singleton (base + 92) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+20))))
  (CodeReq.union (CodeReq.singleton (base + 96) (.LW .x7 .x12 (BitVec.ofNat 12 24)))
  (CodeReq.union (CodeReq.singleton (base + 100) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+24))))
  (CodeReq.union (CodeReq.singleton (base + 104) (.SW .x12 .x6 (BitVec.ofNat 12 24)))
  (CodeReq.union (CodeReq.singleton (base + 108) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+24))))
  (CodeReq.union (CodeReq.singleton (base + 112) (.LW .x7 .x12 (BitVec.ofNat 12 28)))
  (CodeReq.union (CodeReq.singleton (base + 116) (.LW .x6 .x12 (BitVec.ofNat 12 (n*32+28))))
  (CodeReq.union (CodeReq.singleton (base + 120) (.SW .x12 .x6 (BitVec.ofNat 12 28)))
   (CodeReq.singleton (base + 124) (.SW .x12 .x7 (BitVec.ofNat 12 (n*32+28))))))))))))))))))))))))))))))))))

set_option maxHeartbeats 3200000 in
/-- Generic SWAPn spec (low level): swaps 8 limbs at sp (top) with 8 limbs at sp+n*32 (nth).
    Requires 1 ≤ n ≤ 16 (valid EVM SWAP range). -/
theorem evm_swap_spec (sp base : Addr)
    (n : Nat) (hn1 : 1 ≤ n) (hn16 : n ≤ 16)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    let code := evm_swap_code n base
    cpsTriple base (base + 128) code
      -- Registers + memory
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
      -- Registers + memory (swapped)
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
    let code := evm_swap_code n base
    cpsTriple base (base + 128) code
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
    (stack : List EvmWord) (hlen : n < stack.length)
    (v7 v6 : Word)
    (hvalid : ValidMemRange sp ((n + 1) * 8)) :
    let code := evm_swap_code n base
    cpsTriple base (base + 128) code
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmStackIs sp stack)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ (stack[0]'(by omega)).getLimb 7) **
       (.x6 ↦ᵣ (stack[n]'(by omega)).getLimb 7) **
       evmStackIs sp (stack.set 0 (stack[n]'(by omega)) |>.set n (stack[0]'(by omega)))) := by
  sorry

end EvmAsm
