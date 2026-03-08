/-
  EvmAsm.Evm64.StackOps

  Verified 256-bit EVM stack manipulation opcodes (RV64):
  - POP: discard top of stack, sp += 32. 1 instruction.
  - PUSH0: push 0 onto stack, sp -= 32. 5 instructions.
  - DUP1: duplicate top of stack, sp -= 32. 9 instructions.
  - SWAP1: swap top two stack items, sp unchanged. 16 instructions.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Rv64

@[simp] theorem EvmWord.getLimb_zero (i : Fin 4) : (0 : EvmWord).getLimb i = 0 := by
  have h : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by native_decide
  exact h i

@[simp] theorem signExtend12_neg32 : signExtend12 (-32 : BitVec 12) = (-32 : Word) := by
  native_decide

-- ============================================================================
-- Program definitions
-- ============================================================================

def evm_pop : Program := ADDI .x12 .x12 32

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

def evm_dup1 : Program :=
  ADDI .x12 .x12 (-32) ;;
  LD .x7 .x12 32 ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 40 ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 48 ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 56 ;; SD .x12 .x7 24

def evm_swap1 : Program :=
  LD .x7 .x12 0  ;; LD .x6 .x12 32 ;; SD .x12 .x6 0  ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8  ;; LD .x6 .x12 40 ;; SD .x12 .x6 8  ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; SD .x12 .x6 16 ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; SD .x12 .x6 24 ;; SD .x12 .x7 56

-- ============================================================================
-- POP spec
-- ============================================================================

theorem evm_pop_spec (sp base : Addr) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ sp))
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ (sp + 32))) := by
  have h := addi_spec_gen_same .x12 sp 32 base (by nofun)
  simp only [signExtend12_32] at h; exact h

theorem evm_pop_stack_spec (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord) :
    cpsTriple base (base + 4)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((base ↦ᵢ .ADDI .x12 .x12 32) ** (.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) :=
  cpsTriple_consequence base (base + 4) _ _ _ _
    (fun h hp => (sepConj_assoc _ _ _ h).mpr hp)
    (fun h hq => (sepConj_assoc _ _ _ h).mp hq)
    (cpsTriple_frame_left base (base + 4) _ _ _ (by pcFree) (evm_pop_spec sp base))

-- ============================================================================
-- PUSH0 spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem evm_push0_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word)
    (hvalid : ValidMemRange nsp 4) :
    cpsTriple base (base + 20)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .SD .x12 .x0 0) ** ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 12) ↦ᵢ .SD .x12 .x0 16) ** ((base + 16) ↦ᵢ .SD .x12 .x0 24) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3))
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .SD .x12 .x0 0) ** ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 12) ↦ᵢ .SD .x12 .x0 16) ** ((base + 16) ↦ᵢ .SD .x12 .x0 24) **
       (.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0)) := by
  have hv0 : isValidDwordAccess (nsp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (nsp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (nsp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (nsp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; have := hvalid.get (i := 3) (by omega); simpa using this
  have LADDI := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have L0 := sd_x0_spec_gen .x12 nsp d0 0 (base + 4) hv0
  have L1 := sd_x0_spec_gen .x12 nsp d1 8 (base + 8) hv8
  have L2 := sd_x0_spec_gen .x12 nsp d2 16 (base + 12) hv16
  have L3 := sd_x0_spec_gen .x12 nsp d3 24 (base + 16) hv24
  runBlock LADDI L0 L1 L2 L3

theorem evm_push0_stack_spec (nsp base : Addr)
    (d0 d1 d2 d3 : Word) (rest : List EvmWord)
    (hvalid : ValidMemRange nsp 4) :
    cpsTriple base (base + 20)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .SD .x12 .x0 0) ** ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 12) ↦ᵢ .SD .x12 .x0 16) ** ((base + 16) ↦ᵢ .SD .x12 .x0 24) **
       (.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmStackIs (nsp + 32) rest)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .SD .x12 .x0 0) ** ((base + 8) ↦ᵢ .SD .x12 .x0 8) **
       ((base + 12) ↦ᵢ .SD .x12 .x0 16) ** ((base + 16) ↦ᵢ .SD .x12 .x0 24) **
       (.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) :=
  cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_zero]; xperm_hyp hq)
    (cpsTriple_frame_left _ _ _ _ (evmStackIs (nsp + 32) rest)
      (by exact pcFree_evmStackIs (nsp + 32) rest)
      (evm_push0_spec nsp base d0 d1 d2 d3 hvalid))

-- ============================================================================
-- DUP1 per-pair helper
-- ============================================================================

/-- Two-instruction spec for DUP1: LD x7 from source, SD x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hvalid_src : isValidDwordAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidDwordAccess (sp + signExtend12 off_dst) = true) :
    cpsTriple base (base + 8)
      ((base ↦ᵢ .LD .x7 .x12 off_src) ** ((base + 4) ↦ᵢ .SD .x12 .x7 off_dst) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((base ↦ᵢ .LD .x7 .x12 off_src) ** ((base + 4) ↦ᵢ .SD .x12 .x7 off_dst) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  runBlock

-- ============================================================================
-- DUP1 spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem evm_dup1_spec (nsp base : Addr)
    (a0 a1 a2 a3 d0 d1 d2 d3 : Word) (v7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple base (base + 36)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LD .x7 .x12 32) ** ((base + 8) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LD .x7 .x12 40) ** ((base + 16) ↦ᵢ .SD .x12 .x7 8) **
       ((base + 20) ↦ᵢ .LD .x7 .x12 48) ** ((base + 24) ↦ᵢ .SD .x12 .x7 16) **
       ((base + 28) ↦ᵢ .LD .x7 .x12 56) ** ((base + 32) ↦ᵢ .SD .x12 .x7 24) **
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 40) ↦ₘ a1) ** ((nsp + 48) ↦ₘ a2) ** ((nsp + 56) ↦ₘ a3))
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LD .x7 .x12 32) ** ((base + 8) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LD .x7 .x12 40) ** ((base + 16) ↦ᵢ .SD .x12 .x7 8) **
       ((base + 20) ↦ᵢ .LD .x7 .x12 48) ** ((base + 24) ↦ᵢ .SD .x12 .x7 16) **
       ((base + 28) ↦ᵢ .LD .x7 .x12 56) ** ((base + 32) ↦ᵢ .SD .x12 .x7 24) **
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a3) **
       (nsp ↦ₘ a0) ** ((nsp + 8) ↦ₘ a1) ** ((nsp + 16) ↦ₘ a2) ** ((nsp + 24) ↦ₘ a3) **
       ((nsp + 32) ↦ₘ a0) ** ((nsp + 40) ↦ₘ a1) ** ((nsp + 48) ↦ₘ a2) ** ((nsp + 56) ↦ₘ a3)) := by
  have hv0 : isValidDwordAccess (nsp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (nsp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (nsp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (nsp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; have := hvalid.get (i := 3) (by omega); simpa using this
  have hv32 : isValidDwordAccess (nsp + signExtend12 (32 : BitVec 12)) = true := by
    simp only [signExtend12_32]; have := hvalid.get (i := 4) (by omega); simpa using this
  have hv40 : isValidDwordAccess (nsp + signExtend12 (40 : BitVec 12)) = true := by
    simp only [signExtend12_40]; have := hvalid.get (i := 5) (by omega); simpa using this
  have hv48 : isValidDwordAccess (nsp + signExtend12 (48 : BitVec 12)) = true := by
    simp only [signExtend12_48]; have := hvalid.get (i := 6) (by omega); simpa using this
  have hv56 : isValidDwordAccess (nsp + signExtend12 (56 : BitVec 12)) = true := by
    simp only [signExtend12_56]; have := hvalid.get (i := 7) (by omega); simpa using this
  have LADDI := addi_spec_gen_same .x12 (nsp + 32) (-32) base (by nofun)
  simp only [signExtend12_neg32] at LADDI
  rw [show (nsp + 32 : Word) + (-32 : Word) = nsp from by bv_omega] at LADDI
  have P0 := dup1_pair_spec nsp 32 0 a0 d0 v7 (base + 4) hv32 hv0
  have P1 := dup1_pair_spec nsp 40 8 a1 d1 a0 (base + 12) hv40 hv8
  have P2 := dup1_pair_spec nsp 48 16 a2 d2 a1 (base + 20) hv48 hv16
  have P3 := dup1_pair_spec nsp 56 24 a3 d3 a2 (base + 28) hv56 hv24
  runBlock LADDI P0 P1 P2 P3

set_option maxHeartbeats 6400000 in
theorem evm_dup1_stack_spec (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 : Word) (v7 : Word)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple base (base + 36)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LD .x7 .x12 32) ** ((base + 8) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LD .x7 .x12 40) ** ((base + 16) ↦ᵢ .SD .x12 .x7 8) **
       ((base + 20) ↦ᵢ .LD .x7 .x12 48) ** ((base + 24) ↦ᵢ .SD .x12 .x7 16) **
       ((base + 28) ↦ᵢ .LD .x7 .x12 56) ** ((base + 32) ↦ᵢ .SD .x12 .x7 24) **
       (.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 8) ↦ₘ d1) ** ((nsp + 16) ↦ₘ d2) ** ((nsp + 24) ↦ₘ d3) **
       evmWordIs (nsp + 32) a)
      ((base ↦ᵢ .ADDI .x12 .x12 (-32)) **
       ((base + 4) ↦ᵢ .LD .x7 .x12 32) ** ((base + 8) ↦ᵢ .SD .x12 .x7 0) **
       ((base + 12) ↦ᵢ .LD .x7 .x12 40) ** ((base + 16) ↦ᵢ .SD .x12 .x7 8) **
       ((base + 20) ↦ᵢ .LD .x7 .x12 48) ** ((base + 24) ↦ᵢ .SD .x12 .x7 16) **
       ((base + 28) ↦ᵢ .LD .x7 .x12 56) ** ((base + 32) ↦ᵢ .SD .x12 .x7 24) **
       (.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a.getLimb 3) **
       evmWordIs nsp a ** evmWordIs (nsp + 32) a) := by
  have h_main := evm_dup1_spec nsp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3) d0 d1 d2 d3 v7 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (nsp : Addr) + 32 + 8 = nsp + 40 := by bv_omega
      have : (nsp : Addr) + 32 + 16 = nsp + 48 := by bv_omega
      have : (nsp : Addr) + 32 + 24 = nsp + 56 := by bv_omega
      rw [‹nsp + 32 + 8 = nsp + 40›, ‹nsp + 32 + 16 = nsp + 48›, ‹nsp + 32 + 24 = nsp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have : (nsp : Addr) + 32 + 8 = nsp + 40 := by bv_omega
      have : (nsp : Addr) + 32 + 16 = nsp + 48 := by bv_omega
      have : (nsp : Addr) + 32 + 24 = nsp + 56 := by bv_omega
      rw [‹nsp + 32 + 8 = nsp + 40›, ‹nsp + 32 + 16 = nsp + 48›, ‹nsp + 32 + 24 = nsp + 56›]
      xperm_hyp hq)
    h_main

-- ============================================================================
-- SWAP1 per-limb helper
-- ============================================================================

/-- Four-instruction spec for SWAP1 per-limb: LD x7 from A, LD x6 from B,
    SD x6 to A, SD x7 to B. Swaps values at offsets off_a and off_b. -/
theorem swap1_limb_spec (sp : Addr)
    (off_a off_b : BitVec 12) (a_val b_val v7 v6 : Word) (base : Addr)
    (hvalid_a : isValidDwordAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidDwordAccess (sp + signExtend12 off_b) = true) :
    cpsTriple base (base + 16)
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 off_a) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ a_val) ** ((sp + signExtend12 off_b) ↦ₘ b_val))
      ((base ↦ᵢ .LD .x7 .x12 off_a) ** ((base + 4) ↦ᵢ .LD .x6 .x12 off_b) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 off_a) ** ((base + 12) ↦ᵢ .SD .x12 .x7 off_b) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a_val) ** (.x6 ↦ᵣ b_val) **
       ((sp + signExtend12 off_a) ↦ₘ b_val) ** ((sp + signExtend12 off_b) ↦ₘ a_val)) := by
  runBlock

-- ============================================================================
-- SWAP1 spec
-- ============================================================================

set_option maxHeartbeats 6400000 in
theorem evm_swap1_spec (sp base : Addr)
    (a0 a1 a2 a3 b0 b1 b2 b3 v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 64)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 0) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .SD .x12 .x6 8) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .SD .x12 .x6 16) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .SD .x12 .x6 24) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       (sp ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 0) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .SD .x12 .x6 8) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .SD .x12 .x6 16) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .SD .x12 .x6 24) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a3) ** (.x6 ↦ᵣ b3) **
       (sp ↦ₘ b0) ** ((sp + 8) ↦ₘ b1) ** ((sp + 16) ↦ₘ b2) ** ((sp + 24) ↦ₘ b3) **
       ((sp + 32) ↦ₘ a0) ** ((sp + 40) ↦ₘ a1) ** ((sp + 48) ↦ₘ a2) ** ((sp + 56) ↦ₘ a3)) := by
  have hv0 : isValidDwordAccess (sp + signExtend12 (0 : BitVec 12)) = true := by
    simp only [signExtend12_0]; have := hvalid.get (i := 0) (by omega); simpa using this
  have hv8 : isValidDwordAccess (sp + signExtend12 (8 : BitVec 12)) = true := by
    simp only [signExtend12_8]; have := hvalid.get (i := 1) (by omega); simpa using this
  have hv16 : isValidDwordAccess (sp + signExtend12 (16 : BitVec 12)) = true := by
    simp only [signExtend12_16]; have := hvalid.get (i := 2) (by omega); simpa using this
  have hv24 : isValidDwordAccess (sp + signExtend12 (24 : BitVec 12)) = true := by
    simp only [signExtend12_24]; have := hvalid.get (i := 3) (by omega); simpa using this
  have hv32 : isValidDwordAccess (sp + signExtend12 (32 : BitVec 12)) = true := by
    simp only [signExtend12_32]; have := hvalid.get (i := 4) (by omega); simpa using this
  have hv40 : isValidDwordAccess (sp + signExtend12 (40 : BitVec 12)) = true := by
    simp only [signExtend12_40]; have := hvalid.get (i := 5) (by omega); simpa using this
  have hv48 : isValidDwordAccess (sp + signExtend12 (48 : BitVec 12)) = true := by
    simp only [signExtend12_48]; have := hvalid.get (i := 6) (by omega); simpa using this
  have hv56 : isValidDwordAccess (sp + signExtend12 (56 : BitVec 12)) = true := by
    simp only [signExtend12_56]; have := hvalid.get (i := 7) (by omega); simpa using this
  have L0 := swap1_limb_spec sp 0 32 a0 b0 v7 v6 base hv0 hv32
  have L1 := swap1_limb_spec sp 8 40 a1 b1 a0 b0 (base + 16) hv8 hv40
  have L2 := swap1_limb_spec sp 16 48 a2 b2 a1 b1 (base + 32) hv16 hv48
  have L3 := swap1_limb_spec sp 24 56 a3 b3 a2 b2 (base + 48) hv24 hv56
  runBlock L0 L1 L2 L3

set_option maxHeartbeats 6400000 in
theorem evm_swap1_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    cpsTriple base (base + 64)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 0) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .SD .x12 .x6 8) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .SD .x12 .x6 16) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .SD .x12 .x6 24) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      ((base ↦ᵢ .LD .x7 .x12 0) ** ((base + 4) ↦ᵢ .LD .x6 .x12 32) **
       ((base + 8) ↦ᵢ .SD .x12 .x6 0) ** ((base + 12) ↦ᵢ .SD .x12 .x7 32) **
       ((base + 16) ↦ᵢ .LD .x7 .x12 8) ** ((base + 20) ↦ᵢ .LD .x6 .x12 40) **
       ((base + 24) ↦ᵢ .SD .x12 .x6 8) ** ((base + 28) ↦ᵢ .SD .x12 .x7 40) **
       ((base + 32) ↦ᵢ .LD .x7 .x12 16) ** ((base + 36) ↦ᵢ .LD .x6 .x12 48) **
       ((base + 40) ↦ᵢ .SD .x12 .x6 16) ** ((base + 44) ↦ᵢ .SD .x12 .x7 48) **
       ((base + 48) ↦ᵢ .LD .x7 .x12 24) ** ((base + 52) ↦ᵢ .LD .x6 .x12 56) **
       ((base + 56) ↦ᵢ .SD .x12 .x6 24) ** ((base + 60) ↦ᵢ .SD .x12 .x7 56) **
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a.getLimb 3) ** (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp b ** evmWordIs (sp + 32) a) := by
  have h_main := evm_swap1_spec sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    v7 v6 hvalid
  exact cpsTriple_consequence _ _ _ _ _ _
    (fun h hp => by
      simp only [evmWordIs] at hp
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›] at hp
      xperm_hyp hp)
    (fun h hq => by
      simp only [evmWordIs]
      have : (sp : Addr) + 32 + 8 = sp + 40 := by bv_omega
      have : (sp : Addr) + 32 + 16 = sp + 48 := by bv_omega
      have : (sp : Addr) + 32 + 24 = sp + 56 := by bv_omega
      rw [‹sp + 32 + 8 = sp + 40›, ‹sp + 32 + 16 = sp + 48›, ‹sp + 32 + 24 = sp + 56›]
      xperm_hyp hq)
    h_main

end EvmAsm.Rv64
