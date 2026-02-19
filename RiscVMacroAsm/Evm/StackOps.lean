/-
  RiscVMacroAsm.Evm.StackOps

  Verified 256-bit EVM stack manipulation opcodes:
  - POP (Phase 2.1): discard top of stack, sp += 32. 1 instruction.
  - PUSH0 (Phase 2.2): push 0 onto stack, sp -= 32. 9 instructions.
  - DUP1 (Phase 2.3): duplicate top of stack, sp -= 32. 17 instructions.
  - SWAP1 (Phase 2.4): swap top two stack items, sp unchanged. 32 instructions.
-/

import RiscVMacroAsm.Evm.Stack
import RiscVMacroAsm.SyscallSpecs
import RiscVMacroAsm.Tactics.XSimp

open RiscVMacroAsm.Tactics

namespace RiscVMacroAsm

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

theorem evm_pop_spec (code : CodeMem) (sp base : Addr)
    (hcode : ProgramAt code base evm_pop) :
    cpsTriple code base (base + 4) (.x12 ↦ᵣ sp) (.x12 ↦ᵣ (sp + 32)) := by
  have hc0 := hcode.fetch 0 base (.ADDI .x12 .x12 32) (by decide) (by decide) (by bv_addr)
  have LA := addi_spec_gen_same code .x12 sp 32 base (by nofun) hc0
  simp only [signExtend12_32] at LA; exact LA

theorem evm_pop_stack_spec (code : CodeMem) (sp base : Addr)
    (a : EvmWord) (rest : List EvmWord)
    (hcode : ProgramAt code base evm_pop) :
    cpsTriple code base (base + 4)
      ((.x12 ↦ᵣ sp) ** evmWordIs sp a ** evmStackIs (sp + 32) rest)
      ((.x12 ↦ᵣ (sp + 32)) ** evmWordIs sp a ** evmStackIs (sp + 32) rest) := by
  have hc0 := hcode.fetch 0 base (.ADDI .x12 .x12 32) (by decide) (by decide) (by bv_addr)
  have LA := addi_spec_gen_same code .x12 sp 32 base (by nofun) hc0
  simp only [signExtend12_32] at LA
  exact cpsTriple_frame_left code base (base + 4) _ _
    (evmWordIs sp a ** evmStackIs (sp + 32) rest)
    (pcFree_sepConj (pcFree_evmWordIs sp a) (pcFree_evmStackIs (sp + 32) rest)) LA

-- ============================================================================
-- PUSH0 spec (Phase 2.2)
-- ============================================================================
theorem evm_push0_spec (code : CodeMem) (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (hcode : ProgramAt code base evm_push0)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple code base (base + 36)
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
      ((.x12 ↦ᵣ nsp) **
       (nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
       ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0) ** ((nsp + 28) ↦ₘ 0)) := by
  have hc0 := hcode.fetch 0 base        (.ADDI .x12 .x12 (-32)) (by decide) (by decide) (by bv_addr)
  have hc1 := hcode.fetch 1 (base + 4)  (.SW .x12 .x0 0)        (by decide) (by decide) (by bv_addr)
  have hc2 := hcode.fetch 2 (base + 8)  (.SW .x12 .x0 4)        (by decide) (by decide) (by bv_addr)
  have hc3 := hcode.fetch 3 (base + 12) (.SW .x12 .x0 8)        (by decide) (by decide) (by bv_addr)
  have hc4 := hcode.fetch 4 (base + 16) (.SW .x12 .x0 12)       (by decide) (by decide) (by bv_addr)
  have hc5 := hcode.fetch 5 (base + 20) (.SW .x12 .x0 16)       (by decide) (by decide) (by bv_addr)
  have hc6 := hcode.fetch 6 (base + 24) (.SW .x12 .x0 20)       (by decide) (by decide) (by bv_addr)
  have hc7 := hcode.fetch 7 (base + 28) (.SW .x12 .x0 24)       (by decide) (by decide) (by bv_addr)
  have hc8 := hcode.fetch 8 (base + 32) (.SW .x12 .x0 28)       (by decide) (by decide) (by bv_addr)
  have hv0  := hvalid.fetch 0 nsp        (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1 (nsp + 4)  (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2 (nsp + 8)  (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3 (nsp + 12) (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4 (nsp + 16) (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5 (nsp + 20) (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6 (nsp + 24) (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7 (nsp + 28) (by omega) (by bv_addr)
  -- ADDI x12, x12, -32: x12 goes nsp+32 → nsp
  have LA := addi_spec_gen_same code .x12 (nsp + 32) (-32 : BitVec 12) base (by nofun) hc0
  simp only [signExtend12_neg32] at LA
  rw [show (nsp + 32) + (-32 : Word) = nsp from by bv_addr] at LA
  have LAf := cpsTriple_frame_left code base (base + 4) _ _
    ((nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) LA
  -- SW x12, x0, 0: mem[nsp] := 0
  have S0 := sw_x0_spec_gen code .x12 nsp d0 0 (base + 4) hc1
    (by simp only [signExtend12_0]; rw [show nsp + (0 : Word) = nsp from by bv_addr]; exact hv0)
  simp only [signExtend12_0] at S0
  rw [show nsp + (0 : Word) = nsp from by bv_addr,
      show (base + 4) + 4 = base + 8 from by bv_addr] at S0
  have S0f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    (((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S0
  -- SW x12, x0, 4: mem[nsp+4] := 0
  have S1 := sw_x0_spec_gen code .x12 nsp d1 4 (base + 8) hc2
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_4] at S1
  rw [show (base + 8) + 4 = base + 12 from by bv_addr] at S1
  have S1f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S1
  -- SW x12, x0, 8: mem[nsp+8] := 0
  have S2 := sw_x0_spec_gen code .x12 nsp d2 8 (base + 12) hc3
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_8] at S2
  rw [show (base + 12) + 4 = base + 16 from by bv_addr] at S2
  have S2f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S2
  -- SW x12, x0, 12: mem[nsp+12] := 0
  have S3 := sw_x0_spec_gen code .x12 nsp d3 12 (base + 16) hc4
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_12] at S3
  rw [show (base + 16) + 4 = base + 20 from by bv_addr] at S3
  have S3f := cpsTriple_frame_left code (base + 16) (base + 20) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S3
  -- SW x12, x0, 16: mem[nsp+16] := 0
  have S4 := sw_x0_spec_gen code .x12 nsp d4 16 (base + 20) hc5
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_16] at S4
  rw [show (base + 20) + 4 = base + 24 from by bv_addr] at S4
  have S4f := cpsTriple_frame_left code (base + 20) (base + 24) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S4
  -- SW x12, x0, 20: mem[nsp+20] := 0
  have S5 := sw_x0_spec_gen code .x12 nsp d5 20 (base + 24) hc6
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_20] at S5
  rw [show (base + 24) + 4 = base + 28 from by bv_addr] at S5
  have S5f := cpsTriple_frame_left code (base + 24) (base + 28) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S5
  -- SW x12, x0, 24: mem[nsp+24] := 0
  have S6 := sw_x0_spec_gen code .x12 nsp d6 24 (base + 28) hc7
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_24] at S6
  rw [show (base + 28) + 4 = base + 32 from by bv_addr] at S6
  have S6f := cpsTriple_frame_left code (base + 28) (base + 32) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 28) ↦ₘ d7))
    (by pcFree) S6
  -- SW x12, x0, 28: mem[nsp+28] := 0
  have S7 := sw_x0_spec_gen code .x12 nsp d7 28 (base + 32) hc8
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_28] at S7
  rw [show (base + 32) + 4 = base + 36 from by bv_addr] at S7
  have S7f := cpsTriple_frame_left code (base + 32) (base + 36) _ _
    ((nsp ↦ₘ 0) ** ((nsp + 4) ↦ₘ 0) ** ((nsp + 8) ↦ₘ 0) ** ((nsp + 12) ↦ₘ 0) **
     ((nsp + 16) ↦ₘ 0) ** ((nsp + 20) ↦ₘ 0) ** ((nsp + 24) ↦ₘ 0))
    (by pcFree) S7
  -- Compose all 9 steps
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8
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

theorem evm_push0_stack_spec (code : CodeMem) (nsp base : Addr)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (rest : List EvmWord)
    (hcode : ProgramAt code base evm_push0)
    (hvalid : ValidMemRange nsp 8) :
    cpsTriple code base (base + 36)
      ((.x12 ↦ᵣ (nsp + 32)) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmStackIs (nsp + 32) rest)
      ((.x12 ↦ᵣ nsp) ** evmWordIs nsp 0 ** evmStackIs (nsp + 32) rest) := by
  have base_spec := evm_push0_spec code nsp base d0 d1 d2 d3 d4 d5 d6 d7 hcode hvalid
  have framed := cpsTriple_frame_left code base (base + 36) _ _
    (evmStackIs (nsp + 32) rest) (pcFree_evmStackIs (nsp + 32) rest) base_spec
  apply cpsTriple_consequence code base (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) _ framed
  intro h hp
  simp only [evmWordIs, EvmWord.getLimb_zero]
  xperm_hyp hp

-- ============================================================================
-- DUP1 per-pair helper (Phase 2.3)
-- ============================================================================

/-- Two-instruction spec for DUP1: LW x7 from source, SW x7 to destination.
    Copies src_val from src address to dst address. -/
theorem dup1_pair_spec (code : CodeMem) (sp : Addr)
    (off_src off_dst : BitVec 12) (src_val dst_old v7 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_src))
    (hf2 : code (base + 4) = some (.SW .x12 .x7 off_dst))
    (hvalid_src : isValidMemAccess (sp + signExtend12 off_src) = true)
    (hvalid_dst : isValidMemAccess (sp + signExtend12 off_dst) = true) :
    cpsTriple code base (base + 8)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ dst_old))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ src_val) **
       ((sp + signExtend12 off_src) ↦ₘ src_val) ** ((sp + signExtend12 off_dst) ↦ₘ src_val)) := by
  have lw := lw_spec_gen code .x7 .x12 sp v7 src_val off_src base (by nofun) hf1 hvalid_src
  have sw := sw_spec_gen code .x12 .x7 sp src_val dst_old off_dst (base + 4) hf2 hvalid_dst
  rw [show (base + 4) + 4 = base + 8 from by bv_addr] at sw
  have lwf := cpsTriple_frame_left code base (base + 4) _ _
    ((sp + signExtend12 off_dst) ↦ₘ dst_old) (by pcFree) lw
  have swf := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((sp + signExtend12 off_src) ↦ₘ src_val) (by pcFree) sw
  have c := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) lwf swf
  exact cpsTriple_consequence code base (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) c

-- ============================================================================
-- DUP1 spec (Phase 2.3)
-- ============================================================================

theorem evm_dup1_spec (code : CodeMem) (nsp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 : Word)
    (v7 : Word)
    (hcode : ProgramAt code base evm_dup1)
    (hvalid : ValidMemRange nsp 16) :
    cpsTriple code base (base + 68)
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
  have hc0  := hcode.fetch 0  base        (.ADDI .x12 .x12 (-32))  (by decide) (by decide) (by bv_addr)
  have hc1  := hcode.fetch 1  (base + 4)  (.LW .x7 .x12 32)        (by decide) (by decide) (by bv_addr)
  have hc2  := hcode.fetch 2  (base + 8)  (.SW .x12 .x7 0)         (by decide) (by decide) (by bv_addr)
  have hc3  := hcode.fetch 3  (base + 12) (.LW .x7 .x12 36)        (by decide) (by decide) (by bv_addr)
  have hc4  := hcode.fetch 4  (base + 16) (.SW .x12 .x7 4)         (by decide) (by decide) (by bv_addr)
  have hc5  := hcode.fetch 5  (base + 20) (.LW .x7 .x12 40)        (by decide) (by decide) (by bv_addr)
  have hc6  := hcode.fetch 6  (base + 24) (.SW .x12 .x7 8)         (by decide) (by decide) (by bv_addr)
  have hc7  := hcode.fetch 7  (base + 28) (.LW .x7 .x12 44)        (by decide) (by decide) (by bv_addr)
  have hc8  := hcode.fetch 8  (base + 32) (.SW .x12 .x7 12)        (by decide) (by decide) (by bv_addr)
  have hc9  := hcode.fetch 9  (base + 36) (.LW .x7 .x12 48)        (by decide) (by decide) (by bv_addr)
  have hc10 := hcode.fetch 10 (base + 40) (.SW .x12 .x7 16)        (by decide) (by decide) (by bv_addr)
  have hc11 := hcode.fetch 11 (base + 44) (.LW .x7 .x12 52)        (by decide) (by decide) (by bv_addr)
  have hc12 := hcode.fetch 12 (base + 48) (.SW .x12 .x7 20)        (by decide) (by decide) (by bv_addr)
  have hc13 := hcode.fetch 13 (base + 52) (.LW .x7 .x12 56)        (by decide) (by decide) (by bv_addr)
  have hc14 := hcode.fetch 14 (base + 56) (.SW .x12 .x7 24)        (by decide) (by decide) (by bv_addr)
  have hc15 := hcode.fetch 15 (base + 60) (.LW .x7 .x12 60)        (by decide) (by decide) (by bv_addr)
  have hc16 := hcode.fetch 16 (base + 64) (.SW .x12 .x7 28)        (by decide) (by decide) (by bv_addr)
  have hv0  := hvalid.fetch 0  nsp         (by omega) (by bv_addr)
  have hv4  := hvalid.fetch 1  (nsp + 4)   (by omega) (by bv_addr)
  have hv8  := hvalid.fetch 2  (nsp + 8)   (by omega) (by bv_addr)
  have hv12 := hvalid.fetch 3  (nsp + 12)  (by omega) (by bv_addr)
  have hv16 := hvalid.fetch 4  (nsp + 16)  (by omega) (by bv_addr)
  have hv20 := hvalid.fetch 5  (nsp + 20)  (by omega) (by bv_addr)
  have hv24 := hvalid.fetch 6  (nsp + 24)  (by omega) (by bv_addr)
  have hv28 := hvalid.fetch 7  (nsp + 28)  (by omega) (by bv_addr)
  have hv32 := hvalid.fetch 8  (nsp + 32)  (by omega) (by bv_addr)
  have hv36 := hvalid.fetch 9  (nsp + 36)  (by omega) (by bv_addr)
  have hv40 := hvalid.fetch 10 (nsp + 40)  (by omega) (by bv_addr)
  have hv44 := hvalid.fetch 11 (nsp + 44)  (by omega) (by bv_addr)
  have hv48 := hvalid.fetch 12 (nsp + 48)  (by omega) (by bv_addr)
  have hv52 := hvalid.fetch 13 (nsp + 52)  (by omega) (by bv_addr)
  have hv56 := hvalid.fetch 14 (nsp + 56)  (by omega) (by bv_addr)
  have hv60 := hvalid.fetch 15 (nsp + 60)  (by omega) (by bv_addr)
  -- ADDI x12, x12, -32: x12 goes nsp+32 → nsp
  have LA := addi_spec_gen_same code .x12 (nsp + 32) (-32 : BitVec 12) base (by nofun) hc0
  simp only [signExtend12_neg32] at LA
  rw [show (nsp + 32) + (-32 : Word) = nsp from by bv_addr] at LA
  have LAf := cpsTriple_frame_left code base (base + 4) _ _
    ((.x7 ↦ᵣ v7) **
     (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) LA
  -- Pair 0: LW x7 from nsp+32, SW to nsp
  have P0 := dup1_pair_spec code nsp 32 0 a0 d0 v7 (base + 4) hc1
    (by rw [show (base + 4) + 4 = base + 8 from by bv_addr]; exact hc2)
    (by simp only [signExtend12_32]; exact hv32)
    (by simp only [signExtend12_0]; rw [show nsp + (0 : Word) = nsp from by bv_addr]; exact hv0)
  simp only [signExtend12_32, signExtend12_0] at P0
  rw [show nsp + (0 : Word) = nsp from by bv_addr,
      show (base + 4) + 8 = base + 12 from by bv_addr] at P0
  have P0f := cpsTriple_frame_left code (base + 4) (base + 12) _ _
    (((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P0
  -- Pair 1: LW x7 from nsp+36, SW to nsp+4
  have P1 := dup1_pair_spec code nsp 36 4 a1 d1 a0 (base + 12) hc3
    (by rw [show (base + 12) + 4 = base + 16 from by bv_addr]; exact hc4)
    (by simp only [signExtend12_36]; exact hv36)
    (by simp only [signExtend12_4]; exact hv4)
  simp only [signExtend12_36, signExtend12_4] at P1
  rw [show (base + 12) + 8 = base + 20 from by bv_addr] at P1
  have P1f := cpsTriple_frame_left code (base + 12) (base + 20) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P1
  -- Pair 2: LW x7 from nsp+40, SW to nsp+8
  have P2 := dup1_pair_spec code nsp 40 8 a2 d2 a1 (base + 20) hc5
    (by rw [show (base + 20) + 4 = base + 24 from by bv_addr]; exact hc6)
    (by simp only [signExtend12_40]; exact hv40)
    (by simp only [signExtend12_8]; exact hv8)
  simp only [signExtend12_40, signExtend12_8] at P2
  rw [show (base + 20) + 8 = base + 28 from by bv_addr] at P2
  have P2f := cpsTriple_frame_left code (base + 20) (base + 28) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 12) ↦ₘ d3) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P2
  -- Pair 3: LW x7 from nsp+44, SW to nsp+12
  have P3 := dup1_pair_spec code nsp 44 12 a3 d3 a2 (base + 28) hc7
    (by rw [show (base + 28) + 4 = base + 32 from by bv_addr]; exact hc8)
    (by simp only [signExtend12_44]; exact hv44)
    (by simp only [signExtend12_12]; exact hv12)
  simp only [signExtend12_44, signExtend12_12] at P3
  rw [show (base + 28) + 8 = base + 36 from by bv_addr] at P3
  have P3f := cpsTriple_frame_left code (base + 28) (base + 36) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) **
     ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P3
  -- Pair 4: LW x7 from nsp+48, SW to nsp+16
  have P4 := dup1_pair_spec code nsp 48 16 a4 d4 a3 (base + 36) hc9
    (by rw [show (base + 36) + 4 = base + 40 from by bv_addr]; exact hc10)
    (by simp only [signExtend12_48]; exact hv48)
    (by simp only [signExtend12_16]; exact hv16)
  simp only [signExtend12_48, signExtend12_16] at P4
  rw [show (base + 36) + 8 = base + 44 from by bv_addr] at P4
  have P4f := cpsTriple_frame_left code (base + 36) (base + 44) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
     ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P4
  -- Pair 5: LW x7 from nsp+52, SW to nsp+20
  have P5 := dup1_pair_spec code nsp 52 20 a5 d5 a4 (base + 44) hc11
    (by rw [show (base + 44) + 4 = base + 48 from by bv_addr]; exact hc12)
    (by simp only [signExtend12_52]; exact hv52)
    (by simp only [signExtend12_20]; exact hv20)
  simp only [signExtend12_52, signExtend12_20] at P5
  rw [show (base + 44) + 8 = base + 52 from by bv_addr] at P5
  have P5f := cpsTriple_frame_left code (base + 44) (base + 52) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
     ((nsp + 16) ↦ₘ a4) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 56) ↦ₘ a6) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P5
  -- Pair 6: LW x7 from nsp+56, SW to nsp+24
  have P6 := dup1_pair_spec code nsp 56 24 a6 d6 a5 (base + 52) hc13
    (by rw [show (base + 52) + 4 = base + 56 from by bv_addr]; exact hc14)
    (by simp only [signExtend12_56]; exact hv56)
    (by simp only [signExtend12_24]; exact hv24)
  simp only [signExtend12_56, signExtend12_24] at P6
  rw [show (base + 52) + 8 = base + 60 from by bv_addr] at P6
  have P6f := cpsTriple_frame_left code (base + 52) (base + 60) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
     ((nsp + 16) ↦ₘ a4) ** ((nsp + 20) ↦ₘ a5) ** ((nsp + 28) ↦ₘ d7) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 60) ↦ₘ a7))
    (by pcFree) P6
  -- Pair 7: LW x7 from nsp+60, SW to nsp+28
  have P7 := dup1_pair_spec code nsp 60 28 a7 d7 a6 (base + 60) hc15
    (by rw [show (base + 60) + 4 = base + 64 from by bv_addr]; exact hc16)
    (by simp only [signExtend12_60]; exact hv60)
    (by simp only [signExtend12_28]; exact hv28)
  simp only [signExtend12_60, signExtend12_28] at P7
  rw [show (base + 60) + 8 = base + 68 from by bv_addr] at P7
  have P7f := cpsTriple_frame_left code (base + 60) (base + 68) _ _
    ((nsp ↦ₘ a0) ** ((nsp + 4) ↦ₘ a1) ** ((nsp + 8) ↦ₘ a2) ** ((nsp + 12) ↦ₘ a3) **
     ((nsp + 16) ↦ₘ a4) ** ((nsp + 20) ↦ₘ a5) ** ((nsp + 24) ↦ₘ a6) **
     ((nsp + 32) ↦ₘ a0) ** ((nsp + 36) ↦ₘ a1) ** ((nsp + 40) ↦ₘ a2) ** ((nsp + 44) ↦ₘ a3) **
     ((nsp + 48) ↦ₘ a4) ** ((nsp + 52) ↦ₘ a5) ** ((nsp + 56) ↦ₘ a6))
    (by pcFree) P7
  -- Compose all steps
  clear hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14 hc15 hc16
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28 hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear LA P0 P1 P2 P3 P4 P5 P6 P7
  have c01 := cpsTriple_seq_with_perm code base (base + 4) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) LAf P0f; clear LAf P0f
  have c02 := cpsTriple_seq_with_perm code base (base + 12) (base + 20) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 P1f; clear c01 P1f
  have c03 := cpsTriple_seq_with_perm code base (base + 20) (base + 28) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 P2f; clear c02 P2f
  have c04 := cpsTriple_seq_with_perm code base (base + 28) (base + 36) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 P3f; clear c03 P3f
  have c05 := cpsTriple_seq_with_perm code base (base + 36) (base + 44) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 P4f; clear c04 P4f
  have c06 := cpsTriple_seq_with_perm code base (base + 44) (base + 52) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 P5f; clear c05 P5f
  have c07 := cpsTriple_seq_with_perm code base (base + 52) (base + 60) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 P6f; clear c06 P6f
  have cfull := cpsTriple_seq_with_perm code base (base + 60) (base + 68) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c07 P7f; clear c07 P7f
  exact cpsTriple_consequence code base (base + 68) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

theorem evm_dup1_stack_spec (code : CodeMem) (nsp base : Addr)
    (a : EvmWord) (d0 d1 d2 d3 d4 d5 d6 d7 : Word) (v7 : Word) (rest : List EvmWord)
    (hcode : ProgramAt code base evm_dup1)
    (hvalid : ValidMemRange nsp 16) :
    cpsTriple code base (base + 68)
      ((.x12 ↦ᵣ (nsp + 32)) ** (.x7 ↦ᵣ v7) **
       (nsp ↦ₘ d0) ** ((nsp + 4) ↦ₘ d1) ** ((nsp + 8) ↦ₘ d2) ** ((nsp + 12) ↦ₘ d3) **
       ((nsp + 16) ↦ₘ d4) ** ((nsp + 20) ↦ₘ d5) ** ((nsp + 24) ↦ₘ d6) ** ((nsp + 28) ↦ₘ d7) **
       evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest)
      ((.x12 ↦ᵣ nsp) ** (.x7 ↦ᵣ a.getLimb 7) **
       evmWordIs nsp a ** evmWordIs (nsp + 32) a ** evmStackIs (nsp + 64) rest) := by
  simp only [evmWordIs, sepConj_assoc']
  have h36 : nsp + 32 + 4  = nsp + 36 := by bv_addr
  have h40 : nsp + 32 + 8  = nsp + 40 := by bv_addr
  have h44 : nsp + 32 + 12 = nsp + 44 := by bv_addr
  have h48 : nsp + 32 + 16 = nsp + 48 := by bv_addr
  have h52 : nsp + 32 + 20 = nsp + 52 := by bv_addr
  have h56 : nsp + 32 + 24 = nsp + 56 := by bv_addr
  have h60 : nsp + 32 + 28 = nsp + 60 := by bv_addr
  simp only [h36, h40, h44, h48, h52, h56, h60]
  have base_spec := evm_dup1_spec code nsp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    d0 d1 d2 d3 d4 d5 d6 d7 v7 hcode hvalid
  have framed := cpsTriple_frame_left code base (base + 68) _ _
    (evmStackIs (nsp + 64) rest) (pcFree_evmStackIs (nsp + 64) rest) base_spec
  exact cpsTriple_consequence code base (base + 68) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) framed

-- ============================================================================
-- SWAP1 per-limb helper (Phase 2.4)
-- ============================================================================

/-- Four-instruction spec for SWAP1: loads a from off_a into x7, b from off_b into x6,
    writes b to off_a, writes a to off_b. Net effect: swaps the two memory cells. -/
theorem swap1_limb_spec (code : CodeMem) (sp : Addr)
    (off_a off_b : BitVec 12) (a b v7 v6 : Word) (base : Addr)
    (hf1 : code base = some (.LW .x7 .x12 off_a))
    (hf2 : code (base + 4) = some (.LW .x6 .x12 off_b))
    (hf3 : code (base + 8) = some (.SW .x12 .x6 off_a))
    (hf4 : code (base + 12) = some (.SW .x12 .x7 off_b))
    (hvalid_a : isValidMemAccess (sp + signExtend12 off_a) = true)
    (hvalid_b : isValidMemAccess (sp + signExtend12 off_b) = true) :
    cpsTriple code base (base + 16)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       ((sp + signExtend12 off_a) ↦ₘ a) ** ((sp + signExtend12 off_b) ↦ₘ b))
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a) ** (.x6 ↦ᵣ b) **
       ((sp + signExtend12 off_a) ↦ₘ b) ** ((sp + signExtend12 off_b) ↦ₘ a)) := by
  have lw1 := lw_spec_gen code .x7 .x12 sp v7 a off_a base (by nofun) hf1 hvalid_a
  have lw2 := lw_spec_gen code .x6 .x12 sp v6 b off_b (base + 4) (by nofun) hf2 hvalid_b
  have sw1 := sw_spec_gen code .x12 .x6 sp b a off_a (base + 8) hf3 hvalid_a
  have sw2 := sw_spec_gen code .x12 .x7 sp a b off_b (base + 12) hf4 hvalid_b
  rw [show (base + 4) + 4 = base + 8 from by bv_addr] at lw2
  rw [show (base + 8) + 4 = base + 12 from by bv_addr] at sw1
  rw [show (base + 12) + 4 = base + 16 from by bv_addr] at sw2
  have lw1f := cpsTriple_frame_left code base (base + 4) _ _
    ((.x6 ↦ᵣ v6) ** ((sp + signExtend12 off_b) ↦ₘ b)) (by pcFree) lw1
  have lw2f := cpsTriple_frame_left code (base + 4) (base + 8) _ _
    ((.x7 ↦ᵣ a) ** ((sp + signExtend12 off_a) ↦ₘ a)) (by pcFree) lw2
  have sw1f := cpsTriple_frame_left code (base + 8) (base + 12) _ _
    ((.x7 ↦ᵣ a) ** ((sp + signExtend12 off_b) ↦ₘ b)) (by pcFree) sw1
  have sw2f := cpsTriple_frame_left code (base + 12) (base + 16) _ _
    ((.x6 ↦ᵣ b) ** ((sp + signExtend12 off_a) ↦ₘ b)) (by pcFree) sw2
  have c12 := cpsTriple_seq_with_perm code base (base + 4) (base + 8) _ _ _ _
    (fun _ hp => by xperm_hyp hp) lw1f lw2f
  have c123 := cpsTriple_seq_with_perm code base (base + 8) (base + 12) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c12 sw1f
  have c1234 := cpsTriple_seq_with_perm code base (base + 12) (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c123 sw2f
  exact cpsTriple_consequence code base (base + 16) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) c1234

-- ============================================================================
-- SWAP1 spec (Phase 2.4)
-- ============================================================================

set_option maxHeartbeats 3200000 in
theorem evm_swap1_spec (code : CodeMem) (sp base : Addr)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Word)
    (b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (v7 v6 : Word)
    (hcode : ProgramAt code base evm_swap1)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple code base (base + 128)
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
  -- Limb 0 (off_a=0, off_b=32): swap sp ↔ sp+32
  have L0 := swap1_limb_spec code sp 0 32 a0 b0 v7 v6 base
    (hcode.fetch 0  base        (.LW .x7 .x12 0)  (by decide) (by decide) (by bv_addr))
    (hcode.fetch 1  (base + 4)  (.LW .x6 .x12 32) (by decide) (by decide) (by bv_addr))
    (hcode.fetch 2  (base + 8)  (.SW .x12 .x6 0)  (by decide) (by decide) (by bv_addr))
    (hcode.fetch 3  (base + 12) (.SW .x12 .x7 32) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_0]; rw [show sp + (0:Word) = sp from by bv_addr]; exact hv0)
    (by simp only [signExtend12_32]; exact hv32)
  simp only [signExtend12_0, signExtend12_32] at L0
  rw [show sp + (0:Word) = sp from by bv_addr,
      show base + 16 = base + 16 from rfl] at L0
  have L0f := cpsTriple_frame_left code base (base + 16) _ _
    (((sp + 4) ↦ₘ a1) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 36) ↦ₘ b1) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L0
  -- Limb 1 (off_a=4, off_b=36): swap sp+4 ↔ sp+36
  have L1 := swap1_limb_spec code sp 4 36 a1 b1 a0 b0 (base + 16)
    (hcode.fetch 4  (base + 16) (.LW .x7 .x12 4)  (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 16) + 4  = base + 20 from by bv_addr]; exact
        hcode.fetch 5  (base + 20) (.LW .x6 .x12 36) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 16) + 8  = base + 24 from by bv_addr]; exact
        hcode.fetch 6  (base + 24) (.SW .x12 .x6 4)  (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 16) + 12 = base + 28 from by bv_addr]; exact
        hcode.fetch 7  (base + 28) (.SW .x12 .x7 36) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_4]; exact hv4)
    (by simp only [signExtend12_36]; exact hv36)
  simp only [signExtend12_4, signExtend12_36] at L1
  rw [show (base + 16) + 16 = base + 32 from by bv_addr] at L1
  have L1f := cpsTriple_frame_left code (base + 16) (base + 32) _ _
    ((sp ↦ₘ b0) ** ((sp + 8) ↦ₘ a2) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 40) ↦ₘ b2) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L1
  -- Limb 2 (off_a=8, off_b=40): swap sp+8 ↔ sp+40
  have L2 := swap1_limb_spec code sp 8 40 a2 b2 a1 b1 (base + 32)
    (hcode.fetch 8  (base + 32) (.LW .x7 .x12 8)  (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 32) + 4  = base + 36 from by bv_addr]; exact
        hcode.fetch 9  (base + 36) (.LW .x6 .x12 40) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 32) + 8  = base + 40 from by bv_addr]; exact
        hcode.fetch 10 (base + 40) (.SW .x12 .x6 8)  (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 32) + 12 = base + 44 from by bv_addr]; exact
        hcode.fetch 11 (base + 44) (.SW .x12 .x7 40) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_8]; exact hv8)
    (by simp only [signExtend12_40]; exact hv40)
  simp only [signExtend12_8, signExtend12_40] at L2
  rw [show (base + 32) + 16 = base + 48 from by bv_addr] at L2
  have L2f := cpsTriple_frame_left code (base + 32) (base + 48) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 12) ↦ₘ a3) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 44) ↦ₘ b3) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L2
  -- Limb 3 (off_a=12, off_b=44): swap sp+12 ↔ sp+44
  have L3 := swap1_limb_spec code sp 12 44 a3 b3 a2 b2 (base + 48)
    (hcode.fetch 12 (base + 48) (.LW .x7 .x12 12) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 48) + 4  = base + 52 from by bv_addr]; exact
        hcode.fetch 13 (base + 52) (.LW .x6 .x12 44) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 48) + 8  = base + 56 from by bv_addr]; exact
        hcode.fetch 14 (base + 56) (.SW .x12 .x6 12) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 48) + 12 = base + 60 from by bv_addr]; exact
        hcode.fetch 15 (base + 60) (.SW .x12 .x7 44) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_12]; exact hv12)
    (by simp only [signExtend12_44]; exact hv44)
  simp only [signExtend12_12, signExtend12_44] at L3
  rw [show (base + 48) + 16 = base + 64 from by bv_addr] at L3
  have L3f := cpsTriple_frame_left code (base + 48) (base + 64) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) **
     ((sp + 16) ↦ₘ a4) ** ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) **
     ((sp + 48) ↦ₘ b4) ** ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L3
  -- Limb 4 (off_a=16, off_b=48): swap sp+16 ↔ sp+48
  have L4 := swap1_limb_spec code sp 16 48 a4 b4 a3 b3 (base + 64)
    (hcode.fetch 16 (base + 64) (.LW .x7 .x12 16) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 64) + 4  = base + 68 from by bv_addr]; exact
        hcode.fetch 17 (base + 68) (.LW .x6 .x12 48) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 64) + 8  = base + 72 from by bv_addr]; exact
        hcode.fetch 18 (base + 72) (.SW .x12 .x6 16) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 64) + 12 = base + 76 from by bv_addr]; exact
        hcode.fetch 19 (base + 76) (.SW .x12 .x7 48) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_16]; exact hv16)
    (by simp only [signExtend12_48]; exact hv48)
  simp only [signExtend12_16, signExtend12_48] at L4
  rw [show (base + 64) + 16 = base + 80 from by bv_addr] at L4
  have L4f := cpsTriple_frame_left code (base + 64) (base + 80) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
     ((sp + 20) ↦ₘ a5) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
     ((sp + 52) ↦ₘ b5) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L4
  -- Limb 5 (off_a=20, off_b=52): swap sp+20 ↔ sp+52
  have L5 := swap1_limb_spec code sp 20 52 a5 b5 a4 b4 (base + 80)
    (hcode.fetch 20 (base + 80) (.LW .x7 .x12 20) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 80) + 4  = base + 84 from by bv_addr]; exact
        hcode.fetch 21 (base + 84) (.LW .x6 .x12 52) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 80) + 8  = base + 88 from by bv_addr]; exact
        hcode.fetch 22 (base + 88) (.SW .x12 .x6 20) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 80) + 12 = base + 92 from by bv_addr]; exact
        hcode.fetch 23 (base + 92) (.SW .x12 .x7 52) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_20]; exact hv20)
    (by simp only [signExtend12_52]; exact hv52)
  simp only [signExtend12_20, signExtend12_52] at L5
  rw [show (base + 80) + 16 = base + 96 from by bv_addr] at L5
  have L5f := cpsTriple_frame_left code (base + 80) (base + 96) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
     ((sp + 16) ↦ₘ b4) ** ((sp + 24) ↦ₘ a6) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
     ((sp + 48) ↦ₘ a4) ** ((sp + 56) ↦ₘ b6) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L5
  -- Limb 6 (off_a=24, off_b=56): swap sp+24 ↔ sp+56
  have L6 := swap1_limb_spec code sp 24 56 a6 b6 a5 b5 (base + 96)
    (hcode.fetch 24 (base + 96)  (.LW .x7 .x12 24) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 96) + 4  = base + 100 from by bv_addr]; exact
        hcode.fetch 25 (base + 100) (.LW .x6 .x12 56) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 96) + 8  = base + 104 from by bv_addr]; exact
        hcode.fetch 26 (base + 104) (.SW .x12 .x6 24) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 96) + 12 = base + 108 from by bv_addr]; exact
        hcode.fetch 27 (base + 108) (.SW .x12 .x7 56) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_24]; exact hv24)
    (by simp only [signExtend12_56]; exact hv56)
  simp only [signExtend12_24, signExtend12_56] at L6
  rw [show (base + 96) + 16 = base + 112 from by bv_addr] at L6
  have L6f := cpsTriple_frame_left code (base + 96) (base + 112) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
     ((sp + 16) ↦ₘ b4) ** ((sp + 20) ↦ₘ b5) ** ((sp + 28) ↦ₘ a7) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
     ((sp + 48) ↦ₘ a4) ** ((sp + 52) ↦ₘ a5) ** ((sp + 60) ↦ₘ b7))
    (by pcFree) L6
  -- Limb 7 (off_a=28, off_b=60): swap sp+28 ↔ sp+60
  have L7 := swap1_limb_spec code sp 28 60 a7 b7 a6 b6 (base + 112)
    (hcode.fetch 28 (base + 112) (.LW .x7 .x12 28) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 112) + 4  = base + 116 from by bv_addr]; exact
        hcode.fetch 29 (base + 116) (.LW .x6 .x12 60) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 112) + 8  = base + 120 from by bv_addr]; exact
        hcode.fetch 30 (base + 120) (.SW .x12 .x6 28) (by decide) (by decide) (by bv_addr))
    (by rw [show (base + 112) + 12 = base + 124 from by bv_addr]; exact
        hcode.fetch 31 (base + 124) (.SW .x12 .x7 60) (by decide) (by decide) (by bv_addr))
    (by simp only [signExtend12_28]; exact hv28)
    (by simp only [signExtend12_60]; exact hv60)
  simp only [signExtend12_28, signExtend12_60] at L7
  rw [show (base + 112) + 16 = base + 128 from by bv_addr] at L7
  have L7f := cpsTriple_frame_left code (base + 112) (base + 128) _ _
    ((sp ↦ₘ b0) ** ((sp + 4) ↦ₘ b1) ** ((sp + 8) ↦ₘ b2) ** ((sp + 12) ↦ₘ b3) **
     ((sp + 16) ↦ₘ b4) ** ((sp + 20) ↦ₘ b5) ** ((sp + 24) ↦ₘ b6) **
     ((sp + 32) ↦ₘ a0) ** ((sp + 36) ↦ₘ a1) ** ((sp + 40) ↦ₘ a2) ** ((sp + 44) ↦ₘ a3) **
     ((sp + 48) ↦ₘ a4) ** ((sp + 52) ↦ₘ a5) ** ((sp + 56) ↦ₘ a6))
    (by pcFree) L7
  -- Compose all 8 limbs
  clear hv0 hv4 hv8 hv12 hv16 hv20 hv24 hv28 hv32 hv36 hv40 hv44 hv48 hv52 hv56 hv60
  clear L0 L1 L2 L3 L4 L5 L6 L7
  have c01 := cpsTriple_seq_with_perm code base (base + 16) (base + 32) _ _ _ _
    (fun _ hp => by xperm_hyp hp) L0f L1f; clear L0f L1f
  have c02 := cpsTriple_seq_with_perm code base (base + 32) (base + 48) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c01 L2f; clear c01 L2f
  have c03 := cpsTriple_seq_with_perm code base (base + 48) (base + 64) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c02 L3f; clear c02 L3f
  have c04 := cpsTriple_seq_with_perm code base (base + 64) (base + 80) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c03 L4f; clear c03 L4f
  have c05 := cpsTriple_seq_with_perm code base (base + 80) (base + 96) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c04 L5f; clear c04 L5f
  have c06 := cpsTriple_seq_with_perm code base (base + 96) (base + 112) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c05 L6f; clear c05 L6f
  have cfull := cpsTriple_seq_with_perm code base (base + 112) (base + 128) _ _ _ _
    (fun _ hp => by xperm_hyp hp) c06 L7f; clear c06 L7f
  exact cpsTriple_consequence code base (base + 128) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) cfull

theorem evm_swap1_stack_spec (code : CodeMem) (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word) (rest : List EvmWord)
    (hcode : ProgramAt code base evm_swap1)
    (hvalid : ValidMemRange sp 16) :
    cpsTriple code base (base + 128)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b ** evmStackIs (sp + 64) rest)
      ((.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ a.getLimb 7) ** (.x6 ↦ᵣ b.getLimb 7) **
       evmWordIs sp b ** evmWordIs (sp + 32) a ** evmStackIs (sp + 64) rest) := by
  simp only [evmWordIs, sepConj_assoc']
  have h32_4  : sp + 32 + 4  = sp + 36 := by bv_addr
  have h32_8  : sp + 32 + 8  = sp + 40 := by bv_addr
  have h32_12 : sp + 32 + 12 = sp + 44 := by bv_addr
  have h32_16 : sp + 32 + 16 = sp + 48 := by bv_addr
  have h32_20 : sp + 32 + 20 = sp + 52 := by bv_addr
  have h32_24 : sp + 32 + 24 = sp + 56 := by bv_addr
  have h32_28 : sp + 32 + 28 = sp + 60 := by bv_addr
  simp only [h32_4, h32_8, h32_12, h32_16, h32_20, h32_24, h32_28]
  have base_spec := evm_swap1_spec code sp base
    (a.getLimb 0) (a.getLimb 1) (a.getLimb 2) (a.getLimb 3)
    (a.getLimb 4) (a.getLimb 5) (a.getLimb 6) (a.getLimb 7)
    (b.getLimb 0) (b.getLimb 1) (b.getLimb 2) (b.getLimb 3)
    (b.getLimb 4) (b.getLimb 5) (b.getLimb 6) (b.getLimb 7)
    v7 v6 hcode hvalid
  have framed := cpsTriple_frame_left code base (base + 128) _ _
    (evmStackIs (sp + 64) rest) (pcFree_evmStackIs (sp + 64) rest) base_spec
  exact cpsTriple_consequence code base (base + 128) _ _ _ _
    (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp) framed

end RiscVMacroAsm
