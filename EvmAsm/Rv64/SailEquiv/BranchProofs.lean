/-
  EvmAsm.Rv64.SailEquiv.BranchProofs

  Per-instruction equivalence theorems for branch and jump instructions:
  BEQ, BNE, BLT, BGE, BLTU, BGEU, JAL, JALR.

  Branches don't write general registers — they only update nextPC. Since
  StateRel doesn't track PC or nextPC, branches trivially preserve StateRel
  for registers and memory.

  JAL/JALR additionally write a link register (rd := next_pc).
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 8000000

-- ============================================================================
-- Helper lemmas for branch proofs
-- ============================================================================

private theorem sign_extend_13_eq (imm : BitVec 13) :
    sign_extend (m := 64) imm = signExtend13 imm := by
  unfold sign_extend signExtend13 Sail.BitVec.signExtend; rfl

/-- Writing Register.nextPC preserves StateRel (nextPC is not in the tracked register set). -/
theorem stateRel_nextPC (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (v : BitVec 64) :
    StateRel s_rv { s_sail with regs := s_sail.regs.insert Register.nextPC v } :=
  ⟨fun r => by
    have ha := hrel.reg_agree r
    cases r <;> simp only [sailRegVal, Std.ExtDHashMap.get?_insert,
      show (Register.nextPC == Register.x1) = false from by decide,
      show (Register.nextPC == Register.x2) = false from by decide,
      show (Register.nextPC == Register.x5) = false from by decide,
      show (Register.nextPC == Register.x6) = false from by decide,
      show (Register.nextPC == Register.x7) = false from by decide,
      show (Register.nextPC == Register.x10) = false from by decide,
      show (Register.nextPC == Register.x11) = false from by decide,
      show (Register.nextPC == Register.x12) = false from by decide,
      ite_false] at ha ⊢ <;> exact ha,
   fun a => hrel.mem_agree a⟩

-- Comparison operator equivalences (definitional: SAIL and Lean use the same operations)
private theorem slt_equiv (a b : BitVec 64) : zopz0zI_s a b = BitVec.slt a b := by
  unfold zopz0zI_s BitVec.slt; rfl
private theorem sge_equiv (a b : BitVec 64) : zopz0zKzJ_s a b = !zopz0zI_s a b := by
  unfold zopz0zKzJ_s zopz0zI_s
  by_cases h : a.toInt < b.toInt <;>
    simp [h, show ¬(a.toInt < b.toInt) → a.toInt ≥ b.toInt from by omega]
private theorem ult_equiv (a b : BitVec 64) : zopz0zI_u a b = BitVec.ult a b := by
  unfold zopz0zI_u BitVec.ult BitVec.toNatInt
  simp [BEq.beq, decide_eq_decide, Int.ofNat_lt]
private theorem uge_equiv (a b : BitVec 64) : zopz0zKzJ_u a b = !zopz0zI_u a b := by
  unfold zopz0zKzJ_u zopz0zI_u BitVec.toNatInt
  by_cases h : (↑a.toNat : Int) < (↑b.toNat : Int) <;> (simp [h]; omega)

-- ============================================================================
-- Common branch proof tactic
-- ============================================================================

-- The proof pattern for all 6 conditional branches is identical:
-- 1. Unfold execute_BTYPE, apply monad lemmas
-- 2. Case-split on branch condition
-- 3. Taken: apply jump_to, StateRel preserved via stateRel_nextPC
-- 4. Not taken: pure RETIRE_SUCCESS, StateRel trivially preserved

-- ============================================================================
-- Conditional branches (BEQ, BNE, BLT, BGE, BLTU, BGEU)
-- ============================================================================

theorem beq_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BEQ) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BEQ rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  by_cases h : s_rv.getReg rs1 == s_rv.getReg rs2
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bne_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BNE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BNE rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure]
  by_cases h : s_rv.getReg rs1 != s_rv.getReg rs2
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem blt_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLT) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BLT rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure, slt_equiv]
  by_cases h : BitVec.slt (s_rv.getReg rs1) (s_rv.getReg rs2)
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bge_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGE) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BGE rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    sge_equiv, slt_equiv]
  by_cases h : BitVec.slt (s_rv.getReg rs1) (s_rv.getReg rs2)
  · -- slt = true, so !slt = false → not taken
    simp only [h, Bool.not_true, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, show ¬¬BitVec.slt _ _ from fun h' => absurd h h']; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, show ¬¬BitVec.slt _ _ from fun h' => absurd h h']; exact hrel.mem_agree a⟩⟩
  · -- slt = false, so !slt = true → taken
    simp only [show BitVec.slt (s_rv.getReg rs1) (s_rv.getReg rs2) = false from by simp [h],
      Bool.not_false, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩

theorem bltu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BLTU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BLTU rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure, ult_equiv]
  by_cases h : BitVec.ult (s_rv.getReg rs1) (s_rv.getReg rs2)
  · simp only [h, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩
  · simp only [h, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩⟩

theorem bgeu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rs1 rs2 : Reg) (offset : BitVec 13)
    (h_align : (s_rv.pc + signExtend13 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_BTYPE offset (regToRegidx rs2) (regToRegidx rs1) bop.BGEU) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.BGEU rs1 rs2 offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_BTYPE
  simp only [runSail_bind, runSail_rX_bits_of_stateRel s_rv s_sail hrel, runSail_pure,
    uge_equiv, ult_equiv]
  by_cases h : BitVec.ult (s_rv.getReg rs1) (s_rv.getReg rs2)
  · -- ult = true, so !ult = false → not taken
    simp only [h, Bool.not_true, ite_false]
    exact ⟨_, rfl,
      ⟨fun r => by simp [execInstrBr, show ¬¬BitVec.ult _ _ from fun h' => absurd h h']; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, show ¬¬BitVec.ult _ _ from fun h' => absurd h h']; exact hrel.mem_agree a⟩⟩
  · -- ult = false, so !ult = true → taken
    simp only [show BitVec.ult (s_rv.getReg rs1) (s_rv.getReg rs2) = false from by simp [h],
      Bool.not_false, ite_true, runSail_bind,
      runSail_readReg_PC s_sail s_rv.pc h_pc, runSail_pure, sign_extend_13_eq]
    rw [runSail_jump_to _ _ misa_val h_align h_misa]
    exact ⟨_, rfl, stateRel_nextPC _ _
      ⟨fun r => by simp [execInstrBr, h]; exact hrel.reg_agree r,
       fun a => by simp [execInstrBr, h]; exact hrel.mem_agree a⟩ _⟩

-- ============================================================================
-- Unconditional jumps (JAL, JALR)
-- ============================================================================

private theorem sign_extend_21_eq (imm : BitVec 21) :
    sign_extend (m := 64) imm = signExtend21 imm := by
  unfold sign_extend signExtend21 Sail.BitVec.signExtend; rfl

theorem jal_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (h_nextpc : s_sail.regs.get? Register.nextPC = some (s_rv.pc + 4))
    (h_misa : ∃ v, s_sail.regs.get? Register.misa = some v)
    (rd : Reg) (offset : BitVec 21)
    (h_align : (s_rv.pc + signExtend21 offset) &&& 3 = 0) :
    ∃ s_sail',
      runSail (execute_JAL offset (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.JAL rd offset)) s_sail' := by
  obtain ⟨misa_val, h_misa⟩ := h_misa
  unfold execute_JAL
  simp only [runSail_bind,
    runSail_get_next_pc s_sail (s_rv.pc + 4) h_nextpc,
    runSail_readReg_PC s_sail s_rv.pc h_pc,
    sign_extend_21_eq]
  rw [runSail_jump_to _ _ misa_val h_align h_misa]
  simp only [RETIRE_SUCCESS, runSail_bind, runSail_pure]
  cases rd <;>
    simp only [regToRegidx,
      runSail_wX_bits_x0, runSail_wX_bits_x1, runSail_wX_bits_x2,
      runSail_wX_bits_x5, runSail_wX_bits_x6, runSail_wX_bits_x7,
      runSail_wX_bits_x10, runSail_wX_bits_x11, runSail_wX_bits_x12]
  all_goals first
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x0 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x1 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x2 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x5 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x6 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x7 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x10 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x11 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩
    | exact ⟨_, rfl, ⟨fun r => by simpa [execInstrBr, MachineState.setPC] using reg_agree_after_insert _ _ (stateRel_nextPC _ _ hrel _) .x12 _ r,
        fun a => by simpa [execInstrBr, MachineState.setPC] using hrel.mem_agree a⟩⟩

theorem jalr_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail)
    (h_pc : s_sail.regs.get? Register.PC = some s_rv.pc)
    (rd rs1 : Reg) (offset : BitVec 12) :
    ∃ s_sail',
      runSail (execute_JALR offset (regToRegidx rs1) (regToRegidx rd)) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.JALR rd rs1 offset)) s_sail' := by
  sorry

end EvmAsm.Rv64.SailEquiv
