/-
  RiscVMacroAsm.Execution

  Branch-aware instruction execution, code memory, and step-based execution.

  This module provides an alternative execution model that handles branch and
  jump instructions with proper PC semantics (as opposed to the straight-line
  execInstr which always advances PC by 4).

  Key components:
  - execInstrBr: per-instruction PC control (branches change PC by offset)
  - CodeMem: maps addresses to instructions
  - loadProgram: loads a program into code memory at a base address
  - step / stepN: single-step and multi-step execution over code memory
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.Program

namespace RiscVMacroAsm

-- ============================================================================
-- Branch-aware instruction execution
-- ============================================================================

/-- Execute a single instruction with full PC control.
    Non-branch instructions: PC += 4.
    Branch instructions: PC += offset (taken) or PC += 4 (not taken).
    JAL: rd := PC + 4, PC += offset.
    JALR: rd := PC + 4, PC := (rs1 + sext(offset)) & ~1. -/
def execInstrBr (s : MachineState) (i : Instr) : MachineState :=
  match i with
  -- RV32I ALU register-register
  | .ADD rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)
  | .SUB rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)
  | .SLL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 <<< shamt)).setPC (s.pc + 4)
  | .SRL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 >>> shamt)).setPC (s.pc + 4)
  | .SRA rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt)).setPC (s.pc + 4)
  | .AND rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4)
  | .OR rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)
  | .XOR rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 ^^^ s.getReg rs2)).setPC (s.pc + 4)
  | .SLT rd rs1 rs2 =>
      (s.setReg rd (if BitVec.slt (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4)
  | .SLTU rd rs1 rs2 =>
      (s.setReg rd (if BitVec.ult (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4)
  -- RV32I ALU immediate
  | .ADDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)
  | .ANDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)
  | .ORI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 ||| signExtend12 imm)).setPC (s.pc + 4)
  | .XORI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)
  | .SLTI rd rs1 imm =>
      (s.setReg rd (if BitVec.slt (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4)
  | .SLTIU rd rs1 imm =>
      (s.setReg rd (if BitVec.ult (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4)
  | .SLLI rd rs1 shamt =>
      (s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)
  | .SRLI rd rs1 shamt =>
      (s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)
  | .SRAI rd rs1 shamt =>
      (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt.toNat)).setPC (s.pc + 4)
  -- RV32I upper immediate
  | .LUI rd imm =>
      let val : Word := imm.zeroExtend 32 <<< 12
      (s.setReg rd val).setPC (s.pc + 4)
  | .AUIPC rd imm =>
      let val : Word := s.pc + (imm.zeroExtend 32 <<< 12)
      (s.setReg rd val).setPC (s.pc + 4)
  -- RV32I word memory
  | .LW rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd (s.getMem addr)).setPC (s.pc + 4)
  | .SW rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setMem addr (s.getReg rs2)).setPC (s.pc + 4)
  -- RV32I sub-word memory
  | .LB rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).signExtend 32)).setPC (s.pc + 4)
  | .LH rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).signExtend 32)).setPC (s.pc + 4)
  | .LBU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getByte addr).zeroExtend 32)).setPC (s.pc + 4)
  | .LHU rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd ((s.getHalfword addr).zeroExtend 32)).setPC (s.pc + 4)
  | .SB rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setByte addr ((s.getReg rs2).truncate 8)).setPC (s.pc + 4)
  | .SH rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setHalfword addr ((s.getReg rs2).truncate 16)).setPC (s.pc + 4)
  -- RV32I branches
  | .BEQ rs1 rs2 offset =>
      if s.getReg rs1 == s.getReg rs2 then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BNE rs1 rs2 offset =>
      if s.getReg rs1 != s.getReg rs2 then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BLT rs1 rs2 offset =>
      if BitVec.slt (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BGE rs1 rs2 offset =>
      if ¬ BitVec.slt (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BLTU rs1 rs2 offset =>
      if BitVec.ult (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  | .BGEU rs1 rs2 offset =>
      if ¬ BitVec.ult (s.getReg rs1) (s.getReg rs2) then
        s.setPC (s.pc + signExtend13 offset)
      else
        s.setPC (s.pc + 4)
  -- RV32I jumps
  | .JAL rd offset =>
      (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)
  | .JALR rd rs1 offset =>
      (s.setReg rd (s.pc + 4)).setPC ((s.getReg rs1 + signExtend12 offset) &&& ~~~1#32)
  -- RV32I pseudo-instructions
  | .MV rd rs =>
      (s.setReg rd (s.getReg rs)).setPC (s.pc + 4)
  | .LI rd imm =>
      (s.setReg rd imm).setPC (s.pc + 4)
  | .NOP =>
      s.setPC (s.pc + 4)
  -- RV32I system
  | .ECALL =>
      s.setPC (s.pc + 4)
  | .FENCE =>
      s.setPC (s.pc + 4)
  | .EBREAK =>
      s.setPC (s.pc + 4)
  -- RV32M multiply
  | .MUL rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 * s.getReg rs2)).setPC (s.pc + 4)
  | .MULH rd rs1 rs2 =>
      (s.setReg rd (rv32_mulh (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHSU rd rs1 rs2 =>
      (s.setReg rd (rv32_mulhsu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .MULHU rd rs1 rs2 =>
      (s.setReg rd (rv32_mulhu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  -- RV32M divide
  | .DIV rd rs1 rs2 =>
      (s.setReg rd (rv32_div (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .DIVU rd rs1 rs2 =>
      (s.setReg rd (rv32_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REM rd rs1 rs2 =>
      (s.setReg rd (rv32_rem (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)
  | .REMU rd rs1 rs2 =>
      (s.setReg rd (rv32_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)

/-- For non-branch instructions, execInstrBr agrees with execInstr
    (both advance PC by 4 and compute the same state update). -/
theorem execInstrBr_eq_execInstr (s : MachineState) (i : Instr)
    (h : i.isBranch = false) : execInstrBr s i = execInstr s i := by
  cases i <;> simp_all [execInstrBr, execInstr, Instr.isBranch,
    MachineState.pc_setReg, MachineState.pc_setMem,
    MachineState.pc_setByte, MachineState.pc_setHalfword]

@[simp] theorem committed_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).committed = s.committed := by
  cases i <;> simp [execInstrBr, MachineState.committed_setPC,
    MachineState.committed_setReg, MachineState.committed_setMem,
    MachineState.committed_setByte, MachineState.committed_setHalfword]
  all_goals split <;> simp [MachineState.committed_setPC]

@[simp] theorem publicValues_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).publicValues = s.publicValues := by
  cases i <;> simp [execInstrBr, MachineState.publicValues_setPC,
    MachineState.publicValues_setReg, MachineState.publicValues_setMem,
    MachineState.publicValues_setByte, MachineState.publicValues_setHalfword]
  all_goals split <;> simp [MachineState.publicValues_setPC]

@[simp] theorem publicInput_execInstrBr (s : MachineState) (i : Instr) :
    (execInstrBr s i).publicInput = s.publicInput := by
  cases i <;> simp [execInstrBr, MachineState.publicInput_setPC,
    MachineState.publicInput_setReg, MachineState.publicInput_setMem,
    MachineState.publicInput_setByte, MachineState.publicInput_setHalfword]
  all_goals split <;> simp [MachineState.publicInput_setPC]

-- ============================================================================
-- Code memory
-- ============================================================================

/-- Code memory: maps addresses to instructions. -/
def CodeMem := Addr → Option Instr

/-- Load a program into code memory at a base address.
    Instruction k is at address base + 4*k. -/
def loadProgram (base : Addr) (prog : List Instr) : CodeMem :=
  fun addr =>
    let offset := addr - base
    let idx := offset.toNat / 4
    if offset.toNat % 4 == 0 ∧ idx < prog.length then
      prog[idx]?
    else
      none

-- ============================================================================
-- Step-based execution
-- ============================================================================

/-- Single step: fetch instruction at PC, execute with branch-aware semantics.
    Returns none if no instruction at PC (stuck/halted), or if the instruction
    is ECALL with t0 = 0 (HALT syscall, following SP1 convention).
    LW/SW trap (return none) on misaligned or out-of-range addresses.
    LB/LBU/SB trap on out-of-range addresses.
    LH/LHU/SH trap on misaligned or out-of-range addresses.
    EBREAK traps (returns none).
    WRITE (t0 = 0x02) to fd 13 appends words from memory to public values.
    COMMIT (t0 = 0x10) appends (a0, a1) to committed outputs.
    Other ECALLs continue execution. -/
def step (code : CodeMem) (s : MachineState) : Option MachineState :=
  match code s.pc with
  | none => none
  | some (.LW rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.LW rd rs1 offset))
    else none  -- trap: invalid memory access
  | some (.SW rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidMemAccess addr then
      some (execInstrBr s (.SW rs1 rs2 offset))
    else none  -- trap: invalid memory access
  | some (.LB rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.LB rd rs1 offset))
    else none
  | some (.LBU rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.LBU rd rs1 offset))
    else none
  | some (.LH rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.LH rd rs1 offset))
    else none
  | some (.LHU rd rs1 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.LHU rd rs1 offset))
    else none
  | some (.SB rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidByteAccess addr then
      some (execInstrBr s (.SB rs1 rs2 offset))
    else none
  | some (.SH rs1 rs2 offset) =>
    let addr := s.getReg rs1 + signExtend12 offset
    if isValidHalfwordAccess addr then
      some (execInstrBr s (.SH rs1 rs2 offset))
    else none
  | some .EBREAK => none  -- trap: breakpoint
  | some .ECALL =>
    let t0 := s.getReg .x5
    if t0 == (0 : Word) then none  -- HALT syscall (SP1: t0 = 0)
    else if t0 == (0x02 : Word) then  -- WRITE syscall
      let fd := s.getReg .x10
      let buf := s.getReg .x11
      let nbytes := s.getReg .x12
      if fd == (13 : Word) then
        let nwords := nbytes.toNat / 4
        let words := s.readWords buf nwords
        some ((s.appendPublicValues words).setPC (s.pc + 4))
      else
        some (s.setPC (s.pc + 4))  -- other fd: continue
    else if t0 == (0x10 : Word) then  -- COMMIT syscall
      some ((s.appendCommit (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4))
    else if t0 == (0xF0 : Word) then  -- HINT_LEN syscall
      let len := BitVec.ofNat 32 (4 * s.publicInput.length)
      some ((s.setReg .x10 len).setPC (s.pc + 4))
    else if t0 == (0xF1 : Word) then  -- HINT_READ syscall
      let addr := s.getReg .x10
      let nbytes := s.getReg .x11
      let nwords := nbytes.toNat / 4
      if nwords ≤ s.publicInput.length then
        let words := s.publicInput.take nwords
        let s' := { s with publicInput := s.publicInput.drop nwords }
        some ((s'.writeWords addr words).setPC (s.pc + 4))
      else
        none  -- trap: not enough input (SP1: panic)
    else some (execInstrBr s .ECALL)  -- other ecalls continue
  | some i => some (execInstrBr s i)

/-- step for non-ECALL, non-EBREAK, non-memory instructions. -/
@[simp] theorem step_non_ecall_non_mem (code : CodeMem) (s : MachineState) (i : Instr)
    (hfetch : code s.pc = some i) (hne : i ≠ .ECALL) (hnb : i ≠ .EBREAK)
    (hnm : i.isMemAccess = false) :
    step code s = some (execInstrBr s i) := by
  unfold step; rw [hfetch]; cases i <;> simp_all [Instr.isMemAccess]

/-- step for LW with valid memory access. -/
theorem step_lw (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LW rd rs1 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.LW rd rs1 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SW with valid memory access. -/
theorem step_sw (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.SW rs1 rs2 offset)) := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LW with invalid memory access (trap). -/
theorem step_lw_trap (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LW rd rs1 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SW with invalid memory access (trap). -/
theorem step_sw_trap (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SW rs1 rs2 offset))
    (hinvalid : isValidMemAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidMemAccess, isValidMemAddr, isAligned4, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LB with valid byte access. -/
theorem step_lb (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LB rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.LB rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LB with invalid byte access (trap). -/
theorem step_lb_trap (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LB rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LBU with valid byte access. -/
theorem step_lbu (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LBU rd rs1 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.LBU rd rs1 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LBU with invalid byte access (trap). -/
theorem step_lbu_trap (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LBU rd rs1 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LH with valid halfword access. -/
theorem step_lh (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LH rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.LH rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LH with invalid halfword access (trap). -/
theorem step_lh_trap (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LH rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for LHU with valid halfword access. -/
theorem step_lhu (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LHU rd rs1 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.LHU rd rs1 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for LHU with invalid halfword access (trap). -/
theorem step_lhu_trap (code : CodeMem) (s : MachineState) (rd rs1 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.LHU rd rs1 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SB with valid byte access. -/
theorem step_sb (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SB rs1 rs2 offset))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.SB rs1 rs2 offset)) := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SB with invalid byte access (trap). -/
theorem step_sb_trap (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SB rs1 rs2 offset))
    (hinvalid : isValidByteAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidByteAccess, isValidMemAddr, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for SH with valid halfword access. -/
theorem step_sh (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SH rs1 rs2 offset))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = true) :
    step code s = some (execInstrBr s (.SH rs1 rs2 offset)) := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hvalid ⊢
  omega

/-- step for SH with invalid halfword access (trap). -/
theorem step_sh_trap (code : CodeMem) (s : MachineState) (rs1 rs2 : Reg) (offset : BitVec 12)
    (hfetch : code s.pc = some (.SH rs1 rs2 offset))
    (hinvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 offset) = false) :
    step code s = none := by
  simp [step, hfetch, isValidHalfwordAccess, isValidMemAddr, isAligned2, SP1_MEM_START, SP1_MEM_END] at hinvalid ⊢
  omega

/-- step for EBREAK (always traps). -/
theorem step_ebreak (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .EBREAK) :
    step code s = none := by
  simp [step, hfetch]

theorem step_ecall_halt (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL) (ht0 : s.getReg .x5 = 0) :
    step code s = none := by
  simp [step, hfetch, ht0]

theorem step_ecall_continue (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 ≠ 0)
    (ht0_nw : s.getReg .x5 ≠ (0x02 : Word))
    (ht0_nc : s.getReg .x5 ≠ (0x10 : Word))
    (ht0_nhl : s.getReg .x5 ≠ (0xF0 : Word))
    (ht0_nhr : s.getReg .x5 ≠ (0xF1 : Word)) :
    step code s = some (execInstrBr s .ECALL) := by
  simp only [step, hfetch, beq_iff_eq, ht0, ht0_nw, ht0_nc, ht0_nhl, ht0_nhr, ↓reduceIte]

/-- COMMIT syscall (SP1 convention: t0 = 0x10) appends (a0, a1) to committed outputs. -/
theorem step_ecall_commit (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x10) :
    step code s =
      some ((s.appendCommit (s.getReg .x10) (s.getReg .x11)).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0]

/-- WRITE syscall to FD_PUBLIC_VALUES (t0 = 0x02, fd = 13) appends words from memory. -/
theorem step_ecall_write_public (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x02)
    (hfd : s.getReg .x10 = 13) :
    step code s =
      some ((s.appendPublicValues (s.readWords (s.getReg .x11) ((s.getReg .x12).toNat / 4))).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, hfd]

/-- WRITE syscall to non-public-values fd (t0 = 0x02, fd ≠ 13) just advances PC. -/
theorem step_ecall_write_other (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0x02)
    (hfd : s.getReg .x10 ≠ (13 : Word)) :
    step code s = some (s.setPC (s.pc + 4)) := by
  simp only [step, hfetch, ht0, beq_iff_eq, hfd, ite_false]
  simp (config := { decide := true })

/-- HINT_LEN syscall (SP1 convention: t0 = 0xF0) returns 4 * publicInput.length in a0. -/
theorem step_ecall_hint_len (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF0) :
    step code s =
      some ((s.setReg .x10 (BitVec.ofNat 32 (4 * s.publicInput.length))).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0]

/-- HINT_READ syscall (SP1 convention: t0 = 0xF1) reads words from publicInput into memory. -/
theorem step_ecall_hint_read (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF1)
    (hsuff : (s.getReg .x11).toNat / 4 ≤ s.publicInput.length) :
    step code s =
      let nwords := (s.getReg .x11).toNat / 4
      let words := s.publicInput.take nwords
      let s' := { s with publicInput := s.publicInput.drop nwords }
      some ((s'.writeWords (s.getReg .x10) words).setPC (s.pc + 4)) := by
  simp [step, hfetch, ht0, hsuff]

/-- HINT_READ syscall traps when not enough input is available. -/
theorem step_ecall_hint_read_trap (code : CodeMem) (s : MachineState)
    (hfetch : code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = BitVec.ofNat 32 0xF1)
    (hinsuff : ¬ ((s.getReg .x11).toNat / 4 ≤ s.publicInput.length)) :
    step code s = none := by
  simp [step, hfetch, ht0, hinsuff]

/-- Multi-step execution (n steps). -/
def stepN : Nat → CodeMem → MachineState → Option MachineState
  | 0,     _,    s => some s
  | n + 1, code, s => (step code s).bind (stepN n code ·)

-- ============================================================================
-- stepN lemmas
-- ============================================================================

@[simp]
theorem stepN_zero (code : CodeMem) (s : MachineState) :
    stepN 0 code s = some s := rfl

@[simp]
theorem stepN_succ (code : CodeMem) (s : MachineState) (n : Nat) :
    stepN (n + 1) code s = (step code s).bind (stepN n code ·) := rfl

theorem stepN_one (code : CodeMem) (s : MachineState) :
    stepN 1 code s = step code s := by
  simp [stepN, Option.bind]
  cases step code s <;> simp

/-- Composing step counts: n+m steps = n steps then m steps. -/
theorem stepN_add (n m : Nat) (code : CodeMem) (s : MachineState) :
    stepN (n + m) code s = (stepN n code s).bind (stepN m code ·) := by
  induction n generalizing s with
  | zero => simp [Option.bind]
  | succ k ih =>
    simp only [Nat.succ_add, stepN_succ]
    cases h : step code s with
    | none => simp [Option.bind]
    | some s' => simp [Option.bind, ih]

/-- If stepN n succeeds and then stepN m succeeds, stepN (n+m) gives the same result. -/
theorem stepN_add_eq (n m : Nat) (code : CodeMem) (s s' s'' : MachineState)
    (h1 : stepN n code s = some s')
    (h2 : stepN m code s' = some s'') :
    stepN (n + m) code s = some s'' := by
  rw [stepN_add, h1, Option.bind]
  exact h2

end RiscVMacroAsm
