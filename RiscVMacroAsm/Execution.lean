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
    JAL: rd := PC + 4, PC += offset. -/
def execInstrBr (s : MachineState) (i : Instr) : MachineState :=
  match i with
  | .ADD rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)
  | .ADDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)
  | .SUB rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)
  | .SLL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 <<< shamt)).setPC (s.pc + 4)
  | .SLLI rd rs1 shamt =>
      (s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)
  | .SRL rd rs1 rs2 =>
      let shamt := (s.getReg rs2).toNat % 32
      (s.setReg rd (s.getReg rs1 >>> shamt)).setPC (s.pc + 4)
  | .AND rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4)
  | .ANDI rd rs1 imm =>
      (s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)
  | .OR rd rs1 rs2 =>
      (s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)
  | .LW rd rs1 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setReg rd (s.getMem addr)).setPC (s.pc + 4)
  | .SW rs1 rs2 offset =>
      let addr := s.getReg rs1 + signExtend12 offset
      (s.setMem addr (s.getReg rs2)).setPC (s.pc + 4)
  | .LUI rd imm =>
      let val : Word := imm.zeroExtend 32 <<< 12
      (s.setReg rd val).setPC (s.pc + 4)
  | .MV rd rs =>
      (s.setReg rd (s.getReg rs)).setPC (s.pc + 4)
  | .LI rd imm =>
      (s.setReg rd imm).setPC (s.pc + 4)
  | .NOP =>
      s.setPC (s.pc + 4)
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
  | .JAL rd offset =>
      (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 offset)

/-- For non-branch instructions, execInstrBr agrees with execInstr
    (both advance PC by 4 and compute the same state update). -/
theorem execInstrBr_eq_execInstr (s : MachineState) (i : Instr)
    (h : i.isBranch = false) : execInstrBr s i = execInstr s i := by
  cases i <;> simp_all [execInstrBr, execInstr, Instr.isBranch,
    MachineState.pc_setReg, MachineState.pc_setMem]

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
    Returns none if no instruction at PC (stuck/halted). -/
def step (code : CodeMem) (s : MachineState) : Option MachineState :=
  (code s.pc).map (execInstrBr s)

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
