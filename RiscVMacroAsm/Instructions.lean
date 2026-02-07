/-
  RiscVMacroAsm.Instructions

  RISC-V instruction definitions and their semantics.
  We model a small subset of RV32I instructions.
-/

import RiscVMacroAsm.Basic

namespace RiscVMacroAsm

-- ============================================================================
-- Instructions (a small RV32I subset)
-- ============================================================================

/-- A single RISC-V instruction. -/
inductive Instr where
  /-- ADD rd, rs1, rs2 : rd := rs1 + rs2 -/
  | ADD  (rd rs1 rs2 : Reg)
  /-- ADDI rd, rs1, imm : rd := rs1 + imm -/
  | ADDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- SUB rd, rs1, rs2 : rd := rs1 - rs2 -/
  | SUB  (rd rs1 rs2 : Reg)
  /-- SLL rd, rs1, rs2 : rd := rs1 << rs2[4:0] (shift left logical) -/
  | SLL  (rd rs1 rs2 : Reg)
  /-- SLLI rd, rs1, shamt : rd := rs1 << shamt -/
  | SLLI (rd rs1 : Reg) (shamt : BitVec 5)
  /-- SRL rd, rs1, rs2 : rd := rs1 >>> rs2[4:0] (shift right logical) -/
  | SRL  (rd rs1 rs2 : Reg)
  /-- AND rd, rs1, rs2 : rd := rs1 &&& rs2 -/
  | AND  (rd rs1 rs2 : Reg)
  /-- ANDI rd, rs1, imm : rd := rs1 &&& sext(imm) -/
  | ANDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- OR rd, rs1, rs2 : rd := rs1 ||| rs2 -/
  | OR   (rd rs1 rs2 : Reg)
  /-- LW rd, offset(rs1) : rd := mem[rs1 + sext(offset)] -/
  | LW   (rd rs1 : Reg) (offset : BitVec 12)
  /-- SW rs2, offset(rs1) : mem[rs1 + sext(offset)] := rs2 -/
  | SW   (rs1 rs2 : Reg) (offset : BitVec 12)
  /-- LUI rd, imm : rd := imm << 12 -/
  | LUI  (rd : Reg) (imm : BitVec 20)
  /-- MV rd, rs (pseudo: ADDI rd, rs, 0) -/
  | MV   (rd rs : Reg)
  /-- LI rd, imm (pseudo: load immediate) -/
  | LI   (rd : Reg) (imm : Word)
  /-- NOP (pseudo: ADDI x0, x0, 0) -/
  | NOP
  /-- BEQ rs1, rs2, offset : branch if rs1 = rs2 (B-type, byte offset) -/
  | BEQ  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BNE rs1, rs2, offset : branch if rs1 ≠ rs2 (B-type, byte offset) -/
  | BNE  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- JAL rd, offset : jump and link (J-type, byte offset) -/
  | JAL  (rd : Reg) (offset : BitVec 21)
  /-- ECALL: environment call (syscall ID in t0/x5, args in a0-a2).
      Following SP1 convention, t0 = 0 signals HALT with exit code in a0. -/
  | ECALL
  deriving Repr

-- ============================================================================
-- Instruction Semantics
-- ============================================================================

/-- Is this instruction a branch or jump? -/
def Instr.isBranch : Instr → Bool
  | .BEQ _ _ _ => true
  | .BNE _ _ _ => true
  | .JAL _ _   => true
  | _          => false

/-- Sign-extend a 12-bit immediate to 32 bits. -/
def signExtend12 (imm : BitVec 12) : Word :=
  imm.signExtend 32

/-- Sign-extend a 13-bit branch offset to 32 bits. -/
def signExtend13 (imm : BitVec 13) : Word :=
  imm.signExtend 32

/-- Sign-extend a 21-bit jump offset to 32 bits. -/
def signExtend21 (imm : BitVec 21) : Word :=
  imm.signExtend 32

/-- Execute a single instruction, returning the new state.
    The PC is advanced by 4 (one instruction width). -/
def execInstr (s : MachineState) (i : Instr) : MachineState :=
  let s' := match i with
    | .ADD rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 + s.getReg rs2)
    | .ADDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 + signExtend12 imm)
    | .SUB rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 - s.getReg rs2)
    | .SLL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (s.getReg rs1 <<< shamt)
    | .SLLI rd rs1 shamt =>
        s.setReg rd (s.getReg rs1 <<< shamt.toNat)
    | .SRL rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (s.getReg rs1 >>> shamt)
    | .AND rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 &&& s.getReg rs2)
    | .ANDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 &&& signExtend12 imm)
    | .OR rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 ||| s.getReg rs2)
    | .LW rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd (s.getMem addr)
    | .SW rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setMem addr (s.getReg rs2)
    | .LUI rd imm =>
        let val : Word := imm.zeroExtend 32 <<< 12
        s.setReg rd val
    | .MV rd rs =>
        s.setReg rd (s.getReg rs)
    | .LI rd imm =>
        s.setReg rd imm
    | .NOP => s
    -- Branch/jump instructions are treated as NOP in list-based execution.
    -- For proper branch semantics, use execInstrBr + step-based execution.
    | .BEQ _ _ _ | .BNE _ _ _ | .JAL _ _ | .ECALL => s
  s'.setPC (s'.pc + 4#32)

end RiscVMacroAsm
