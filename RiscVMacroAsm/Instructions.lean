/-
  RiscVMacroAsm.Instructions

  RISC-V instruction definitions and their semantics.
  We model the full RV32IM instruction set (base + M extension).
-/

import RiscVMacroAsm.Basic

namespace RiscVMacroAsm

-- ============================================================================
-- Instructions (RV32IM)
-- ============================================================================

/-- A single RISC-V instruction. -/
inductive Instr where
  -- RV32I ALU register-register
  /-- ADD rd, rs1, rs2 : rd := rs1 + rs2 -/
  | ADD  (rd rs1 rs2 : Reg)
  /-- SUB rd, rs1, rs2 : rd := rs1 - rs2 -/
  | SUB  (rd rs1 rs2 : Reg)
  /-- SLL rd, rs1, rs2 : rd := rs1 << rs2[4:0] (shift left logical) -/
  | SLL  (rd rs1 rs2 : Reg)
  /-- SRL rd, rs1, rs2 : rd := rs1 >>> rs2[4:0] (shift right logical) -/
  | SRL  (rd rs1 rs2 : Reg)
  /-- SRA rd, rs1, rs2 : rd := rs1 >>s rs2[4:0] (shift right arithmetic) -/
  | SRA  (rd rs1 rs2 : Reg)
  /-- AND rd, rs1, rs2 : rd := rs1 &&& rs2 -/
  | AND  (rd rs1 rs2 : Reg)
  /-- OR rd, rs1, rs2 : rd := rs1 ||| rs2 -/
  | OR   (rd rs1 rs2 : Reg)
  /-- XOR rd, rs1, rs2 : rd := rs1 ^^^ rs2 -/
  | XOR  (rd rs1 rs2 : Reg)
  /-- SLT rd, rs1, rs2 : rd := (rs1 <s rs2) ? 1 : 0 (signed) -/
  | SLT  (rd rs1 rs2 : Reg)
  /-- SLTU rd, rs1, rs2 : rd := (rs1 <u rs2) ? 1 : 0 (unsigned) -/
  | SLTU (rd rs1 rs2 : Reg)
  -- RV32I ALU immediate
  /-- ADDI rd, rs1, imm : rd := rs1 + sext(imm) -/
  | ADDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- ANDI rd, rs1, imm : rd := rs1 &&& sext(imm) -/
  | ANDI (rd rs1 : Reg) (imm : BitVec 12)
  /-- ORI rd, rs1, imm : rd := rs1 ||| sext(imm) -/
  | ORI  (rd rs1 : Reg) (imm : BitVec 12)
  /-- XORI rd, rs1, imm : rd := rs1 ^^^ sext(imm) -/
  | XORI (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLTI rd, rs1, imm : rd := (rs1 <s sext(imm)) ? 1 : 0 -/
  | SLTI (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLTIU rd, rs1, imm : rd := (rs1 <u sext(imm)) ? 1 : 0 -/
  | SLTIU (rd rs1 : Reg) (imm : BitVec 12)
  /-- SLLI rd, rs1, shamt : rd := rs1 << shamt -/
  | SLLI (rd rs1 : Reg) (shamt : BitVec 5)
  /-- SRLI rd, rs1, shamt : rd := rs1 >>> shamt (logical) -/
  | SRLI (rd rs1 : Reg) (shamt : BitVec 5)
  /-- SRAI rd, rs1, shamt : rd := rs1 >>s shamt (arithmetic) -/
  | SRAI (rd rs1 : Reg) (shamt : BitVec 5)
  -- RV32I upper immediate
  /-- LUI rd, imm : rd := imm << 12 -/
  | LUI  (rd : Reg) (imm : BitVec 20)
  /-- AUIPC rd, imm : rd := PC + (imm << 12) -/
  | AUIPC (rd : Reg) (imm : BitVec 20)
  -- RV32I word memory
  /-- LW rd, offset(rs1) : rd := mem[rs1 + sext(offset)] -/
  | LW   (rd rs1 : Reg) (offset : BitVec 12)
  /-- SW rs2, offset(rs1) : mem[rs1 + sext(offset)] := rs2 -/
  | SW   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV32I sub-word memory
  /-- LB rd, offset(rs1) : rd := sext(mem_byte[rs1 + sext(offset)]) -/
  | LB   (rd rs1 : Reg) (offset : BitVec 12)
  /-- LH rd, offset(rs1) : rd := sext(mem_halfword[rs1 + sext(offset)]) -/
  | LH   (rd rs1 : Reg) (offset : BitVec 12)
  /-- LBU rd, offset(rs1) : rd := zext(mem_byte[rs1 + sext(offset)]) -/
  | LBU  (rd rs1 : Reg) (offset : BitVec 12)
  /-- LHU rd, offset(rs1) : rd := zext(mem_halfword[rs1 + sext(offset)]) -/
  | LHU  (rd rs1 : Reg) (offset : BitVec 12)
  /-- SB rs2, offset(rs1) : mem_byte[rs1 + sext(offset)] := rs2[7:0] -/
  | SB   (rs1 rs2 : Reg) (offset : BitVec 12)
  /-- SH rs2, offset(rs1) : mem_halfword[rs1 + sext(offset)] := rs2[15:0] -/
  | SH   (rs1 rs2 : Reg) (offset : BitVec 12)
  -- RV32I branches
  /-- BEQ rs1, rs2, offset : branch if rs1 = rs2 (B-type, byte offset) -/
  | BEQ  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BNE rs1, rs2, offset : branch if rs1 ≠ rs2 (B-type, byte offset) -/
  | BNE  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BLT rs1, rs2, offset : branch if rs1 <s rs2 (signed) -/
  | BLT  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BGE rs1, rs2, offset : branch if rs1 >=s rs2 (signed) -/
  | BGE  (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BLTU rs1, rs2, offset : branch if rs1 <u rs2 (unsigned) -/
  | BLTU (rs1 rs2 : Reg) (offset : BitVec 13)
  /-- BGEU rs1, rs2, offset : branch if rs1 >=u rs2 (unsigned) -/
  | BGEU (rs1 rs2 : Reg) (offset : BitVec 13)
  -- RV32I jumps
  /-- JAL rd, offset : jump and link (J-type, byte offset) -/
  | JAL  (rd : Reg) (offset : BitVec 21)
  /-- JALR rd, rs1, offset : jump and link register (I-type) -/
  | JALR (rd rs1 : Reg) (offset : BitVec 12)
  -- RV32I pseudo-instructions
  /-- MV rd, rs (pseudo: ADDI rd, rs, 0) -/
  | MV   (rd rs : Reg)
  /-- LI rd, imm (pseudo: load immediate) -/
  | LI   (rd : Reg) (imm : Word)
  /-- NOP (pseudo: ADDI x0, x0, 0) -/
  | NOP
  -- RV32I system
  /-- ECALL: environment call (syscall ID in t0/x5, args in a0-a2).
      Following SP1 convention, t0 = 0 signals HALT with exit code in a0. -/
  | ECALL
  /-- FENCE: memory ordering fence (NOP in single-hart zkVM) -/
  | FENCE
  /-- EBREAK: breakpoint trap -/
  | EBREAK
  -- RV32M multiply
  /-- MUL rd, rs1, rs2 : rd := (rs1 * rs2)[31:0] -/
  | MUL  (rd rs1 rs2 : Reg)
  /-- MULH rd, rs1, rs2 : rd := (sext(rs1) * sext(rs2))[63:32] -/
  | MULH (rd rs1 rs2 : Reg)
  /-- MULHSU rd, rs1, rs2 : rd := (sext(rs1) * zext(rs2))[63:32] -/
  | MULHSU (rd rs1 rs2 : Reg)
  /-- MULHU rd, rs1, rs2 : rd := (zext(rs1) * zext(rs2))[63:32] -/
  | MULHU (rd rs1 rs2 : Reg)
  -- RV32M divide
  /-- DIV rd, rs1, rs2 : rd := rs1 /s rs2 (signed division) -/
  | DIV  (rd rs1 rs2 : Reg)
  /-- DIVU rd, rs1, rs2 : rd := rs1 /u rs2 (unsigned division) -/
  | DIVU (rd rs1 rs2 : Reg)
  /-- REM rd, rs1, rs2 : rd := rs1 %s rs2 (signed remainder) -/
  | REM  (rd rs1 rs2 : Reg)
  /-- REMU rd, rs1, rs2 : rd := rs1 %u rs2 (unsigned remainder) -/
  | REMU (rd rs1 rs2 : Reg)
  deriving Repr, DecidableEq

-- ============================================================================
-- Instruction classification
-- ============================================================================

/-- Is this instruction a branch or jump? -/
def Instr.isBranch : Instr → Bool
  | .BEQ _ _ _  => true
  | .BNE _ _ _  => true
  | .BLT _ _ _  => true
  | .BGE _ _ _  => true
  | .BLTU _ _ _ => true
  | .BGEU _ _ _ => true
  | .JAL _ _    => true
  | .JALR _ _ _ => true
  | _           => false

/-- Is this instruction a memory access? -/
def Instr.isMemAccess : Instr → Bool
  | .LW _ _ _   => true
  | .SW _ _ _   => true
  | .LB _ _ _   => true
  | .LH _ _ _   => true
  | .LBU _ _ _  => true
  | .LHU _ _ _  => true
  | .SB _ _ _   => true
  | .SH _ _ _   => true
  | _           => false

-- ============================================================================
-- Sign extension helpers
-- ============================================================================

/-- Sign-extend a 12-bit immediate to 32 bits. -/
def signExtend12 (imm : BitVec 12) : Word :=
  imm.signExtend 32

/-- Sign-extend a 13-bit branch offset to 32 bits. -/
def signExtend13 (imm : BitVec 13) : Word :=
  imm.signExtend 32

/-- Sign-extend a 21-bit jump offset to 32 bits. -/
def signExtend21 (imm : BitVec 21) : Word :=
  imm.signExtend 32

-- ============================================================================
-- M-extension helper functions (division/multiply edge cases per RV32IM spec)
-- ============================================================================

/-- RV32IM signed division with spec-mandated edge cases:
    - Division by zero returns -1 (all ones)
    - Overflow (-2^31 / -1) returns -2^31 -/
def rv32_div (a b : Word) : Word :=
  if b == 0#32 then
    (BitVec.ofNat 32 0xFFFFFFFF)  -- -1
  else
    BitVec.sdiv a b  -- handles overflow correctly

/-- RV32IM unsigned division: division by zero returns 2^32-1. -/
def rv32_divu (a b : Word) : Word :=
  if b == 0#32 then
    (BitVec.ofNat 32 0xFFFFFFFF)  -- 2^32 - 1
  else
    a / b

/-- RV32IM signed remainder with spec-mandated edge cases:
    - Division by zero returns the dividend
    - Overflow (-2^31 % -1) returns 0 -/
def rv32_rem (a b : Word) : Word :=
  if b == 0#32 then
    a
  else
    BitVec.srem a b  -- handles overflow correctly (returns 0)

/-- RV32IM unsigned remainder: division by zero returns the dividend. -/
def rv32_remu (a b : Word) : Word :=
  if b == 0#32 then
    a
  else
    a % b

/-- MULH: signed × signed, upper 32 bits. -/
def rv32_mulh (a b : Word) : Word :=
  let a64 : BitVec 64 := a.signExtend 64
  let b64 : BitVec 64 := b.signExtend 64
  (a64 * b64 >>> 32).truncate 32

/-- MULHSU: signed × unsigned, upper 32 bits. -/
def rv32_mulhsu (a b : Word) : Word :=
  let a64 : BitVec 64 := a.signExtend 64
  let b64 : BitVec 64 := b.zeroExtend 64
  (a64 * b64 >>> 32).truncate 32

/-- MULHU: unsigned × unsigned, upper 32 bits. -/
def rv32_mulhu (a b : Word) : Word :=
  let a64 : BitVec 64 := a.zeroExtend 64
  let b64 : BitVec 64 := b.zeroExtend 64
  (a64 * b64 >>> 32).truncate 32

-- ============================================================================
-- Instruction Semantics
-- ============================================================================

/-- Execute a single instruction, returning the new state.
    The PC is advanced by 4 (one instruction width).
    Branch/jump instructions are treated as NOP in list-based execution;
    for proper branch semantics, use execInstrBr + step-based execution. -/
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
    | .SRA rd rs1 rs2 =>
        let shamt := (s.getReg rs2).toNat % 32
        s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt)
    | .AND rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 &&& s.getReg rs2)
    | .ANDI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 &&& signExtend12 imm)
    | .OR rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 ||| s.getReg rs2)
    | .ORI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 ||| signExtend12 imm)
    | .XOR rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 ^^^ s.getReg rs2)
    | .XORI rd rs1 imm =>
        s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)
    | .SLT rd rs1 rs2 =>
        s.setReg rd (if BitVec.slt (s.getReg rs1) (s.getReg rs2) then 1 else 0)
    | .SLTU rd rs1 rs2 =>
        s.setReg rd (if BitVec.ult (s.getReg rs1) (s.getReg rs2) then 1 else 0)
    | .SLTI rd rs1 imm =>
        s.setReg rd (if BitVec.slt (s.getReg rs1) (signExtend12 imm) then 1 else 0)
    | .SLTIU rd rs1 imm =>
        s.setReg rd (if BitVec.ult (s.getReg rs1) (signExtend12 imm) then 1 else 0)
    | .SRLI rd rs1 shamt =>
        s.setReg rd (s.getReg rs1 >>> shamt.toNat)
    | .SRAI rd rs1 shamt =>
        s.setReg rd (BitVec.sshiftRight (s.getReg rs1) shamt.toNat)
    | .LW rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd (s.getMem addr)
    | .SW rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setMem addr (s.getReg rs2)
    | .LB rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).signExtend 32)
    | .LH rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).signExtend 32)
    | .LBU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getByte addr).zeroExtend 32)
    | .LHU rd rs1 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setReg rd ((s.getHalfword addr).zeroExtend 32)
    | .SB rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setByte addr ((s.getReg rs2).truncate 8)
    | .SH rs1 rs2 offset =>
        let addr := s.getReg rs1 + signExtend12 offset
        s.setHalfword addr ((s.getReg rs2).truncate 16)
    | .LUI rd imm =>
        let val : Word := imm.zeroExtend 32 <<< 12
        s.setReg rd val
    | .AUIPC rd imm =>
        let val : Word := s.pc + (imm.zeroExtend 32 <<< 12)
        s.setReg rd val
    | .MV rd rs =>
        s.setReg rd (s.getReg rs)
    | .LI rd imm =>
        s.setReg rd imm
    | .NOP => s
    | .FENCE => s  -- NOP in single-hart zkVM
    | .EBREAK => s  -- NOP in list-based execution
    -- M extension
    | .MUL rd rs1 rs2 =>
        s.setReg rd (s.getReg rs1 * s.getReg rs2)
    | .MULH rd rs1 rs2 =>
        s.setReg rd (rv32_mulh (s.getReg rs1) (s.getReg rs2))
    | .MULHSU rd rs1 rs2 =>
        s.setReg rd (rv32_mulhsu (s.getReg rs1) (s.getReg rs2))
    | .MULHU rd rs1 rs2 =>
        s.setReg rd (rv32_mulhu (s.getReg rs1) (s.getReg rs2))
    | .DIV rd rs1 rs2 =>
        s.setReg rd (rv32_div (s.getReg rs1) (s.getReg rs2))
    | .DIVU rd rs1 rs2 =>
        s.setReg rd (rv32_divu (s.getReg rs1) (s.getReg rs2))
    | .REM rd rs1 rs2 =>
        s.setReg rd (rv32_rem (s.getReg rs1) (s.getReg rs2))
    | .REMU rd rs1 rs2 =>
        s.setReg rd (rv32_remu (s.getReg rs1) (s.getReg rs2))
    -- Branch/jump instructions are treated as NOP in list-based execution.
    | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _
    | .BLTU _ _ _ | .BGEU _ _ _ | .JAL _ _ | .JALR _ _ _ | .ECALL => s
  s'.setPC (s'.pc + 4#32)

end RiscVMacroAsm
