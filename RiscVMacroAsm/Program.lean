/-
  RiscVMacroAsm.Program

  Programs as sequences of instructions, with sequential composition.
  This is the "macro assembler" part: programs are Lean definitions that
  produce instruction sequences, allowing us to use Lean as a macro language.
-/

import RiscVMacroAsm.Instructions

namespace RiscVMacroAsm

-- ============================================================================
-- Programs
-- ============================================================================

/-- A program is a list of instructions. -/
def Program := List Instr

instance : Append Program := ⟨List.append⟩

/-- The empty program (no instructions). -/
def prog_skip : Program := []

/-- A single instruction as a program. -/
def single (i : Instr) : Program := [i]

/-- Sequential composition of programs. -/
def seq (p1 p2 : Program) : Program := p1 ++ p2

/-- Notation for sequential composition: p1 ;; p2 -/
infixr:50 " ;; " => seq

-- ============================================================================
-- Program Execution
-- ============================================================================

/-- Execute a program (list of instructions) sequentially. -/
def execProgram (s : MachineState) : Program → MachineState
  | []      => s
  | i :: is => execProgram (execInstr s i) is

/-- Executing the empty program is the identity. -/
@[simp]
theorem execProgram_nil (s : MachineState) :
    execProgram s [] = s := rfl

/-- Executing a single instruction. -/
@[simp]
theorem execProgram_cons (s : MachineState) (i : Instr) (is : List Instr) :
    execProgram s (i :: is) = execProgram (execInstr s i) is := rfl

/-- Sequential composition of programs composes execution. -/
theorem execProgram_append (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ++ p2) = execProgram (execProgram s p1) p2 := by
  induction p1 generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [execProgram]
    exact ih (execInstr s i)

/-- Sequential composition (;;) composes execution. -/
theorem execProgram_seq (s : MachineState) (p1 p2 : Program) :
    execProgram s (p1 ;; p2) = execProgram (execProgram s p1) p2 :=
  execProgram_append s p1 p2

-- ============================================================================
-- Convenience constructors (macro-assembler style)
-- ============================================================================

/-- Wrap a single instruction into a program. -/
def ADD  (rd rs1 rs2 : Reg)                 : Program := single (.ADD rd rs1 rs2)
def ADDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ADDI rd rs1 imm)
def SUB  (rd rs1 rs2 : Reg)                 : Program := single (.SUB rd rs1 rs2)
def SLL  (rd rs1 rs2 : Reg)                 : Program := single (.SLL rd rs1 rs2)
def SLLI (rd rs1 : Reg) (shamt : BitVec 5)  : Program := single (.SLLI rd rs1 shamt)
def SRL  (rd rs1 rs2 : Reg)                 : Program := single (.SRL rd rs1 rs2)
def AND' (rd rs1 rs2 : Reg)                 : Program := single (.AND rd rs1 rs2)
def ANDI (rd rs1 : Reg) (imm : BitVec 12)   : Program := single (.ANDI rd rs1 imm)
def OR'  (rd rs1 rs2 : Reg)                 : Program := single (.OR rd rs1 rs2)
def LW   (rd rs1 : Reg) (offset : BitVec 12): Program := single (.LW rd rs1 offset)
def SW   (rs1 rs2 : Reg) (offset : BitVec 12): Program := single (.SW rs1 rs2 offset)
def LUI  (rd : Reg) (imm : BitVec 20)       : Program := single (.LUI rd imm)
def MV   (rd rs : Reg)                      : Program := single (.MV rd rs)
def LI   (rd : Reg) (imm : Word)            : Program := single (.LI rd imm)
def NOP                                     : Program := single .NOP
def ECALL                                   : Program := single .ECALL

/-- HALT macro (SP1 convention): set t0 := 0 (HALT syscall), a0 := exit code, then ecall. -/
def HALT (exitCode : Word := 0) : Program :=
  LI .x5 0 ;;
  LI .x10 exitCode ;;
  single .ECALL

/-- COMMIT macro (SP1 convention): set t0 := 0x10 (COMMIT syscall),
    a0/a1 for data, then ecall. Execution continues after commit. -/
def COMMIT (a0val a1val : Word) : Program :=
  LI .x5 0x10 ;;
  LI .x10 a0val ;;
  LI .x11 a1val ;;
  single .ECALL

/-- WRITE macro (SP1 convention): set t0 := 0x02 (WRITE syscall),
    a0 := fd, a1 := buffer pointer, a2 := nbytes, then ecall. -/
def WRITE (fd bufPtr nbytes : Word) : Program :=
  LI .x5 0x02 ;;
  LI .x10 fd ;;
  LI .x11 bufPtr ;;
  LI .x12 nbytes ;;
  single .ECALL

/-- HINT_LEN macro (SP1 convention): set t0 := 0xF0 (HINT_LEN syscall),
    then ecall. Returns byte length of available input in a0. -/
def HINT_LEN : Program :=
  LI .x5 0xF0 ;;
  single .ECALL

/-- HINT_READ macro (SP1 convention): set t0 := 0xF1 (HINT_READ syscall),
    a0 := destination address, a1 := nbytes, then ecall. -/
def HINT_READ (addr nbytes : Word) : Program :=
  LI .x5 0xF1 ;;
  LI .x10 addr ;;
  LI .x11 nbytes ;;
  single .ECALL

end RiscVMacroAsm
