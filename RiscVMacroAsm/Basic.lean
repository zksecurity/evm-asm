/-
  RiscVMacroAsm.Basic

  A simplified RISC-V machine model for macro assembly verification,
  inspired by "Coq: The world's best macro assembler?" (Kennedy et al., 2013).

  We model a small subset of RV32I: enough to demonstrate verified macro
  assembly with separation logic specifications.
-/

namespace RiscVMacroAsm

-- ============================================================================
-- Registers
-- ============================================================================

/-- A small subset of RISC-V integer registers. -/
inductive Reg where
  | x0  -- hardwired zero
  | x1  -- ra
  | x2  -- sp
  | x5  -- t0
  | x6  -- t1
  | x7  -- t2
  | x10 -- a0
  | x11 -- a1
  | x12 -- a2
  deriving DecidableEq, BEq, Repr, Hashable

instance : LawfulBEq Reg where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

namespace Reg

def toNat : Reg → Nat
  | x0  => 0
  | x1  => 1
  | x2  => 2
  | x5  => 5
  | x6  => 6
  | x7  => 7
  | x10 => 10
  | x11 => 11
  | x12 => 12

instance : ToString Reg where
  toString r := s!"x{r.toNat}"

end Reg

-- ============================================================================
-- Word type (32-bit bitvectors)
-- ============================================================================

/-- We use 32-bit words as our machine word size. -/
abbrev Word := BitVec 32

/-- Memory addresses are words. -/
abbrev Addr := Word

-- ============================================================================
-- Machine State
-- ============================================================================

/-- The machine state: a register file, memory, and program counter. -/
structure MachineState where
  /-- Register file: maps register to its value -/
  regs : Reg → Word
  /-- Byte-addressable memory (simplified: word-addressable for now) -/
  mem  : Addr → Word
  /-- Program counter -/
  pc   : Word
  /-- Committed public outputs (a0, a1) from COMMIT syscalls -/
  committed : List (Word × Word) := []
  /-- Accumulated public values from WRITE syscalls (flat word stream) -/
  publicValues : List Word := []
  /-- Public input stream (flat word list, consumed by HINT_READ) -/
  publicInput : List Word := []

namespace MachineState

/-- Read a register (x0 always returns 0). -/
def getReg (s : MachineState) (r : Reg) : Word :=
  match r with
  | .x0 => 0#32
  | _   => s.regs r

/-- Write a register (writes to x0 are silently dropped). -/
def setReg (s : MachineState) (r : Reg) (v : Word) : MachineState :=
  match r with
  | .x0 => s
  | _   => { s with regs := fun r' => if r' == r then v else s.regs r' }

/-- Read memory at an address. -/
def getMem (s : MachineState) (a : Addr) : Word :=
  s.mem a

/-- Write memory at an address. -/
def setMem (s : MachineState) (a : Addr) (v : Word) : MachineState :=
  { s with mem := fun a' => if a' == a then v else s.mem a' }

/-- Set the program counter. -/
def setPC (s : MachineState) (v : Word) : MachineState :=
  { s with pc := v }

/-- Append a committed public output pair. -/
def appendCommit (s : MachineState) (a0 a1 : Word) : MachineState :=
  { s with committed := s.committed ++ [(a0, a1)] }

/-- Read n consecutive words from memory starting at base address. -/
def readWords (s : MachineState) (base : Addr) : Nat → List Word
  | 0 => []
  | n + 1 => s.getMem base :: readWords s (base + 4) n

/-- Write n consecutive words to memory starting at base address. -/
def writeWords (s : MachineState) (base : Addr) : List Word → MachineState
  | [] => s
  | w :: ws => (s.setMem base w).writeWords (base + 4) ws

/-- Append words to the public values stream. -/
def appendPublicValues (s : MachineState) (words : List Word) : MachineState :=
  { s with publicValues := s.publicValues ++ words }

-- Lemmas for reasoning about register file operations

/-- setReg does not affect the program counter. -/
@[simp]
theorem pc_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).pc = s.pc := by
  cases r <;> rfl

/-- setMem does not affect the program counter. -/
@[simp]
theorem pc_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).pc = s.pc := by
  simp [setMem]

/-- setPC does not affect register reads. -/
@[simp]
theorem getReg_setPC (s : MachineState) (v : Word) (r : Reg) :
    (s.setPC v).getReg r = s.getReg r := by
  cases r <;> rfl

/-- Setting register r and reading register r' ≠ r gives the old value. -/
theorem getReg_setReg_ne (s : MachineState) (r r' : Reg) (v : Word)
    (h : r ≠ r') : (s.setReg r v).getReg r' = s.getReg r' := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

/-- Setting register r (≠ x0) and reading it back gives the new value. -/
theorem getReg_setReg_eq (s : MachineState) (r : Reg) (v : Word)
    (h : r ≠ .x0) : (s.setReg r v).getReg r = v := by
  cases r <;> first | exact absurd rfl h | rfl

-- Committed field preservation through existing setters

@[simp]
theorem committed_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).committed = s.committed := by
  cases r <;> rfl

@[simp]
theorem committed_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).committed = s.committed := by
  simp [setMem]

@[simp]
theorem committed_setPC (s : MachineState) (v : Word) :
    (s.setPC v).committed = s.committed := by
  simp [setPC]

-- publicValues field preservation through existing setters

@[simp]
theorem publicValues_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).publicValues = s.publicValues := by
  cases r <;> rfl

@[simp]
theorem publicValues_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).publicValues = s.publicValues := by
  simp [setMem]

@[simp]
theorem publicValues_setPC (s : MachineState) (v : Word) :
    (s.setPC v).publicValues = s.publicValues := by
  simp [setPC]

@[simp]
theorem publicValues_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).publicValues = s.publicValues := by
  simp [appendCommit]

-- publicInput field preservation through existing setters

@[simp]
theorem publicInput_setReg (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).publicInput = s.publicInput := by
  cases r <;> rfl

@[simp]
theorem publicInput_setMem (s : MachineState) (a : Addr) (v : Word) :
    (s.setMem a v).publicInput = s.publicInput := by
  simp [setMem]

@[simp]
theorem publicInput_setPC (s : MachineState) (v : Word) :
    (s.setPC v).publicInput = s.publicInput := by
  simp [setPC]

@[simp]
theorem publicInput_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).publicInput = s.publicInput := by
  simp [appendCommit]

@[simp]
theorem publicInput_appendPublicValues (s : MachineState) (words : List Word) :
    (s.appendPublicValues words).publicInput = s.publicInput := by
  simp [appendPublicValues]

-- appendCommit preservation lemmas

@[simp]
theorem getReg_appendCommit (s : MachineState) (a0 a1 : Word) (r : Reg) :
    (s.appendCommit a0 a1).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp]
theorem getMem_appendCommit (s : MachineState) (a0 a1 : Word) (a : Addr) :
    (s.appendCommit a0 a1).getMem a = s.getMem a := by
  simp [appendCommit, getMem]

@[simp]
theorem pc_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).pc = s.pc := by
  simp [appendCommit]

@[simp]
theorem committed_appendCommit (s : MachineState) (a0 a1 : Word) :
    (s.appendCommit a0 a1).committed = s.committed ++ [(a0, a1)] := by
  simp [appendCommit]

-- appendPublicValues preservation lemmas

@[simp]
theorem getReg_appendPublicValues (s : MachineState) (words : List Word) (r : Reg) :
    (s.appendPublicValues words).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp]
theorem getMem_appendPublicValues (s : MachineState) (words : List Word) (a : Addr) :
    (s.appendPublicValues words).getMem a = s.getMem a := by
  simp [appendPublicValues, getMem]

@[simp]
theorem pc_appendPublicValues (s : MachineState) (words : List Word) :
    (s.appendPublicValues words).pc = s.pc := by
  simp [appendPublicValues]

@[simp]
theorem committed_appendPublicValues (s : MachineState) (words : List Word) :
    (s.appendPublicValues words).committed = s.committed := by
  simp [appendPublicValues]

@[simp]
theorem publicValues_appendPublicValues (s : MachineState) (words : List Word) :
    (s.appendPublicValues words).publicValues = s.publicValues ++ words := by
  simp [appendPublicValues]

-- readWords simp lemmas

@[simp]
theorem readWords_zero (s : MachineState) (base : Addr) :
    s.readWords base 0 = [] := rfl

@[simp]
theorem readWords_succ (s : MachineState) (base : Addr) (n : Nat) :
    s.readWords base (n + 1) = s.getMem base :: s.readWords (base + 4) n := rfl

theorem readWords_length (s : MachineState) (base : Addr) (n : Nat) :
    (s.readWords base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ k ih => simp [readWords, ih]

-- writeWords simp lemmas

@[simp]
theorem writeWords_nil (s : MachineState) (base : Addr) :
    s.writeWords base [] = s := rfl

@[simp]
theorem writeWords_cons (s : MachineState) (base : Addr) (w : Word) (ws : List Word) :
    s.writeWords base (w :: ws) = (s.setMem base w).writeWords (base + 4) ws := rfl

-- writeWords preservation lemmas

@[simp]
theorem pc_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).pc = s.pc := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem committed_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).committed = s.committed := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem publicValues_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).publicValues = s.publicValues := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem publicInput_writeWords (s : MachineState) (base : Addr) (words : List Word) :
    (s.writeWords base words).publicInput = s.publicInput := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih => simp [writeWords, ih]

@[simp]
theorem getReg_writeWords (s : MachineState) (base : Addr) (words : List Word) (r : Reg) :
    (s.writeWords base words).getReg r = s.getReg r := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp [writeWords, ih]
    cases r <;> simp [getReg, setMem]

/-- Predicate asserting the committed output stream equals a given list. -/
def committedIs (vals : List (Word × Word)) (s : MachineState) : Prop :=
  s.committed = vals

/-- Predicate asserting the public values stream equals a given list. -/
def publicValuesIs (vals : List Word) (s : MachineState) : Prop :=
  s.publicValues = vals

/-- Predicate asserting the public input stream equals a given list. -/
def publicInputIs (vals : List Word) (s : MachineState) : Prop :=
  s.publicInput = vals

end MachineState

end RiscVMacroAsm
