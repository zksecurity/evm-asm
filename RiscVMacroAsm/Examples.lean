/-
  RiscVMacroAsm.Examples

  Demonstration of using the macro assembler to build small programs
  and verify their behavior.
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.Program
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Spec
import RiscVMacroAsm.MulMacro
import RiscVMacroAsm.Execution

namespace RiscVMacroAsm

-- ============================================================================
-- Example 1: A simple swap macro
-- ============================================================================

/-- Swap the values of two registers using a temporary register.
    swap rd rs tmp :=
      MV tmp, rd
      MV rd, rs
      MV rs, tmp
-/
def swap (rd rs tmp : Reg) : Program :=
  MV tmp rd ;;
  MV rd rs ;;
  MV rs tmp

/-- Test state for swap. -/
def swapTestState : MachineState where
  regs := fun r =>
    match r with
    | .x10 => 42
    | .x11 => 99
    | _    => 0
  mem := fun _ => 0
  pc := 0

/-- Swap correctness on concrete values: x10 gets the old value of x11. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x10 = 99 := by
  native_decide

/-- Swap correctness on concrete values: x11 gets the old value of x10. -/
example : (execProgram swapTestState (swap .x10 .x11 .x5)).getReg .x11 = 42 := by
  native_decide

-- ============================================================================
-- Example 2: Zero a register
-- ============================================================================

/-- Zero a register: rd := 0. Uses SUB rd, rd, rd. -/
def zero (rd : Reg) : Program :=
  SUB rd rd rd

def zeroTestState : MachineState where
  regs := fun r =>
    match r with
    | .x10 => 12345
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram zeroTestState (zero .x10)).getReg .x10 = 0 := by
  native_decide

-- ============================================================================
-- Example 3: Multiply by constant (from MulMacro)
-- ============================================================================

/-- Multiply x11 by 7, storing the result in x10.
    We first zero x10, then use add_mulc. -/
def mul7 (rd rs : Reg) : Program :=
  zero rd ;;
  add_mulc 8 rd rs 7

def mul7TestState : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 6
    | _    => 0
  mem := fun _ => 0
  pc := 0

/-- 6 * 7 = 42 -/
example : (execProgram mul7TestState (mul7 .x10 .x11)).getReg .x10 = 42 := by
  native_decide

/-- 13 * 7 = 91 -/
def mul7TestState2 : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 13
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram mul7TestState2 (mul7 .x10 .x11)).getReg .x10 = 91 := by
  native_decide

-- ============================================================================
-- Example 4: Load-modify-store pattern
-- ============================================================================

/-- Load a value from memory, add a constant, store it back.
    inc_mem base offset tmp :=
      LW tmp, offset(base)
      ADDI tmp, tmp, 1
      SW base, tmp, offset
-/
def inc_mem (base tmp : Reg) (offset : BitVec 12) : Program :=
  LW tmp base offset ;;
  ADDI tmp tmp 1 ;;
  SW base tmp offset

-- ============================================================================
-- Example 5: Hoare triple for swap (symbolic proof)
-- ============================================================================

/-- Swap specification as a Hoare triple with separating conjunction.

    This is the style from Kennedy et al.: precondition states that
    x10 holds v and x11 holds w (as separated resources), and the
    postcondition states they are swapped.

    The proof uses the getReg_setReg lemmas to trace through the
    chain of register updates. -/
theorem swap_spec (v w : Word) :
    ⦃((.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w)).holdsFor⦄
    swap .x10 .x11 .x5
    ⦃((.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v)).holdsFor⦄ := by
  intro s hpre
  rw [holdsFor_sepConj_regIs_regIs (by decide)] at hpre
  rw [holdsFor_sepConj_regIs_regIs (by decide)]
  obtain ⟨hrd, hrs⟩ := hpre
  -- Unfold the swap program and execution
  simp only [swap, seq, MV, single]
  rw [execProgram_append, execProgram_append]
  simp only [execProgram, execInstr]
  constructor
  · -- Goal: final state's x10 = w
    simp [MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
          MachineState.getReg_setReg_eq]
    exact hrs
  · -- Goal: final state's x11 = v
    simp [MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
          MachineState.getReg_setReg_eq]
    exact hrd

-- ============================================================================
-- Example 6: Combining macros
-- ============================================================================

/-- Double a value: rd := rs * 2. This is just a single left shift. -/
def double (rd rs : Reg) : Program :=
  SLLI rd rs 1

/-- Triple a value: rd := rs * 3 = rs + rs * 2.
    We move rs to rd, then shift rs, then add. -/
def triple (rd rs tmp : Reg) : Program :=
  MV rd rs ;;       -- rd := rs
  SLLI tmp rs 1 ;;  -- tmp := rs * 2
  ADD rd rd tmp     -- rd := rs + rs * 2 = rs * 3

def tripleTestState : MachineState where
  regs := fun r =>
    match r with
    | .x11 => 15
    | _    => 0
  mem := fun _ => 0
  pc := 0

example : (execProgram tripleTestState (triple .x10 .x11 .x5)).getReg .x10 = 45 := by
  native_decide

-- ============================================================================
-- Example 7: Hoare triple using the frame rule
-- ============================================================================

/-- Demonstrate the frame rule: adding an unrelated register to the spec. -/
theorem zero_with_frame (rd : Reg) (v : Word) (hrd : rd ≠ .x0) :
    ⦃(rd ↦ᵣ v).holdsFor⦄ zero rd ⦃(rd ↦ᵣ 0).holdsFor⦄ := by
  intro s hpre
  rw [holdsFor_regIs] at hpre ⊢
  simp only [zero, SUB, single, seq, execProgram, execInstr]
  simp only [MachineState.getReg_setPC]
  rw [MachineState.getReg_setReg_eq _ rd _ hrd]
  simp [hpre, BitVec.sub_self]

-- ============================================================================
-- Example 8: ECALL-based halting (SP1 convention)
-- ============================================================================

/-- A program that computes 6 * 7 and halts with the result as exit code. -/
def mul_and_halt : Program :=
  LI .x10 0 ;;
  LI .x11 6 ;;
  add_mulc 8 .x10 .x11 7 ;;
  LI .x5 0 ;;     -- t0 := HALT
  single .ECALL

def mul_and_halt_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After running all instructions before ECALL, the next step halts. -/
example : let code := loadProgram 0 mul_and_halt
          let steps := mul_and_halt.length - 1  -- run up to ECALL
          (stepN steps code mul_and_halt_state).bind (fun s =>
            step code s) = none := by
  native_decide

/-- After running all instructions before ECALL, a0 (x10) contains 42. -/
example : let code := loadProgram 0 mul_and_halt
          let steps := mul_and_halt.length - 1
          (stepN steps code mul_and_halt_state).bind (fun s =>
            some (s.getReg .x10)) = some 42 := by
  native_decide

/-- A simple program that halts immediately with exit code 0. -/
def halt_zero : Program := HALT 0

/-- halt_zero terminates in 3 steps (LI x5, LI x10, ECALL),
    and the next step returns none. -/
example : let code := loadProgram 0 halt_zero
          let s0 := mul_and_halt_state
          (stepN 2 code s0).bind (fun s => step code s) = none := by
  native_decide

-- ============================================================================
-- Example 9: COMMIT syscall (SP1 convention)
-- ============================================================================

/-- A program that commits a value then halts. -/
def commit_and_halt : Program :=
  LI .x10 42 ;;
  LI .x11 0 ;;
  LI .x5 0x10 ;;     -- t0 := COMMIT
  single .ECALL ;;   -- commit (continues)
  LI .x5 0 ;;        -- t0 := HALT
  single .ECALL       -- halt

def commit_and_halt_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After the commit step (4 instructions to set up + ECALL), execution continues. -/
example : let code := loadProgram 0 commit_and_halt
          let steps := 4  -- LI x10, LI x11, LI x5, ECALL (commit)
          (stepN steps code commit_and_halt_state).isSome = true := by
  native_decide

/-- After all steps up to halt, the next step returns none (halted). -/
example : let code := loadProgram 0 commit_and_halt
          let steps := commit_and_halt.length - 1  -- run up to halt ECALL
          (stepN steps code commit_and_halt_state).bind (fun s =>
            step code s) = none := by
  native_decide

/-- At the halt point, a0 (x10) still contains 42. -/
example : let code := loadProgram 0 commit_and_halt
          let steps := commit_and_halt.length - 1
          (stepN steps code commit_and_halt_state).bind (fun s =>
            some (s.getReg .x10)) = some 42 := by
  native_decide

-- ============================================================================
-- Summary: The macro assembler pattern
-- ============================================================================

/-!
  ## The Macro Assembler Pattern

  The key idea from Kennedy et al. is:

  1. **Instructions** are data: they are an inductive type in Lean.
  2. **Programs** are lists of instructions with sequential composition (;;).
  3. **Macros** are Lean functions that produce programs. They can use
     all of Lean's facilities: recursion, pattern matching, conditionals.
  4. **Specifications** are Hoare triples using separation logic.
  5. **Proofs** verify that macros meet their specifications.

  Lean serves as both the macro language and the verification language.
  The `add_mulc` example shows a recursive macro that compiles a
  multiply-by-constant into a sequence of shifts and adds, with concrete
  correctness verified by `native_decide` and a general specification
  stated using Hoare triples and separating conjunction.
-/

end RiscVMacroAsm
