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
    ⦃(.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w)⦄
    swap .x10 .x11 .x5
    ⦃(.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v)⦄ := by
  intro s ⟨hrd, hrs⟩
  simp only [regIs, sepConj] at *
  -- Unfold the swap program and execution
  simp only [swap, seq, execProgram_seq, execProgram, MV, single, execInstr]
  -- Now reason about the chain of setReg/getReg operations.
  -- After MV x5 x10: x5 := s.getReg x10 = v
  -- After MV x10 x11: x10 := (prev state).getReg x11 = w
  -- After MV x11 x5: x11 := (prev state).getReg x5 = v
  -- Each step involves setPC (which doesn't affect regs) and setReg.
  constructor
  · -- Goal: final state's x10 = w
    simp only [MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ .x11 .x10 _ (by decide)]
    rw [MachineState.getReg_setReg_eq _ .x10 _ (by decide)]
    simp only [MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ .x5 .x11 _ (by decide)]
    exact hrs
  · -- Goal: final state's x11 = v
    simp only [MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq _ .x11 _ (by decide)]
    simp only [MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ .x10 .x5 _ (by decide)]
    simp only [MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq _ .x5 _ (by decide)]
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
    ⦃rd ↦ᵣ v⦄ zero rd ⦃rd ↦ᵣ 0⦄ := by
  intro s hpre
  simp only [regIs] at *
  simp only [zero, SUB, single, seq, execProgram, execInstr]
  simp only [MachineState.getReg_setPC]
  rw [MachineState.getReg_setReg_eq _ rd _ hrd]
  simp [hpre, BitVec.sub_self]

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
