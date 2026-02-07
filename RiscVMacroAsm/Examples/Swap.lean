/-
  RiscVMacroAsm.Examples.Swap

  A simple swap macro and its Hoare triple specification.
-/

import RiscVMacroAsm.Spec

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Swap macro
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
-- Hoare triple for swap (symbolic proof)
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

end RiscVMacroAsm.Examples
