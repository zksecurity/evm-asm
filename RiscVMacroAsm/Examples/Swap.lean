/-
  RiscVMacroAsm.Examples.Swap

  A simple swap macro and its CPS-style Hoare triple specification.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.ControlFlow

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
-- CPS-style Hoare triple for swap (symbolic proof, 3 steps)
-- ============================================================================

/-- Swap specification as a cpsTriple: 3 steps of MV instructions.

    Precondition: x10 holds v and x11 holds w.
    Postcondition: x10 holds w and x11 holds v.

    The proof traces register values through 3 MV instructions
    using loadProgram_at_base and loadProgram_at_index. -/
theorem swap_cpsTriple (v w : Word) (base : Addr) :
    cpsTriple (loadProgram base (swap .x10 .x11 .x5)) base (base + 12)
      ((.x10 ↦ᵣ v) ** (.x11 ↦ᵣ w))
      ((.x10 ↦ᵣ w) ** (.x11 ↦ᵣ v)) := by
  intro s hpre hpc
  rw [holdsFor_sepConj_regIs_regIs (by decide)] at hpre
  obtain ⟨hx10, hx11⟩ := hpre
  -- The swap program is [MV x5 x10, MV x10 x11, MV x11 x5]
  -- i.e., 3 instructions
  have hprog : swap .x10 .x11 .x5 = [Instr.MV .x5 .x10, Instr.MV .x10 .x11, Instr.MV .x11 .x5] := by
    simp only [swap, seq, MV, single, Program]
    rfl
  -- Fetch instruction 0: MV x5 x10 at base
  have hfetch0 : loadProgram base (swap .x10 .x11 .x5) base = some (Instr.MV .x5 .x10) := by
    rw [hprog]; exact loadProgram_at_base base _ _
  -- Step 1: execute MV x5 x10
  have hstep1 : step (loadProgram base (swap .x10 .x11 .x5)) s =
      some (execInstrBr s (Instr.MV .x5 .x10)) := by
    simp [step, hpc, hfetch0]
  let s1 := execInstrBr s (Instr.MV .x5 .x10)
  have hs1_pc : s1.pc = base + 4 := by simp [s1, execInstrBr, MachineState.setPC, hpc]
  have hs1_x10 : s1.getReg .x10 = v := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hx10]
  have hs1_x11 : s1.getReg .x11 = w := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hx11]
  have hs1_x5 : s1.getReg .x5 = v := by
    simp [s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hx10]
  -- Fetch instruction 1: MV x10 x11 at base+4
  have hfetch1 : loadProgram base (swap .x10 .x11 .x5) (base + BitVec.ofNat 32 4) =
      some (Instr.MV .x10 .x11) := by
    rw [hprog, loadProgram_at_index base _ 1 (by simp) (by omega)]
    simp
  -- Step 2: execute MV x10 x11
  have hstep2 : step (loadProgram base (swap .x10 .x11 .x5)) s1 =
      some (execInstrBr s1 (Instr.MV .x10 .x11)) := by
    simp [step, hs1_pc, hfetch1]
  let s2 := execInstrBr s1 (Instr.MV .x10 .x11)
  have hs2_pc : s2.pc = base + 8 := by
    simp only [s2, execInstrBr, MachineState.setPC, hs1_pc, BitVec.add_assoc]; rfl
  have hs2_x10 : s2.getReg .x10 = w := by
    simp [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hs1_x11]
  have hs2_x11 : s2.getReg .x11 = w := by
    simp [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs1_x11]
  have hs2_x5 : s2.getReg .x5 = v := by
    simp [s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs1_x5]
  -- Fetch instruction 2: MV x11 x5 at base+8
  have hfetch2 : loadProgram base (swap .x10 .x11 .x5) (base + BitVec.ofNat 32 8) =
      some (Instr.MV .x11 .x5) := by
    rw [hprog, loadProgram_at_index base _ 2 (by simp) (by omega)]
    simp
  -- Step 3: execute MV x11 x5
  have hstep3 : step (loadProgram base (swap .x10 .x11 .x5)) s2 =
      some (execInstrBr s2 (Instr.MV .x11 .x5)) := by
    simp [step, hs2_pc, hfetch2]
  let s3 := execInstrBr s2 (Instr.MV .x11 .x5)
  have hs3_pc : s3.pc = base + 12 := by
    simp only [s3, execInstrBr, MachineState.setPC, hs2_pc, BitVec.add_assoc]; rfl
  have hs3_x10 : s3.getReg .x10 = w := by
    simp [s3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, hs2_x10]
  have hs3_x11 : s3.getReg .x11 = v := by
    simp [s3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, hs2_x5]
  -- Compose 3 steps
  refine ⟨3, s3, ?_, hs3_pc, ?_⟩
  · show (step (loadProgram base (swap .x10 .x11 .x5)) s).bind
      (fun s' => (step (loadProgram base (swap .x10 .x11 .x5)) s').bind
        (fun s' => (step (loadProgram base (swap .x10 .x11 .x5)) s').bind
          (fun s' => some s'))) = some s3
    rw [hstep1, Option.bind, hstep2, Option.bind, hstep3, Option.bind]
  · rw [holdsFor_sepConj_regIs_regIs (by decide)]
    exact ⟨hs3_x10, hs3_x11⟩

end RiscVMacroAsm.Examples
