/-
  RiscVMacroAsm.Examples.Zero

  A zero-register macro and a CPS-style Hoare triple.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.ControlFlow

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Zero a register
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
-- CPS-style Hoare triple for zero
-- ============================================================================

/-- CPS-style specification: zeroing a register in one step. -/
theorem zero_cpsTriple (rd : Reg) (v : Word) (hrd : rd ≠ .x0) (base : Addr) :
    cpsTriple (loadProgram base (zero rd)) base (base + 4)
      (rd ↦ᵣ v)
      (rd ↦ᵣ 0) := by
  intro s hpre hpc
  simp [holdsFor_regIs] at hpre
  -- Fetch SUB at base
  have hfetch : loadProgram base (zero rd) base = some (Instr.SUB rd rd rd) := by
    simp [zero, SUB, single, loadProgram_at_base]
  -- Execute 1 step
  have hstep : step (loadProgram base (zero rd)) s =
      some (execInstrBr s (Instr.SUB rd rd rd)) := by
    simp [step, hpc, hfetch]
  refine ⟨1, execInstrBr s (Instr.SUB rd rd rd), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [execInstrBr, MachineState.setPC, hpc]
  · simp only [holdsFor_regIs]
    simp [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq _ _ _ hrd,
          BitVec.sub_self]

end RiscVMacroAsm.Examples
