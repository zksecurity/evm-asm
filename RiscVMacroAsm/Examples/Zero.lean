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
  intro R hR s hPR hpc
  -- Extract register value from precondition
  have hv : s.getReg rd = v :=
    (holdsFor_regIs rd v s).mp (holdsFor_sepConj_elim_left hPR)
  -- Fetch SUB at base
  have hfetch : loadProgram base (zero rd) base = some (Instr.SUB rd rd rd) := by
    simp [zero, SUB, single, loadProgram_at_base]
  -- Execute 1 step
  have hstep : step (loadProgram base (zero rd)) s =
      some (execInstrBr s (Instr.SUB rd rd rd)) := by
    simp [step, hpc, hfetch]
  -- s' = (s.setReg rd (rd - rd)).setPC (s.pc + 4) = (s.setReg rd 0).setPC (base + 4)
  have hexec : execInstrBr s (Instr.SUB rd rd rd) =
      (s.setReg rd 0).setPC (s.pc + 4) := by
    simp [execInstrBr, hv, BitVec.sub_self]
  refine ⟨1, (s.setReg rd 0).setPC (s.pc + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, hexec, Option.bind]
  · simp [MachineState.setPC, hpc]
  · -- Frame preservation: (rd ↦ᵣ v) ** R through setReg rd 0, then setPC
    have h1 := holdsFor_sepConj_regIs_setReg (v' := (0 : Word)) hrd hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd 0) hR) _ _ h1

end RiscVMacroAsm.Examples
