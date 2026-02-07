/-
  RiscVMacroAsm.Examples.Zero

  A zero-register macro and a Hoare triple using the frame rule.
-/

import RiscVMacroAsm.Spec

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
-- Hoare triple using the frame rule
-- ============================================================================

/-- Demonstrate the frame rule: adding an unrelated register to the spec. -/
theorem zero_with_frame (rd : Reg) (v : Word) (hrd : rd ≠ .x0) :
    ⦃(rd ↦ᵣ v).holdsFor⦄ zero rd ⦃(rd ↦ᵣ 0).holdsFor⦄ := by
  intro s hpre
  rw [holdsFor_regIs] at hpre ⊢
  simp only [zero, SUB, single, execProgram, execInstr]
  simp only [MachineState.getReg_setPC]
  rw [MachineState.getReg_setReg_eq _ rd _ hrd]
  simp [hpre, BitVec.sub_self]

end RiscVMacroAsm.Examples
