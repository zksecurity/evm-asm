/-
  EvmAsm.Examples.Zero

  A zero-register macro and a CPS-style Hoare triple.
-/

import EvmAsm.Execution
import EvmAsm.SepLogic
import EvmAsm.CPSSpec
import EvmAsm.ControlFlow

namespace EvmAsm.Examples

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
    cpsTriple base (base + 4)
      (rd ↦ᵣ v)
      (rd ↦ᵣ 0) := by
  sorry

end EvmAsm.Examples
