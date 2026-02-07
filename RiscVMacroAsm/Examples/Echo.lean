/-
  RiscVMacroAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  This example demonstrates the compositional proof pattern:
  prove specs for individual instructions, then compose using cpsTriple_seq.

  NOTE: The proofs use `liftPred` which claims full-state ownership via `fullState`,
  making frame reconstruction incompatible with the frame-quantified cpsTriple.
  These proofs need to be rewritten using proper separation logic assertions
  (privateInputIs, publicValuesIs, regIs, memIs) to eliminate the sorries.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- Echo program definition
-- ============================================================================

/-- Echo program: read 4 words from privateInput → mem[0x100..0x10C],
    then write them to publicValues, then halt. -/
def echo : Program :=
  HINT_READ 0x100 16 ;;   -- Read 4 words from privateInput → mem[0x100..0x10C]
  WRITE 13 0x100 16 ;;    -- Write 4 words from mem[0x100..0x10C] → publicValues
  HALT 0                   -- Halt

-- ============================================================================
-- Smoke tests (concrete execution)
-- ============================================================================

/-- The echo program is 12 instructions long. -/
example : echo.length = 12 := by native_decide

/-- A concrete initial state for smoke tests. -/
def echoInitState : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0
  privateInput := [1, 2, 3, 4]
  publicValues := []

/-- After 11 steps, publicValues = [1, 2, 3, 4]. -/
example : (stepN 11 (loadProgram 0 echo) echoInitState).bind
    (fun s => some s.publicValues) = some [1, 2, 3, 4] := by
  native_decide

/-- After 11 steps, privateInput is consumed. -/
example : (stepN 11 (loadProgram 0 echo) echoInitState).bind
    (fun s => some s.privateInput) = some [] := by
  native_decide

/-- After 11 steps, the next step is HALT (returns none). -/
example : ((stepN 11 (loadProgram 0 echo) echoInitState).bind
    (fun s => step (loadProgram 0 echo) s)).isNone = true := by
  native_decide

-- ============================================================================
-- Instruction fetch lemmas
-- ============================================================================

private theorem fetch_0 : loadProgram 0 echo 0 = some (Instr.LI .x5 0xF1) := by native_decide
private theorem fetch_1 : loadProgram 0 echo 4 = some (Instr.LI .x10 0x100) := by native_decide
private theorem fetch_2 : loadProgram 0 echo 8 = some (Instr.LI .x11 16) := by native_decide
private theorem fetch_3 : loadProgram 0 echo 12 = some .ECALL := by native_decide
private theorem fetch_4 : loadProgram 0 echo 16 = some (Instr.LI .x5 0x02) := by native_decide
private theorem fetch_5 : loadProgram 0 echo 20 = some (Instr.LI .x10 13) := by native_decide
private theorem fetch_6 : loadProgram 0 echo 24 = some (Instr.LI .x11 0x100) := by native_decide
private theorem fetch_7 : loadProgram 0 echo 28 = some (Instr.LI .x12 16) := by native_decide
private theorem fetch_8 : loadProgram 0 echo 32 = some .ECALL := by native_decide
private theorem fetch_9 : loadProgram 0 echo 36 = some (Instr.LI .x5 0) := by native_decide
private theorem fetch_10 : loadProgram 0 echo 40 = some (Instr.LI .x10 0) := by native_decide
private theorem fetch_11 : loadProgram 0 echo 44 = some .ECALL := by native_decide

-- ============================================================================
-- Phase A: HINT_READ setup and execution
-- ============================================================================

/-- After setting up x5, x10, x11 for HINT_READ. -/
private def hintReadReady (pi : List Word) (pv : List Word) (s : MachineState) : Prop :=
  s.getReg .x5 = 0xF1 ∧
  s.getReg .x10 = 0x100 ∧
  s.getReg .x11 = 16 ∧
  s.privateInput =pi ∧
  s.publicValues = pv

/-- After HINT_READ completes: memory loaded, privateInput consumed. -/
private def hintReadDone (w0 w1 w2 w3 : Word) (s : MachineState) : Prop :=
  s.getMem 0x100 = w0 ∧
  s.getMem 0x104 = w1 ∧
  s.getMem 0x108 = w2 ∧
  s.getMem 0x10C = w3 ∧
  s.privateInput =[] ∧
  s.publicValues = []

end RiscVMacroAsm.Examples
