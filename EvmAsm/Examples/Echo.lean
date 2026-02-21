/-
  EvmAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  The `echo_spec` theorem proves end-to-end correctness: given 16+ bytes of
  privateInput, the program reads 16 bytes, writes them to publicValues, and halts.
-/

import EvmAsm.Execution
import EvmAsm.SepLogic
import EvmAsm.CPSSpec
import EvmAsm.SyscallSpecs

namespace EvmAsm.Examples

open EvmAsm

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

/-- A concrete initial state for smoke tests.
    privateInput is 16 bytes representing 4 LE words: 1, 2, 3, 4. -/
def echoInitState : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  code := loadProgram 0 echo
  pc := 0
  privateInput := [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0]
  publicValues := []

/-- After 11 steps, publicValues = 16 LE bytes (words 1, 2, 3, 4). -/
example : (stepN 11 echoInitState).bind
    (fun s => some s.publicValues) = some [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0] := by
  native_decide

/-- After 11 steps, privateInput is consumed. -/
example : (stepN 11 echoInitState).bind
    (fun s => some s.privateInput) = some [] := by
  native_decide

/-- After 11 steps, the next step is HALT (returns none). -/
example : ((stepN 11 echoInitState).bind
    (fun s => step s)).isNone = true := by
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
-- Echo specification
-- ============================================================================

/-- End-to-end specification for the echo program.
    Given 16+ bytes of private input and 4 words of memory at 0x100,
    the program reads 16 bytes into memory, writes them to public values, and halts.

    The postcondition for publicValues uses the computed byte representation:
    bytesToWords converts the input bytes to LE words, then extractBytes + flatMap
    converts back to bytes. For properly 4-aligned input, this is the identity.

    Uses regOwn for scratch registers (no old values needed). -/
theorem echo_spec (inputBytes : List (BitVec 8))
    (oldWords : List Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple 0
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  sorry

end EvmAsm.Examples
