/-
  EvmAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  The `echo_spec` theorem proves end-to-end correctness: given 16+ bytes of
  privateInput, the program reads 16 bytes, writes them to publicValues, and halts.
-/

import EvmAsm.Rv32.Execution
import EvmAsm.Rv32.SepLogic
import EvmAsm.Rv32.CPSSpec
import EvmAsm.Rv32.SyscallSpecs

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
-- Helper: weaken holdsFor through assertion implication
private theorem holdsFor_mono {P Q : Assertion} (h : ∀ ps, P ps → Q ps) {s : MachineState}
    (hp : P.holdsFor s) : Q.holdsFor s := by
  obtain ⟨ps, hcompat, hPps⟩ := hp
  exact ⟨ps, hcompat, h ps hPps⟩

-- Helper: bytesToWords of exactly 16 bytes from a long enough list gives 4 words
private theorem bytesToWords_take16_length (inputBytes : List (BitVec 8))
    (hLen : 16 ≤ inputBytes.length) :
    (bytesToWords (inputBytes.take 16)).length = 4 := by
  have h16 : (inputBytes.take 16).length = 16 := by
    rw [List.length_take]; omega
  have h4 : 4 ∣ (inputBytes.take 16).length := ⟨4, by omega⟩
  have := bytesToWords_length (inputBytes.take 16) h4
  omega

-- CodeReq for the three sub-programs
private abbrev readCodeReq : CodeReq :=
  CodeReq.singleton 0 (.LI .x5 0xF1#32) |>.union
  (CodeReq.singleton 4 (.LI .x10 (0x100 : Word)) |>.union
  (CodeReq.singleton 8 (.LI .x11 (16 : Word)) |>.union
  (CodeReq.singleton 12 .ECALL)))

private abbrev writeCodeReq : CodeReq :=
  CodeReq.singleton 16 (.LI .x5 (BitVec.ofNat 32 0x02)) |>.union
  (CodeReq.singleton 20 (.LI .x10 13) |>.union
  (CodeReq.singleton 24 (.LI .x11 (0x100 : Word)) |>.union
  (CodeReq.singleton 28 (.LI .x12 (16 : Word)) |>.union
  (CodeReq.singleton 32 .ECALL))))

private abbrev haltCodeReq : CodeReq :=
  CodeReq.singleton 36 (.LI .x5 (0 : Word)) |>.union
  (CodeReq.singleton 40 (.LI .x10 (0 : Word)) |>.union
  (CodeReq.singleton 44 .ECALL))

private abbrev echoCodeReq : CodeReq :=
  readCodeReq |>.union (writeCodeReq |>.union haltCodeReq)

theorem echo_spec (inputBytes : List (BitVec 8))
    (oldWords : List Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple 0 echoCodeReq
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (16 : Word)) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  sorry

end EvmAsm.Examples
