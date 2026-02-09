/-
  RiscVMacroAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  The `echo_spec` theorem proves end-to-end correctness: given 16+ bytes of
  privateInput, the program reads 16 bytes, writes them to publicValues, and halts.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.SyscallSpecs

namespace RiscVMacroAsm.Examples

open RiscVMacroAsm

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
  pc := 0
  privateInput := [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0]
  publicValues := []

/-- After 11 steps, publicValues = 16 LE bytes (words 1, 2, 3, 4). -/
example : (stepN 11 (loadProgram 0 echo) echoInitState).bind
    (fun s => some s.publicValues) = some [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0] := by
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
-- Echo specification
-- ============================================================================

/-- End-to-end specification for the echo program.
    Given 16+ bytes of private input and 4 words of memory at 0x100,
    the program reads 16 bytes into memory, writes them to public values, and halts.

    The postcondition for publicValues uses the computed byte representation:
    bytesToWords converts the input bytes to LE words, then extractBytes + flatMap
    converts back to bytes. For properly 4-aligned input, this is the identity.

    Registers x5, x10, x11, x12 are used as scratch and have their final HALT values. -/
theorem echo_spec (inputBytes : List (BitVec 8))
    (oldWords : List Word) (v5 v10 v11 v12 : Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let code := loadProgram 0 echo
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple code 0
      ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  let code := loadProgram 0 echo
  -- Address arithmetic
  have h04 : (0 : BitVec 32) + 4 = 4 := by grind
  have h48 : (4 : BitVec 32) + 4 = 8 := by grind
  have h812 : (8 : BitVec 32) + 4 = 12 := by grind
  have h1216 : (12 : BitVec 32) + 4 = 16 := by grind
  have h1620 : (16 : BitVec 32) + 4 = 20 := by grind
  have h2024 : (20 : BitVec 32) + 4 = 24 := by grind
  have h2428 : (24 : BitVec 32) + 4 = 28 := by grind
  have h2832 : (28 : BitVec 32) + 4 = 32 := by grind
  have h3236 : (32 : BitVec 32) + 4 = 36 := by grind
  have h3640 : (36 : BitVec 32) + 4 = 40 := by grind
  have h4044 : (40 : BitVec 32) + 4 = 44 := by grind
  have h4448 : (44 : BitVec 32) + 4 = 48 := by grind

  -- pcFree helpers
  let piPvMb := privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs (0x100 : Addr) oldWords
  have hpiPvMb : piPvMb.pcFree := pcFree_sepConj (pcFree_privateInputIs _)
    (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))

  -- =========================================================================
  -- Phase A: HINT_READ (PC 0 → 16)
  -- 3 LIs (x5=0xF1, x10=0x100, x11=16) + ECALL
  -- =========================================================================

  -- LI x5 0xF1 (PC 0 → 4)
  have a1 : cpsTriple code 0 4 (.x5 ↦ᵣ v5) (.x5 ↦ᵣ 0xF1#32) := by
    have := li_spec_gen code .x5 v5 0xF1 0 (by decide) fetch_0
    simp only [h04] at this; exact this
  have a1f : cpsTriple code 0 4
      ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** piPvMb)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** piPvMb) :=
    cpsTriple_frame_left code 0 4 _ _ _
      (pcFree_sepConj (pcFree_regIs .x10 _) (pcFree_sepConj (pcFree_regIs .x11 _)
        (pcFree_sepConj (pcFree_regIs .x12 _) hpiPvMb))) a1

  -- LI x10 0x100 (PC 4 → 8)
  have a2 : cpsTriple code 4 8 (.x10 ↦ᵣ v10) (.x10 ↦ᵣ 0x100#32) := by
    have := li_spec_gen code .x10 v10 0x100 4 (by decide) fetch_1
    simp only [h48] at this; exact this
  have a2f : cpsTriple code 4 8
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** piPvMb)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** piPvMb) :=
    cpsTriple_frame_right code 4 8 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_left code 4 8 _ _ _
        (pcFree_sepConj (pcFree_regIs .x11 _) (pcFree_sepConj (pcFree_regIs .x12 _) hpiPvMb)) a2)

  -- LI x11 16 (PC 8 → 12)
  have a3 : cpsTriple code 8 12 (.x11 ↦ᵣ v11) (.x11 ↦ᵣ 16#32) := by
    have := li_spec_gen code .x11 v11 16 8 (by decide) fetch_2
    simp only [h812] at this; exact this
  have a3f : cpsTriple code 8 12
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) ** piPvMb)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) ** piPvMb) :=
    cpsTriple_frame_right code 8 12 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code 8 12 _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_left code 8 12 _ _ _
          (pcFree_sepConj (pcFree_regIs .x12 _) hpiPvMb) a3))

  -- ECALL HINT_READ (PC 12 → 16)
  -- We need to rearrange the precondition to match ecall_hint_read_spec_gen
  -- Pre: x5=0xF1 ** x10=0x100 ** x11=16 ** x12 ** piPvMb
  -- piPvMb = privateInputIs ** publicValuesIs ** memBufferIs
  -- ecall_hint_read_spec_gen wants:
  --   x5=0xF1 ** x10=bufAddr ** x11=nbytes ** privateInputIs ** memBufferIs
  -- So we need to rearrange x12 and publicValuesIs into the frame

  -- First build the ECALL hint_read spec at base
  have a4_core : cpsTriple code 12 16
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) **
       privateInputIs inputBytes ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) **
       privateInputIs (inputBytes.drop 16) **
       memBufferIs 0x100 (bytesToWords (inputBytes.take 16))) := by
    have := ecall_hint_read_spec_gen code 0x100 16 inputBytes oldWords 12 fetch_3
      (by simp; omega) (by simp; omega)
    simp only [h1216] at this; exact this

  -- Now embed x12 and publicValuesIs as frame
  have a4f : cpsTriple code 12 16
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs oldPV ** memBufferIs 0x100 (bytesToWords (inputBytes.take 16))) := by
    -- Frame = x12 ** pv; use frame_left then consequence to rearrange
    have a4_framed := cpsTriple_frame_left code 12 16 _ _ ((.x12 ↦ᵣ v12) ** publicValuesIs oldPV)
      (pcFree_sepConj (pcFree_regIs .x12 _) (pcFree_publicValuesIs _)) a4_core
    -- a4_framed : cpsTriple code 12 16
    --   ((x5 ** x10 ** x11 ** pi ** mb) ** (x12 ** pv))
    --   ((x5 ** x10 ** x11 ** pi' ** mb') ** (x12 ** pv))
    -- Need to rearrange both pre and post to the 7-part flat form
    exact cpsTriple_consequence code 12 16 _ _ _ _
      (fun h => by simp only [sepConj_comm', sepConj_left_comm']; exact id)
      (fun h => by simp only [sepConj_comm', sepConj_left_comm']; exact id)
      a4_framed

  -- Chain Phase A
  have phaseA : cpsTriple code 0 16
      ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x12 ↦ᵣ v12) **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs oldPV ** memBufferIs 0x100 (bytesToWords (inputBytes.take 16))) :=
    cpsTriple_seq code 0 12 16 _ _ _
      (cpsTriple_seq code 0 8 12 _ _ _
        (cpsTriple_seq code 0 4 8 _ _ _ a1f a2f) a3f) a4f

  -- =========================================================================
  -- Phase B: WRITE (PC 16 → 36)
  -- 4 LIs (x5=0x02, x10=13, x11=0x100, x12=16) + ECALL
  -- =========================================================================

  let newWords := bytesToWords (inputBytes.take 16)
  let piDrop := privateInputIs (inputBytes.drop 16)
  let pvOld := publicValuesIs oldPV
  let mbNew := memBufferIs (0x100 : Addr) newWords

  have hpiDrop : piDrop.pcFree := pcFree_privateInputIs _
  have hpvOld : pvOld.pcFree := pcFree_publicValuesIs _
  have hmbNew : mbNew.pcFree := pcFree_memBufferIs _ _

  -- LI x5 0x02 (PC 16 → 20)
  have b1 : cpsTriple code 16 20 (.x5 ↦ᵣ 0xF1#32) (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) := by
    have := li_spec_gen code .x5 0xF1#32 (BitVec.ofNat 32 0x02) 16 (by decide) fetch_4
    simp only [h1620] at this; exact this
  have b1f : cpsTriple code 16 20
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew) :=
    cpsTriple_frame_left code 16 20 _ _ _
      (pcFree_sepConj (pcFree_regIs .x10 _) (pcFree_sepConj (pcFree_regIs .x11 _)
        (pcFree_sepConj (pcFree_regIs .x12 _)
          (pcFree_sepConj hpiDrop (pcFree_sepConj hpvOld hmbNew))))) b1

  -- LI x10 13 (PC 20 → 24)
  have b2 : cpsTriple code 20 24 (.x10 ↦ᵣ 0x100#32) (.x10 ↦ᵣ (13 : Word)) := by
    have := li_spec_gen code .x10 0x100#32 13 20 (by decide) fetch_5
    simp only [h2024] at this; exact this
  have b2f : cpsTriple code 20 24
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew) :=
    cpsTriple_frame_right code 20 24 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_left code 20 24 _ _ _
        (pcFree_sepConj (pcFree_regIs .x11 _) (pcFree_sepConj (pcFree_regIs .x12 _)
          (pcFree_sepConj hpiDrop (pcFree_sepConj hpvOld hmbNew)))) b2)

  -- LI x11 0x100 (PC 24 → 28)
  have b3 : cpsTriple code 24 28 (.x11 ↦ᵣ 16#32) (.x11 ↦ᵣ 0x100#32) := by
    have := li_spec_gen code .x11 16#32 0x100 24 (by decide) fetch_6
    simp only [h2428] at this; exact this
  have b3f : cpsTriple code 24 28
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew) :=
    cpsTriple_frame_right code 24 28 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code 24 28 _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_left code 24 28 _ _ _
          (pcFree_sepConj (pcFree_regIs .x12 _)
            (pcFree_sepConj hpiDrop (pcFree_sepConj hpvOld hmbNew))) b3))

  -- LI x12 16 (PC 28 → 32)
  have b4 : cpsTriple code 28 32 (.x12 ↦ᵣ v12) (.x12 ↦ᵣ 16#32) := by
    have := li_spec_gen code .x12 v12 16 28 (by decide) fetch_7
    simp only [h2832] at this; exact this
  have b4f : cpsTriple code 28 32
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop ** pvOld ** mbNew) :=
    cpsTriple_frame_right code 28 32 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code 28 32 _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_right code 28 32 _ _ (.x11 ↦ᵣ _) (pcFree_regIs .x11 _)
          (cpsTriple_frame_left code 28 32 _ _ _
            (pcFree_sepConj hpiDrop (pcFree_sepConj hpvOld hmbNew)) b4)))

  -- ECALL WRITE (PC 32 → 36)
  -- ecall_write_public_spec_gen needs:
  --   x5=0x02 ** x10=13 ** x11=bufPtr ** x12=nbytes ** publicValuesIs ** memBufferIs
  -- We have: x5=0x02 ** x10=13 ** x11=0x100 ** x12=16 ** piDrop ** pvOld ** mbNew
  -- Need to rearrange piDrop out to frame, and pull pvOld/mbNew into position 5,6
  have b5_core : cpsTriple code 32 36
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       publicValuesIs oldPV ** memBufferIs 0x100 newWords)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       publicValuesIs (oldPV ++ (newWords.flatMap
         (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take 16) **
       memBufferIs 0x100 newWords) := by
    have := ecall_write_public_spec_gen code 0x100 16 oldPV newWords 32 fetch_8
      (by
        show 16 ≤ 4 * newWords.length
        have htake_len : (inputBytes.take 16).length = 16 := by
          rw [List.length_take]; omega
        have h4div : 4 ∣ (inputBytes.take 16).length := ⟨4, by rw [htake_len]⟩
        have hbtwl := bytesToWords_length (inputBytes.take 16) h4div
        rw [htake_len] at hbtwl
        show 16 ≤ 4 * (bytesToWords (inputBytes.take 16)).length
        omega)
      (by native_decide)
    simp only [h3236] at this; exact this

  -- Embed piDrop as frame
  have b5f : cpsTriple code 32 36
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop **
       publicValuesIs (oldPV ++ (newWords.flatMap
         (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take 16) **
       memBufferIs 0x100 newWords) := by
    -- Frame = piDrop; use frame_left then consequence to rearrange
    have b5_framed := cpsTriple_frame_left code 32 36 _ _ piDrop hpiDrop b5_core
    exact cpsTriple_consequence code 32 36 _ _ _ _
      (fun h => by simp only [sepConj_comm', sepConj_left_comm']; exact id)
      (fun h => by simp only [sepConj_comm', sepConj_left_comm']; exact id)
      b5_framed

  -- Chain Phase B
  have phaseB : cpsTriple code 16 36
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ 0x100#32) ** (.x11 ↦ᵣ 16#32) ** (.x12 ↦ᵣ v12) **
       piDrop ** pvOld ** mbNew)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop **
       publicValuesIs (oldPV ++ (newWords.flatMap
         (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take 16) **
       memBufferIs 0x100 newWords) :=
    cpsTriple_seq code 16 32 36 _ _ _
      (cpsTriple_seq code 16 28 32 _ _ _
        (cpsTriple_seq code 16 24 28 _ _ _
          (cpsTriple_seq code 16 20 24 _ _ _ b1f b2f) b3f) b4f) b5f

  -- =========================================================================
  -- Phase C: HALT (PC 36 → halts)
  -- 2 LIs (x5=0, x10=0) + ECALL
  -- =========================================================================

  let newBytesFlat := newWords.flatMap
    (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
  let piDrop' := privateInputIs (inputBytes.drop 16)
  let pvNew := publicValuesIs (oldPV ++ newBytesFlat.take 16)
  let mbNew' := memBufferIs (0x100 : Addr) newWords

  have hpiDrop' : piDrop'.pcFree := pcFree_privateInputIs _
  have hpvNew : pvNew.pcFree := pcFree_publicValuesIs _
  have hmbNew' : mbNew'.pcFree := pcFree_memBufferIs _ _

  -- LI x5 0 (PC 36 → 40)
  have c1 : cpsTriple code 36 40 (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) (.x5 ↦ᵣ (0 : Word)) := by
    have := li_spec_gen code .x5 (BitVec.ofNat 32 0x02) 0 36 (by decide) fetch_9
    simp only [h3640] at this; exact this
  have c1f : cpsTriple code 36 40
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew')
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew') :=
    cpsTriple_frame_left code 36 40 _ _ _
      (pcFree_sepConj (pcFree_regIs .x10 _) (pcFree_sepConj (pcFree_regIs .x11 _)
        (pcFree_sepConj (pcFree_regIs .x12 _)
          (pcFree_sepConj hpiDrop' (pcFree_sepConj hpvNew hmbNew'))))) c1

  -- LI x10 0 (PC 40 → 44)
  have c2 : cpsTriple code 40 44 (.x10 ↦ᵣ (13 : Word)) (.x10 ↦ᵣ (0 : Word)) := by
    have := li_spec_gen code .x10 (13 : Word) 0 40 (by decide) fetch_10
    simp only [h4044] at this; exact this
  have c2f : cpsTriple code 40 44
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew')
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew') :=
    cpsTriple_frame_right code 40 44 _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_left code 40 44 _ _ _
        (pcFree_sepConj (pcFree_regIs .x11 _) (pcFree_sepConj (pcFree_regIs .x12 _)
          (pcFree_sepConj hpiDrop' (pcFree_sepConj hpvNew hmbNew')))) c2)

  -- ECALL HALT (PC 44, halts)
  -- ecall_halt_spec_gen needs x5=0 ** x10=exitCode
  -- We have x5=0 ** x10=0 ** rest
  have c3_core : cpsHaltTriple code 44
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word))) :=
    ecall_halt_spec_gen code 0 44 fetch_11

  have c3_framed : cpsHaltTriple code 44
      (((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word))) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew')
      (((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word))) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew') :=
    cpsHaltTriple_frame_left code 44 _ _ _
      (pcFree_sepConj (pcFree_regIs .x11 _) (pcFree_sepConj (pcFree_regIs .x12 _)
        (pcFree_sepConj hpiDrop' (pcFree_sepConj hpvNew hmbNew')))) c3_core
  have c3f : cpsHaltTriple code 44
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew')
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew') :=
    cpsHaltTriple_consequence code 44 _ _ _ _
      (fun h => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm']; exact id)
      (fun h => by simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm']; exact id)
      c3_framed

  -- Chain Phase C
  have phaseC : cpsHaltTriple code 36
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew')
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
       (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       piDrop' ** pvNew ** mbNew') :=
    cpsTriple_seq_halt code 36 44 _ _ _
      (cpsTriple_seq code 36 40 44 _ _ _ c1f c2f) c3f

  -- =========================================================================
  -- Compose all three phases: A → B → C (halt)
  -- =========================================================================

  -- Chain AB: A seq B
  have phaseAB := cpsTriple_seq code 0 16 36 _ _ _ phaseA phaseB

  -- Chain ABC: AB seq_halt C
  exact cpsTriple_seq_halt code 0 36 _ _ _ phaseAB phaseC

/-- Echo with regOwn (no old register values needed).

    Same as echo_spec but the precondition uses regOwn for the 4 scratch registers
    instead of requiring specific old values v5, v10, v11, v12. -/
theorem echo_spec_own (inputBytes : List (BitVec 8))
    (oldWords : List Word)
    (oldPV : List (BitVec 8))
    (hInputLen : 16 ≤ inputBytes.length)
    (hOldWords : oldWords.length = 4) :
    let code := loadProgram 0 echo
    let newWords := bytesToWords (inputBytes.take 16)
    let newBytesFlat := newWords.flatMap
      (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])
    cpsHaltTriple code 0
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       privateInputIs inputBytes ** publicValuesIs oldPV ** memBufferIs 0x100 oldWords)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100#32) ** (.x12 ↦ᵣ 16#32) **
       privateInputIs (inputBytes.drop 16) **
       publicValuesIs (oldPV ++ newBytesFlat.take 16) **
       memBufferIs 0x100 newWords) := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h_inner, h_R, hdisj, hunion, hInner, hRest⟩ := hPR
  obtain ⟨h1, hr1, hd1, hu1, ⟨v5, hv5⟩, hrest1⟩ := hInner
  obtain ⟨h2, hr2, hd2, hu2, ⟨v10, hv10⟩, hrest2⟩ := hrest1
  obtain ⟨h3, hr3, hd3, hu3, ⟨v11, hv11⟩, hrest3⟩ := hrest2
  obtain ⟨h4, hr4, hd4, hu4, ⟨v12, hv12⟩, hrest4⟩ := hrest3
  exact echo_spec inputBytes oldWords v5 v10 v11 v12 oldPV hInputLen hOldWords R hR s
    ⟨hp, hcompat, h_inner, h_R, hdisj, hunion,
      ⟨h1, hr1, hd1, hu1, hv5,
        ⟨h2, hr2, hd2, hu2, hv10,
          ⟨h3, hr3, hd3, hu3, hv11,
            ⟨h4, hr4, hd4, hu4, hv12, hrest4⟩⟩⟩⟩, hRest⟩ hpc

end RiscVMacroAsm.Examples
