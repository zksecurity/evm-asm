/-
  RiscVMacroAsm.Examples.Echo

  An "echo" program that reads 4 words from privateInput via HINT_READ
  and writes them to publicValues via WRITE, demonstrating the
  read-then-write I/O pipeline with a compositional CPS specification.

  This example demonstrates the compositional proof pattern:
  prove specs for individual instructions, then compose using cpsTriple_seq.
-/

import RiscVMacroAsm.Execution
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

/-- Step 0: LI x5 0xF1 at PC=0. -/
private theorem step0_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 0 4
      (fun s => s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = [])
      (fun s => s.getReg .x5 = 0xF1 ∧ s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = []) := by
  intro s ⟨hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x5 0xF1).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_0) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x5 0xF1).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 4
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0xF1
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · show s'.privateInput = [w0, w1, w2, w3]
      simp only [s', MachineState.setPC, MachineState.setReg, hpi]
    · show s'.publicValues = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpv]

/-- Step 1: LI x10 0x100 at PC=4. -/
private theorem step1_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 4 8
      (fun s => s.getReg .x5 = 0xF1 ∧ s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = [])
      (fun s => s.getReg .x5 = 0xF1 ∧ s.getReg .x10 = 0x100 ∧
                s.privateInput =[w0, w1, w2, w3] ∧ s.publicValues = []) := by
  intro s ⟨h5, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x10 0x100).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_1) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x10 0x100).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 8
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0xF1
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.getReg .x10 = 0x100
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · show s'.privateInput = [w0, w1, w2, w3]
      simp only [s', MachineState.setPC, MachineState.setReg, hpi]
    · show s'.publicValues = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpv]

/-- Step 2: LI x11 16 at PC=8. -/
private theorem step2_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 8 12
      (fun s => s.getReg .x5 = 0xF1 ∧ s.getReg .x10 = 0x100 ∧
                s.privateInput =[w0, w1, w2, w3] ∧ s.publicValues = [])
      (hintReadReady [w0, w1, w2, w3] []) := by
  intro s ⟨h5, h10, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x11 16).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_2) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x11 16).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 12
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · unfold hintReadReady
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0xF1
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.getReg .x10 = 0x100
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h10
    · show s'.getReg .x11 = 16
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · show s'.privateInput = [w0, w1, w2, w3]
      simp only [s', MachineState.setPC, MachineState.setReg, hpi]
    · show s'.publicValues = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpv]

/-- Step 3: ECALL HINT_READ at PC=12. -/
private theorem step3_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 12 16
      (hintReadReady [w0, w1, w2, w3] [])
      (hintReadDone w0 w1 w2 w3) := by
  intro s ⟨h5, h10, h11, hpi, hpv⟩ hpc
  -- HINT_READ: nwords = 16/4 = 4, reads [w0,w1,w2,w3], writes to 0x100
  have hsuff : (s.getReg .x11).toNat / 4 ≤ s.privateInput.length := by
    simp [h11, hpi]
  have hs : step (loadProgram 0 echo) s =
      let nwords := 4
      let words := [w0, w1, w2, w3]
      let s' := { s with privateInput := [] }
      some ((s'.writeWords (s.getReg .x10) words).setPC (s.pc + 4)) := by
    rw [step_ecall_hint_read _ _ (by rw [hpc]; exact fetch_3) h5 hsuff]
    simp [h11, h10, hpi]
  let nwords := 4
  let words := [w0, w1, w2, w3]
  let s' := { s with privateInput := [] }
  let sfinal := ((s'.writeWords (s.getReg .x10) words).setPC (s.pc + 4))
  refine ⟨1, sfinal, ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show sfinal.pc = 16
    simp only [sfinal, MachineState.setPC, hpc]
    decide
  · unfold hintReadDone
    simp only [sfinal, s', words, h10, hpv]
    simp [MachineState.getMem, MachineState.writeWords, MachineState.setMem, MachineState.setPC]

/-- Phase A: Compose steps 0-3 for HINT_READ. -/
private theorem phaseA (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 0 16
      (fun s => s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = [])
      (hintReadDone w0 w1 w2 w3) :=
  cpsTriple_seq _ _ _ _ _ _ _
    (cpsTriple_seq _ _ _ _ _ _ _
      (cpsTriple_seq _ _ _ _ _ _ _
        (step0_spec w0 w1 w2 w3)
        (step1_spec w0 w1 w2 w3))
      (step2_spec w0 w1 w2 w3))
    (step3_spec w0 w1 w2 w3)

-- ============================================================================
-- Phase B: WRITE setup and execution
-- ============================================================================

/-- After setting up x5, x10, x11, x12 for WRITE. -/
private def writeReady (w0 w1 w2 w3 : Word) (s : MachineState) : Prop :=
  s.getReg .x5 = 0x02 ∧
  s.getReg .x10 = 13 ∧
  s.getReg .x11 = 0x100 ∧
  s.getReg .x12 = 16 ∧
  s.getMem 0x100 = w0 ∧
  s.getMem 0x104 = w1 ∧
  s.getMem 0x108 = w2 ∧
  s.getMem 0x10C = w3 ∧
  s.privateInput =[] ∧
  s.publicValues = []

/-- After WRITE completes: publicValues populated. -/
private def writeDone (w0 w1 w2 w3 : Word) (s : MachineState) : Prop :=
  s.publicValues = [w0, w1, w2, w3] ∧
  s.privateInput =[]

/-- Step 4: LI x5 0x02 at PC=16. -/
private theorem step4_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 16 20
      (hintReadDone w0 w1 w2 w3)
      (fun s => s.getReg .x5 = 0x02 ∧ hintReadDone w0 w1 w2 w3 s) := by
  intro s ⟨hm0, hm1, hm2, hm3, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x5 0x02).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_4) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x5 0x02).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 20
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_⟩
    · show s'.getReg .x5 = 0x02
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · unfold hintReadDone MachineState.getMem at *
      simp_all [s', MachineState.setPC, MachineState.setReg]

/-- Step 5: LI x10 13 at PC=20. -/
private theorem step5_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 20 24
      (fun s => s.getReg .x5 = 0x02 ∧ hintReadDone w0 w1 w2 w3 s)
      (fun s => s.getReg .x5 = 0x02 ∧ s.getReg .x10 = 13 ∧ hintReadDone w0 w1 w2 w3 s) := by
  intro s ⟨h5, hm0, hm1, hm2, hm3, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x10 13).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_5) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x10 13).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 24
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0x02
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.getReg .x10 = 13
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · unfold hintReadDone MachineState.getMem at *
      simp_all [s', MachineState.setPC, MachineState.setReg]

/-- Step 6: LI x11 0x100 at PC=24. -/
private theorem step6_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 24 28
      (fun s => s.getReg .x5 = 0x02 ∧ s.getReg .x10 = 13 ∧ hintReadDone w0 w1 w2 w3 s)
      (fun s => s.getReg .x5 = 0x02 ∧ s.getReg .x10 = 13 ∧ s.getReg .x11 = 0x100 ∧
                hintReadDone w0 w1 w2 w3 s) := by
  intro s ⟨h5, h10, hm0, hm1, hm2, hm3, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x11 0x100).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_6) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x11 0x100).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 28
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0x02
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.getReg .x10 = 13
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h10
    · show s'.getReg .x11 = 0x100
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · unfold hintReadDone MachineState.getMem at *
      simp_all [s', MachineState.setPC, MachineState.setReg]

/-- Step 7: LI x12 16 at PC=28. -/
private theorem step7_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 28 32
      (fun s => s.getReg .x5 = 0x02 ∧ s.getReg .x10 = 13 ∧ s.getReg .x11 = 0x100 ∧
                hintReadDone w0 w1 w2 w3 s)
      (writeReady w0 w1 w2 w3) := by
  intro s ⟨h5, h10, h11, hm0, hm1, hm2, hm3, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x12 16).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_7) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x12 16).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 32
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · unfold writeReady
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0x02
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.getReg .x10 = 13
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h10
    · show s'.getReg .x11 = 0x100
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h11
    · show s'.getReg .x12 = 16
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · show s'.getMem 0x100 = w0
      simp only [s', MachineState.getMem, MachineState.setPC, MachineState.setReg]
      exact hm0
    · show s'.getMem 0x104 = w1
      simp only [s', MachineState.getMem, MachineState.setPC, MachineState.setReg]
      exact hm1
    · show s'.getMem 0x108 = w2
      simp only [s', MachineState.getMem, MachineState.setPC, MachineState.setReg]
      exact hm2
    · show s'.getMem 0x10C = w3
      simp only [s', MachineState.getMem, MachineState.setPC, MachineState.setReg]
      exact hm3
    · show s'.privateInput = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpi]
    · show s'.publicValues = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpv]

/-- Step 8: ECALL WRITE at PC=32. -/
private theorem step8_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 32 36
      (writeReady w0 w1 w2 w3)
      (writeDone w0 w1 w2 w3) := by
  intro s ⟨h5, h10, h11, h12, hm0, hm1, hm2, hm3, hpi, hpv⟩ hpc
  have hs : step (loadProgram 0 echo) s =
      some ((s.appendPublicValues (s.readWords (s.getReg .x11) ((s.getReg .x12).toNat / 4))).setPC (s.pc + 4)) := by
    rw [step_ecall_write_public _ _ (by rw [hpc]; exact fetch_8) h5 h10]
  let s' := ((s.appendPublicValues (s.readWords (s.getReg .x11) ((s.getReg .x12).toNat / 4))).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 36
    simp only [s', MachineState.setPC, MachineState.appendPublicValues, hpc]
    decide
  · unfold writeDone
    constructor
    · simp [s', h11, h12, hpv, MachineState.appendPublicValues, MachineState.readWords, MachineState.setPC, MachineState.getMem]
      unfold MachineState.getMem at hm0 hm1 hm2 hm3
      exact ⟨hm0, hm1, hm2, hm3⟩
    · simp only [s', MachineState.appendPublicValues, MachineState.setPC]
      exact hpi

/-- Phase B: Compose steps 4-8 for WRITE. -/
private theorem phaseB (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 16 36
      (hintReadDone w0 w1 w2 w3)
      (writeDone w0 w1 w2 w3) :=
  cpsTriple_seq _ _ _ _ _ _ _
    (cpsTriple_seq _ _ _ _ _ _ _
      (cpsTriple_seq _ _ _ _ _ _ _
        (cpsTriple_seq _ _ _ _ _ _ _
          (step4_spec w0 w1 w2 w3)
          (step5_spec w0 w1 w2 w3))
        (step6_spec w0 w1 w2 w3))
      (step7_spec w0 w1 w2 w3))
    (step8_spec w0 w1 w2 w3)

-- ============================================================================
-- Phase C: HALT setup
-- ============================================================================

/-- After HALT setup: ready to halt. -/
private def haltReady (w0 w1 w2 w3 : Word) (s : MachineState) : Prop :=
  s.getReg .x5 = 0 ∧
  s.publicValues = [w0, w1, w2, w3] ∧
  s.privateInput =[]

/-- Step 9: LI x5 0 at PC=36. -/
private theorem step9_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 36 40
      (writeDone w0 w1 w2 w3)
      (fun s => s.getReg .x5 = 0 ∧ writeDone w0 w1 w2 w3 s) := by
  intro s ⟨hpv, hpi⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x5 0).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_9) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x5 0).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 40
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · refine ⟨?_, ?_⟩
    · show s'.getReg .x5 = 0
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
    · unfold writeDone
      simp [s', MachineState.setPC, MachineState.setReg, hpv, hpi]

/-- Step 10: LI x10 0 at PC=40. -/
private theorem step10_spec (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 40 44
      (fun s => s.getReg .x5 = 0 ∧ writeDone w0 w1 w2 w3 s)
      (haltReady w0 w1 w2 w3) := by
  intro s ⟨h5, hpv, hpi⟩ hpc
  have hs : step (loadProgram 0 echo) s = some ((s.setReg .x10 0).setPC (s.pc + 4)) := by
    rw [step_non_ecall_non_mem _ _ _ (by rw [hpc]; exact fetch_10) (by nofun) (by nofun) rfl]; rfl
  let s' := ((s.setReg .x10 0).setPC (s.pc + 4))
  refine ⟨1, s', ?_, ?_, ?_⟩
  · rw [stepN_one, hs]
  · show s'.pc = 44
    simp only [s', MachineState.setPC, MachineState.setReg, hpc]
    decide
  · unfold haltReady
    refine ⟨?_, ?_, ?_⟩
    · show s'.getReg .x5 = 0
      simp [s', MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact h5
    · show s'.publicValues = [w0, w1, w2, w3]
      simp only [s', MachineState.setPC, MachineState.setReg, hpv]
    · show s'.privateInput = []
      simp only [s', MachineState.setPC, MachineState.setReg, hpi]

/-- Phase C: Compose steps 9-10 for HALT setup. -/
private theorem phaseC (w0 w1 w2 w3 : Word) :
    cpsTriple (loadProgram 0 echo) 36 44
      (writeDone w0 w1 w2 w3)
      (haltReady w0 w1 w2 w3) :=
  cpsTriple_seq _ _ _ _ _ _ _
    (step9_spec w0 w1 w2 w3)
    (step10_spec w0 w1 w2 w3)

-- ============================================================================
-- Halt lemma
-- ============================================================================

private theorem halt_at_44 (w0 w1 w2 w3 : Word) :
    ∀ s, haltReady w0 w1 w2 w3 s → s.pc = 44 →
      isHalted (loadProgram 0 echo) s = true := by
  intro s ⟨h5, _, _⟩ hpc
  unfold isHalted
  rw [step_ecall_halt _ _ (by rw [hpc]; exact fetch_11) h5]; rfl

-- ============================================================================
-- Main specification
-- ============================================================================

/-- Echo correctly reads 4 words from privateInput and writes them to publicValues.
    Compositionally proved by composing individual instruction specs. -/
theorem echo_spec (w0 w1 w2 w3 : Word) :
    cpsHaltTriple (loadProgram 0 echo) 0
      (fun s => s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = [])
      (fun s => s.publicValues = [w0, w1, w2, w3] ∧ s.privateInput = []) := by
  -- Compose all three phases
  have combined : cpsTriple (loadProgram 0 echo) 0 44
      (fun s => s.privateInput = [w0, w1, w2, w3] ∧ s.publicValues = [])
      (haltReady w0 w1 w2 w3) :=
    cpsTriple_seq _ _ _ _ _ _ _
      (cpsTriple_seq _ _ _ _ _ _ _
        (phaseA w0 w1 w2 w3)
        (phaseB w0 w1 w2 w3))
      (phaseC w0 w1 w2 w3)
  -- Convert to halt triple
  have halt_triple := cpsTriple_to_cpsHaltTriple _ _ 44 _ _ combined (halt_at_44 w0 w1 w2 w3)
  -- Weaken postcondition (drop getReg .x5 = 0)
  intro s hs hpc
  obtain ⟨k, s', hstep, hhalt, _, hpv, hpi⟩ := halt_triple s hs hpc
  exact ⟨k, s', hstep, hhalt, hpv, hpi⟩

end RiscVMacroAsm.Examples
