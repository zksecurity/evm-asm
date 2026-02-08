/-
  RiscVMacroAsm.SyscallSpecs

  CPS specifications for the HALT and WRITE macro instructions,
  proved by composing generalized per-instruction specs via structural rules
  (cpsTriple_seq, cpsTriple_seq_halt, frame embedding).
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.ControlFlow

namespace RiscVMacroAsm

-- ============================================================================
-- Section 1: Memory Buffer Assertion
-- ============================================================================

/-- Memory buffer: consecutive words at addr, addr+4, addr+8, ... -/
def memBufferIs : Addr → List Word → Assertion
  | _, [] => empAssertion
  | addr, w :: ws => (addr ↦ₘ w) ** memBufferIs (addr + 4) ws

theorem pcFree_memBufferIs (addr : Addr) (words : List Word) :
    (memBufferIs addr words).pcFree := by
  induction words generalizing addr with
  | nil => exact pcFree_emp
  | cons w ws ih => exact pcFree_sepConj (pcFree_memIs addr w) (ih (addr + 4))

/-- If memBufferIs holds, then readWords returns those words. -/
theorem readWords_of_holdsFor_memBufferIs {addr : Addr} {words : List Word}
    {s : MachineState}
    (h : (memBufferIs addr words).holdsFor s) :
    s.readWords addr words.length = words := by
  induction words generalizing addr with
  | nil => rfl
  | cons w ws ih =>
    simp only [memBufferIs] at h
    have hmem : s.getMem addr = w :=
      (holdsFor_memIs addr w s).mp (holdsFor_sepConj_elim_left h)
    have hrest := holdsFor_sepConj_elim_right h
    simp only [List.length_cons, MachineState.readWords]
    rw [hmem, ih hrest]

-- ============================================================================
-- Section 2: appendPublicValues Infrastructure
-- ============================================================================

namespace PartialState

/-- appendPublicValues preserves compatibility for partial states
    that don't own publicValues. -/
theorem CompatibleWith_appendPublicValues {h : PartialState} {s : MachineState}
    {words : List Word}
    (hcompat : h.CompatibleWith s) (hnone : h.publicValues = none) :
    h.CompatibleWith (s.appendPublicValues words) := by
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => by rw [MachineState.getReg_appendPublicValues]; exact hr r v hv,
         fun a v hv => by rw [MachineState.getMem_appendPublicValues]; exact hm a v hv,
         fun v hv => by rw [MachineState.pc_appendPublicValues]; exact hpc v hv,
         fun v hv => by rw [hnone] at hv; exact absurd hv (by simp),
         fun v hv => by rw [MachineState.privateInput_appendPublicValues]; exact hpi v hv⟩

end PartialState

/-- If (publicValuesIs oldPV ** R).holdsFor s, then
    (publicValuesIs (oldPV ++ words) ** R).holdsFor (s.appendPublicValues words).
    R is automatically publicValues-free by disjointness with publicValuesIs. -/
theorem holdsFor_sepConj_publicValuesIs_appendPublicValues
    {oldPV words : List Word} {R : Assertion} {s : MachineState}
    (hPR : ((publicValuesIs oldPV) ** R).holdsFor s) :
    ((publicValuesIs (oldPV ++ words)) ** R).holdsFor (s.appendPublicValues words) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [publicValuesIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own publicValues (from disjointness)
  have hpv2 : h2.publicValues = none := by
    rcases hdisj.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPublicValues (oldPV ++ words)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, Or.inr hpv2, hdisj.2.2.2.2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPublicValues (oldPV ++ words) compatible with s.appendPublicValues words
  have hc1' : (PartialState.singletonPublicValues (oldPV ++ words)).CompatibleWith
      (s.appendPublicValues words) := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPublicValues] at hr,
            fun a w ha => by simp [PartialState.singletonPublicValues] at ha,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => ?_,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw⟩
    simp only [PartialState.singletonPublicValues] at hw
    rw [Option.some.injEq] at hw; subst hw
    rw [MachineState.publicValues_appendPublicValues]
    exact congrArg (· ++ words)
      ((PartialState.CompatibleWith_singletonPublicValues oldPV s).mp hc1)
  -- h2 compatible with s.appendPublicValues words
  have hc2' : h2.CompatibleWith (s.appendPublicValues words) :=
    PartialState.CompatibleWith_appendPublicValues hc2 hpv2
  exact ⟨(PartialState.singletonPublicValues (oldPV ++ words)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPublicValues (oldPV ++ words), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Section 3: Generalized Instruction Specs
-- ============================================================================

/-- LI spec for any code memory (not just a single-instruction loadProgram). -/
theorem li_spec_gen (code : CodeMem) (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hfetch : code addr = some (Instr.LI rd imm)) :
    cpsTriple code addr (addr + 4) (rd ↦ᵣ v_old) (rd ↦ᵣ imm) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.LI rd imm) := by rw [hpc]; exact hfetch
  have hstep : step code st = some ((st.setReg rd imm).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hpc]
  refine ⟨1, (st.setReg rd imm).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd imm) hR)
      (st.setReg rd imm) (addr + 4)
      (holdsFor_sepConj_regIs_setReg (v' := imm) hrd_ne_x0 hPR)

/-- ECALL halt spec: when x5 = 0, ECALL halts. -/
theorem ecall_halt_spec_gen (code : CodeMem) (exitCode : Word) (addr : Addr)
    (hfetch : code addr = some .ECALL) :
    cpsHaltTriple code addr
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR st hPR hpc
  have hinner := holdsFor_sepConj_elim_left hPR
  have hx5 : st.getReg .x5 = 0 :=
    (holdsFor_regIs .x5 (0 : Word) st).mp (holdsFor_sepConj_elim_left hinner)
  have hhalt : step code st = none :=
    step_ecall_halt code st (by rw [hpc]; exact hfetch) hx5
  exact ⟨0, st, rfl, by simp [isHalted, hhalt], hPR⟩

-- ============================================================================
-- Section 4: Frame Embedding for cpsTriple
-- ============================================================================

/-- Frame on the right: if cpsTriple P → Q, then cpsTriple (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (code : CodeMem) (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hQFR'⟩ := h (F ** R) hFR s hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hQFR'⟩

/-- Frame on the left: if cpsTriple P → Q, then cpsTriple (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (code : CodeMem) (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have h1 := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hQFR⟩ := h (F ** R) hFR s h1 hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hQFR⟩

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (code : CodeMem) (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hQFR'⟩ := h (F ** R) hFR s hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hQFR'⟩

/-- Frame on the left for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_right (code : CodeMem) (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have h1 := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hhalt, hQFR⟩ := h (F ** R) hFR s h1 hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_pull_second.mpr hQFR⟩

-- ============================================================================
-- Section 5: HALT macro specification
-- ============================================================================

/-- HALT exitCode: sets x5 := 0, x10 := exitCode, then halts via ECALL.
    Precondition: own x5 and x10 (old values, to be overwritten).
    Postcondition: x5 = 0, x10 = exitCode, execution halted. -/
theorem halt_spec (exitCode : Word) (v5_old v10_old : Word) (base : Addr) :
    cpsHaltTriple (loadProgram base (HALT exitCode)) base
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  let code := loadProgram base (HALT exitCode)
  -- The HALT macro is [LI x5 0, LI x10 exitCode, ECALL]
  have hprog : HALT exitCode =
      ([Instr.LI .x5 0, Instr.LI .x10 exitCode, Instr.ECALL] : List Instr) := by
    simp [HALT, LI, single, seq, Program]
  -- Instruction fetches
  have hf0 : code base = some (Instr.LI .x5 0) := by
    simp [code, hprog, loadProgram, BitVec.sub_self]
  have hf1 : code (base + 4) = some (Instr.LI .x10 exitCode) := by
    simp only [code]
    rw [hprog,
        show (4 : BitVec 32) = BitVec.ofNat 32 (4 * 1) from by grind]
    rw [loadProgram_at_index base _ 1 (by grind) (by omega)]; rfl
  have hf2 : code (base + 8) = some Instr.ECALL := by
    simp only [code]
    rw [hprog,
        show (8 : BitVec 32) = BitVec.ofNat 32 (4 * 2) from by grind]
    rw [loadProgram_at_index base _ 2 (by grind) (by omega)]; rfl
  -- Step 1: LI x5 0 (base → base+4)
  have s1 : cpsTriple code base (base + 4) (.x5 ↦ᵣ v5_old) (.x5 ↦ᵣ (0 : Word)) :=
    li_spec_gen code .x5 v5_old 0 base (by decide) hf0
  -- Embed x10 in frame: (x5 ** x10) → (x5' ** x10)
  have s1' : cpsTriple code base (base + 4)
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10_old)) :=
    cpsTriple_frame_left code base (base + 4) _ _ _ (pcFree_regIs .x10 v10_old) s1
  -- Step 2: LI x10 exitCode (base+4 → base+8)
  have := li_spec_gen code .x10 v10_old exitCode (base + 4) (by decide) hf1
  have h_four_four : base + 4 + 4 = base + 8 := by grind
  have s2 : cpsTriple code (base + 4) (base + 8) (.x10 ↦ᵣ v10_old) (.x10 ↦ᵣ exitCode) := by
    simp only [h_four_four] at this
    assumption
  -- Embed x5 in frame: (x5 ** x10) → (x5 ** x10')
  have s2' : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ _ (pcFree_regIs .x5 (0 : Word)) s2
  -- Step 3: ECALL halt (base+8, halts)
  have s3 : cpsHaltTriple code (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    ecall_halt_spec_gen code exitCode (base + 8) hf2
  -- Compose: (s1' seq s2') seq_halt s3
  exact cpsTriple_seq_halt code base (base + 8) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1' s2') s3

-- ============================================================================
-- Section 6: ECALL WRITE (public values) specification
-- ============================================================================

/-- Single ECALL step for WRITE to public values (fd = 13).
    Precondition: x5 = 0x02, x10 = 13, x11 = bufPtr, x12 = nbytes,
                  publicValues = oldPV, memory buffer at bufPtr = words.
    Postcondition: same registers, publicValues = oldPV ++ words, memory preserved. -/
theorem ecall_write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (oldPV words : List Word) (addr : Addr)
    (hfetch : code addr = some .ECALL)
    (hlen : words.length = nbytes.toNat / 4) :
    cpsTriple code addr (addr + 4)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words) ** memBufferIs bufPtr words) := by
  intro R hR st hPR hpc
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hx5 : st.getReg .x5 = BitVec.ofNat 32 0x02 :=
    (holdsFor_regIs .x5 _ st).mp (holdsFor_sepConj_elim_left hinner)
  have hx10 : st.getReg .x10 = (13 : Word) :=
    (holdsFor_regIs .x10 _ st).mp
      (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hinner))
  have hx11 : st.getReg .x11 = bufPtr :=
    (holdsFor_regIs .x11 _ st).mp
      (holdsFor_sepConj_elim_left
        (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hinner)))
  have hx12 : st.getReg .x12 = nbytes :=
    (holdsFor_regIs .x12 _ st).mp
      (holdsFor_sepConj_elim_left
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hinner))))
  -- Extract memory buffer values
  have hmem_holds : (memBufferIs bufPtr words).holdsFor st :=
    holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right
        (holdsFor_sepConj_elim_right
          (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hinner))))
  have hread : st.readWords bufPtr words.length = words :=
    readWords_of_holdsFor_memBufferIs hmem_holds
  -- Execute ECALL WRITE
  have hfetch' : code st.pc = some .ECALL := by rw [hpc]; exact hfetch
  have hread' : st.readWords bufPtr (nbytes.toNat / 4) = words := by rw [← hlen]; exact hread
  have hstep : step code st =
      some ((st.appendPublicValues words).setPC (addr + 4)) := by
    rw [step_ecall_write_public code st hfetch' hx5 hx10, hx11, hx12, hpc, hread']
  refine ⟨1, (st.appendPublicValues words).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: pull publicValuesIs to front, update, push back
    -- Forward: use pull_second to move publicValuesIs to front
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_pull_second.mp h2
    have h4 := holdsFor_sepConj_pull_second.mp h3
    have h5 := holdsFor_sepConj_assoc.mp h4
    -- h5 : (publicValuesIs oldPV ** (memBufferIs .. ** rest)).holdsFor st
    -- Update publicValues
    have h6 := holdsFor_sepConj_publicValuesIs_appendPublicValues (words := words) h5
    -- Reverse: push publicValuesIs back to original position
    have h7 := holdsFor_sepConj_assoc.mpr h6
    have h8 := holdsFor_sepConj_pull_second.mpr h7
    have h9 := holdsFor_sepConj_pull_second.mpr h8
    have h10 := holdsFor_sepConj_pull_second.mpr h9
    have h11 := holdsFor_sepConj_pull_second.mpr h10
    -- h11 : ((x5 ** x10 ** x11 ** x12 ** pv' ** mem) ** R).holdsFor (st.appendPublicValues words)
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj
        (pcFree_sepConj (pcFree_regIs .x5 _)
          (pcFree_sepConj (pcFree_regIs .x10 _)
            (pcFree_sepConj (pcFree_regIs .x11 _)
              (pcFree_sepConj (pcFree_regIs .x12 _)
                (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))))
        hR)
      (st.appendPublicValues words) (addr + 4) h11

-- ============================================================================
-- Section 7: WRITE macro specification (fd = 13)
-- ============================================================================

/-- WRITE 13 bufPtr nbytes: sets up registers for WRITE syscall and executes it.
    Reads `nbytes/4` words from memory at bufPtr and appends them to publicValues.

    Precondition: own x5, x10, x11, x12, publicValues = oldPV,
                  memory buffer at bufPtr = words.
    Postcondition: x5 = 0x02, x10 = 13, x11 = bufPtr, x12 = nbytes,
                   publicValues = oldPV ++ words, memory preserved.
    Exit: base + 20 (5 instructions × 4 bytes). -/
theorem write_public_spec (bufPtr nbytes : Word)
    (v5_old v10_old v11_old v12_old : Word)
    (oldPV words : List Word) (base : Addr)
    (hlen : words.length = nbytes.toNat / 4) :
    let code := loadProgram base (WRITE 13 bufPtr nbytes)
    cpsTriple code base (base + 20)
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ v12_old) ** publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words) ** memBufferIs bufPtr words) := by
  simp only
  let code := loadProgram base (WRITE 13 bufPtr nbytes)
  -- The WRITE macro expands to 5 instructions
  have hprog : WRITE 13 bufPtr nbytes =
      ([Instr.LI .x5 (BitVec.ofNat 32 0x02), Instr.LI .x10 13,
        Instr.LI .x11 bufPtr, Instr.LI .x12 nbytes, Instr.ECALL] : List Instr) := by
    simp only [WRITE, LI, single, seq, Program]; rfl
  -- Instruction fetches
  have hf0 : code base = some (Instr.LI .x5 (BitVec.ofNat 32 0x02)) := by
    simp [code, loadProgram, BitVec.sub_self, WRITE, LI, single, seq, Program]
  have hf1 : code (base + 4) = some (Instr.LI .x10 13) := by
    simp only [code]
    rw [hprog, show (4 : BitVec 32) = BitVec.ofNat 32 (4 * 1) from by grind]
    rw [loadProgram_at_index base _ 1 (by grind) (by omega)]; rfl
  have hf2 : code (base + 8) = some (Instr.LI .x11 bufPtr) := by
    simp only [code]
    rw [hprog, show (8 : BitVec 32) = BitVec.ofNat 32 (4 * 2) from by grind]
    rw [loadProgram_at_index base _ 2 (by grind) (by omega)]; rfl
  have hf3 : code (base + 12) = some (Instr.LI .x12 nbytes) := by
    simp only [code]
    rw [hprog, show (12 : BitVec 32) = BitVec.ofNat 32 (4 * 3) from by grind]
    rw [loadProgram_at_index base _ 3 (by grind) (by omega)]; rfl
  have hf4 : code (base + 16) = some Instr.ECALL := by
    simp only [code]
    rw [hprog, show (16 : BitVec 32) = BitVec.ofNat 32 (4 * 4) from by grind]
    rw [loadProgram_at_index base _ 4 (by grind) (by omega)]; rfl
  -- Abbreviation for the "rest" assertion (pv + mem) that stays in the frame during LI steps
  let rest := publicValuesIs oldPV ** memBufferIs bufPtr words
  have hrest_pcfree : rest.pcFree :=
    pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)

  -- Step 1: LI x5, 0x02 (base → base+4)
  have s1 := li_spec_gen code .x5 v5_old (BitVec.ofNat 32 0x02) base (by decide) hf0
  have s1' := cpsTriple_frame_left code base (base + 4) _ _ _
    (pcFree_sepConj (pcFree_regIs .x10 v10_old)
      (pcFree_sepConj (pcFree_regIs .x11 v11_old)
        (pcFree_sepConj (pcFree_regIs .x12 v12_old) hrest_pcfree)))
    s1

  -- Step 2: LI x10, 13 (base+4 → base+8)
  have s2 := li_spec_gen code .x10 v10_old 13 (base + 4) (by decide) hf1
  have h_four_eight : base + 4 + 4 = base + 8 := by grind
  have s2_conv : cpsTriple code (base + 4) (base + 8) (.x10 ↦ᵣ v10_old) (.x10 ↦ᵣ 13) := by
    simp only [h_four_eight] at s2; exact s2
  have s2' := cpsTriple_frame_left code (base + 4) (base + 8) _ _ _
    (pcFree_sepConj (pcFree_regIs .x11 v11_old)
      (pcFree_sepConj (pcFree_regIs .x12 v12_old) hrest_pcfree))
    s2_conv
  have s2'' := cpsTriple_frame_right code (base + 4) (base + 8) _ _ _
    (pcFree_regIs .x5 (BitVec.ofNat 32 0x02))
    s2'

  -- Compose s1' and s2'': base → base+8
  have chain12 := cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1' s2''

  -- Step 3: LI x11, bufPtr (base+8 → base+12)
  have s3 := li_spec_gen code .x11 v11_old bufPtr (base + 8) (by decide) hf2
  have h_eight_twelve : base + 8 + 4 = base + 12 := by grind
  have s3_conv : cpsTriple code (base + 8) (base + 12) (.x11 ↦ᵣ v11_old) (.x11 ↦ᵣ bufPtr) := by
    simp only [h_eight_twelve] at s3; exact s3
  have s3' := cpsTriple_frame_left code (base + 8) (base + 12) _ _ _
    (pcFree_sepConj (pcFree_regIs .x12 v12_old) hrest_pcfree) s3_conv
  have s3_x10 := cpsTriple_frame_right code (base + 8) (base + 12) _ _ _
    (pcFree_regIs .x10 13) s3'
  have s3'' := cpsTriple_frame_right code (base + 8) (base + 12) _ _ _
    (pcFree_regIs .x5 (BitVec.ofNat 32 0x02)) s3_x10

  -- Compose: base → base+12
  have chain123 := cpsTriple_seq code base (base + 8) (base + 12) _ _ _ chain12 s3''

  -- Step 4: LI x12, nbytes (base+12 → base+16)
  have s4 := li_spec_gen code .x12 v12_old nbytes (base + 12) (by decide) hf3
  have h_twelve_sixteen : base + 12 + 4 = base + 16 := by grind
  have s4_conv : cpsTriple code (base + 12) (base + 16) (.x12 ↦ᵣ v12_old) (.x12 ↦ᵣ nbytes) := by
    simp only [h_twelve_sixteen] at s4; exact s4
  have s4' := cpsTriple_frame_left code (base + 12) (base + 16) _ _ _
    hrest_pcfree s4_conv
  have s4_x11 := cpsTriple_frame_right code (base + 12) (base + 16) _ _ _
    (pcFree_regIs .x11 bufPtr) s4'
  have s4_x10 := cpsTriple_frame_right code (base + 12) (base + 16) _ _ _
    (pcFree_regIs .x10 13) s4_x11
  have s4'' := cpsTriple_frame_right code (base + 12) (base + 16) _ _ _
    (pcFree_regIs .x5 (BitVec.ofNat 32 0x02)) s4_x10

  -- Compose: base → base+16
  have chain1234 := cpsTriple_seq code base (base + 12) (base + 16) _ _ _ chain123 s4''

  -- Step 5: ECALL WRITE (base+16 → base+20)
  have s5 := ecall_write_public_spec_gen code bufPtr nbytes oldPV words (base + 16) hf4 hlen
  have h_sixteen_twenty : base + 16 + 4 = base + 20 := by grind
  have s5_conv : cpsTriple code (base + 16) (base + 20)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words) ** memBufferIs bufPtr words) := by
    simp only [h_sixteen_twenty] at s5; exact s5

  -- Compose: base → base+20
  exact cpsTriple_seq code base (base + 16) (base + 20) _ _ _ chain1234 s5_conv

end RiscVMacroAsm
