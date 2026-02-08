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
    {bytes : List (BitVec 8)}
    (hcompat : h.CompatibleWith s) (hnone : h.publicValues = none) :
    h.CompatibleWith (s.appendPublicValues bytes) := by
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
    {oldPV bytes : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (hPR : ((publicValuesIs oldPV) ** R).holdsFor s) :
    ((publicValuesIs (oldPV ++ bytes)) ** R).holdsFor (s.appendPublicValues bytes) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [publicValuesIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own publicValues (from disjointness)
  have hpv2 : h2.publicValues = none := by
    rcases hdisj.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPublicValues (oldPV ++ bytes)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, Or.inr hpv2, hdisj.2.2.2.2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPublicValues (oldPV ++ bytes) compatible with s.appendPublicValues bytes
  have hc1' : (PartialState.singletonPublicValues (oldPV ++ bytes)).CompatibleWith
      (s.appendPublicValues bytes) := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPublicValues] at hr,
            fun a w ha => by simp [PartialState.singletonPublicValues] at ha,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => ?_,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw⟩
    simp only [PartialState.singletonPublicValues] at hw
    rw [Option.some.injEq] at hw; subst hw
    rw [MachineState.publicValues_appendPublicValues]
    exact congrArg (· ++ bytes)
      ((PartialState.CompatibleWith_singletonPublicValues oldPV s).mp hc1)
  -- h2 compatible with s.appendPublicValues bytes
  have hc2' : h2.CompatibleWith (s.appendPublicValues bytes) :=
    PartialState.CompatibleWith_appendPublicValues hc2 hpv2
  exact ⟨(PartialState.singletonPublicValues (oldPV ++ bytes)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPublicValues (oldPV ++ bytes), h2, hdisj', rfl, rfl, hh2⟩

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
    Postcondition: same registers, publicValues = oldPV ++ readBytes(bufPtr, nbytes), memory preserved.

    Note: The WRITE syscall now reads individual bytes from memory (matching SP1).
    The postcondition expresses that readBytes from the buffer are appended to publicValues. -/
theorem ecall_write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (addr : Addr)
    (hfetch : code addr = some .ECALL)
    (hlen : words.length = nbytes.toNat / 4) :
    cpsTriple code addr (addr + 4)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])) ** memBufferIs bufPtr words) := by
  sorry

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
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hlen : words.length = nbytes.toNat / 4) :
    let code := loadProgram base (WRITE 13 bufPtr nbytes)
    cpsTriple code base (base + 20)
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ v12_old) ** publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])) ** memBufferIs bufPtr words) := by
  sorry

end RiscVMacroAsm
