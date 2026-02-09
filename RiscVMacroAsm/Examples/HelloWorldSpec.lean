/-
  RiscVMacroAsm.Examples.HelloWorldSpec

  CPS specification for the HelloWorld program: stores "hello world"
  to memory (4 chars per word), outputs via WRITE syscall, and halts.

  Proved by composing generalized per-instruction specs via structural
  rules (cpsTriple_seq, cpsTriple_seq_halt, frame embedding).
-/

import RiscVMacroAsm.Examples.HelloWorld
import RiscVMacroAsm.SyscallSpecs
import RiscVMacroAsm.InstructionSpecs
import RiscVMacroAsm.ControlFlow

namespace RiscVMacroAsm.Examples

open RiscVMacroAsm

-- ============================================================================
-- Section 1: Generalized SW spec (for arbitrary CodeMem)
-- ============================================================================

/-- SW rs1 rs2 offset: mem[rs1 + sext(offset)] := rs2 (generalized for any CodeMem) -/
theorem sw_spec_gen (code : CodeMem) (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hfetch : code addr = some (Instr.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.SW rs1 rs2 offset) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v_addr :=
    (holdsFor_regIs rs1 v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v_data :=
    (holdsFor_regIs rs2 v_data st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hinner))
  let mem_addr := v_addr + signExtend12 offset
  have hnext : execInstrBr st (Instr.SW rs1 rs2 offset) = (st.setMem mem_addr v_data).setPC (st.pc + 4) := by
    simp [execInstrBr, mem_addr, hrs1_val, hrs2_val]
  have hstep : step code st = some ((st.setMem mem_addr v_data).setPC (addr + 4)) := by
    have := step_sw _ _ _ _ _ hfetch' (by rw [hrs1_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setMem mem_addr v_data).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v_data) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rs2 v_data) (pcFree_memIs _ v_data))) hR)
      (st.setMem mem_addr v_data) (addr + 4) h5

/-- SW spec with memOwn (no mem_old needed). -/
theorem sw_spec_gen_own (code : CodeMem) (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hfetch : code addr = some (Instr.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h_inner, h_R, hdisj, hunion, hInner, hRest⟩ := hPR
  obtain ⟨h1, hr1, hd1, hu1, hv_addr, hrest1⟩ := hInner
  obtain ⟨h2, hr2, hd2, hu2, hv_data, ⟨mem_old, hmem⟩⟩ := hrest1
  exact sw_spec_gen code rs1 rs2 v_addr v_data mem_old offset addr hfetch hvalid R hR s
    ⟨hp, hcompat, h_inner, h_R, hdisj, hunion,
      ⟨h1, hr1, hd1, hu1, hv_addr, ⟨h2, hr2, hd2, hu2, hv_data, hmem⟩⟩, hRest⟩ hpc

-- ============================================================================
-- Section 2: Store word helper (LI x6 val ;; SW x7 x6 offset)
-- ============================================================================

/-- Combined spec for "LI x6, val ;; SW x7, x6, offset":
    Stores val at mem[x7_val + sext(offset)], updates x6 to val.
    Proved directly as a 2-step execution. -/
theorem storeWord_spec_gen (code : CodeMem) (val : Word) (offset : BitVec 12)
    (x6_old x7_val mem_old : Word) (addr : Addr)
    (hfetch_li : code addr = some (Instr.LI .x6 val))
    (hfetch_sw : code (addr + 4) = some (Instr.SW .x7 .x6 offset))
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 8)
      ((.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  -- Step 1: LI x6, val (addr → addr+4), frame x7 and mem
  let mem_addr := x7_val + signExtend12 offset
  have s1 : cpsTriple code addr (addr + 4) (.x6 ↦ᵣ x6_old) (.x6 ↦ᵣ val) :=
    li_spec_gen code .x6 x6_old val addr (by decide) hfetch_li
  have s1' : cpsTriple code addr (addr + 4)
      ((.x6 ↦ᵣ x6_old) ** ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old)))
      ((.x6 ↦ᵣ val) ** ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))) :=
    cpsTriple_frame_left code addr (addr + 4) _ _ ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))
      (pcFree_sepConj (pcFree_regIs .x7 x7_val) (pcFree_memIs mem_addr mem_old)) s1
  -- Step 2: SW x7, x6, offset (addr+4 → addr+8), frame x6
  have h48 : addr + 4 + 4 = addr + 8 := by grind
  have s2' : cpsTriple code (addr + 4) (addr + 8)
      ((.x7 ↦ᵣ x7_val) ** (.x6 ↦ᵣ val) ** (mem_addr ↦ₘ mem_old))
      ((.x7 ↦ᵣ x7_val) ** (.x6 ↦ᵣ val) ** (mem_addr ↦ₘ val)) := by
    have sw := sw_spec_gen code .x7 .x6 x7_val val mem_old offset (addr + 4) hfetch_sw hvalid
    simp only [h48] at sw; exact sw
  have swap12 : ∀ (A B C : Assertion) h, (A ** B ** C) h → (B ** A ** C) h :=
    fun A B C h hab =>
      sepConj_mono_right (fun h' hca => (sepConj_comm C A h').mp hca) h
        ((sepConj_assoc B C A h).mp
          ((sepConj_comm A (B ** C) h).mp hab))
  have s2'' : cpsTriple code (addr + 4) (addr + 8)
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ val)) :=
    cpsTriple_consequence code (addr + 4) (addr + 8) _ _ _ _
      (swap12 (.x6 ↦ᵣ val) (.x7 ↦ᵣ x7_val) (mem_addr ↦ₘ mem_old))
      (swap12 (.x7 ↦ᵣ x7_val) (.x6 ↦ᵣ val) (mem_addr ↦ₘ val))
      s2'
  exact cpsTriple_seq code addr (addr + 4) (addr + 8) _ _ _ s1' s2''

/-- Combined LI+SW spec with regOwn and memOwn (no x6_old or mem_old needed). -/
theorem storeWord_spec_gen_own (code : CodeMem) (val : Word) (offset : BitVec 12)
    (x7_val : Word) (addr : Addr)
    (hfetch_li : code addr = some (Instr.LI .x6 val))
    (hfetch_sw : code (addr + 4) = some (Instr.SW .x7 .x6 offset))
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 8)
      (regOwn .x6 ** (.x7 ↦ᵣ x7_val) ** memOwn (x7_val + signExtend12 offset))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h_inner, h_R, hdisj, hunion, hInner, hRest⟩ := hPR
  obtain ⟨h1, hr1, hd1, hu1, ⟨x6_old, hx6⟩, hrest1⟩ := hInner
  obtain ⟨h2, hr2, hd2, hu2, hx7, ⟨mem_old, hmem⟩⟩ := hrest1
  exact storeWord_spec_gen code val offset x6_old x7_val mem_old addr
    hfetch_li hfetch_sw hvalid R hR s
    ⟨hp, hcompat, h_inner, h_R, hdisj, hunion,
      ⟨h1, hr1, hd1, hu1, hx6, ⟨h2, hr2, hd2, hu2, hx7, hmem⟩⟩, hRest⟩ hpc

-- ============================================================================
-- Section 3: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem, given fetch proofs for the 3 instructions.
    Uses regOwn (no old values needed). -/
theorem halt_spec_gen (code : CodeMem) (exitCode : Word) (base : Addr)
    (hf0 : code base = some (Instr.LI .x5 0))
    (hf1 : code (base + 4) = some (Instr.LI .x10 exitCode))
    (hf2 : code (base + 8) = some .ECALL) :
    cpsHaltTriple code base
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  -- Step 1: LI x5 0 (base → base+4), frame regOwn .x10
  have s1 : cpsTriple code base (base + 4) (regOwn .x5) (.x5 ↦ᵣ (0 : Word)) :=
    li_spec_gen_own code .x5 0 base (by decide) hf0
  have s1' : cpsTriple code base (base + 4)
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsTriple_frame_left code base (base + 4) _ _ _ (pcFree_regOwn .x10) s1
  -- Step 2: LI x10 exitCode (base+4 → base+8), frame .x5 ↦ᵣ 0
  have h_four_four : base + 4 + 4 = base + 8 := by grind
  have s2 : cpsTriple code (base + 4) (base + 8) (regOwn .x10) (.x10 ↦ᵣ exitCode) := by
    have := li_spec_gen_own code .x10 exitCode (base + 4) (by decide) hf1
    simp only [h_four_four] at this; exact this
  have s2' : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ _ (pcFree_regIs .x5 (0 : Word)) s2
  -- Step 3: ECALL halt (base+8, halts)
  have s3 : cpsHaltTriple code (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    ecall_halt_spec_gen code exitCode (base + 8) hf2
  exact cpsTriple_seq_halt code base (base + 8) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1' s2') s3

-- ============================================================================
-- Section 4: Generalized WRITE spec (for arbitrary CodeMem)
-- ============================================================================

/-- WRITE 13 bufPtr nbytes on arbitrary CodeMem, given fetch proofs for all 5 instructions.
    Uses regOwn (no old register values needed).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32)
    (hf0 : code base = some (Instr.LI .x5 (BitVec.ofNat 32 0x02)))
    (hf1 : code (base + 4) = some (Instr.LI .x10 13))
    (hf2 : code (base + 8) = some (Instr.LI .x11 bufPtr))
    (hf3 : code (base + 12) = some (Instr.LI .x12 nbytes))
    (hf4 : code (base + 16) = some Instr.ECALL) :
    cpsTriple code base (base + 20)
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  -- Address arithmetic
  have h48 : base + 4 + 4 = base + 8 := by grind
  have h812 : base + 8 + 4 = base + 12 := by grind
  have h1216 : base + 12 + 4 = base + 16 := by grind
  have h1620 : base + 16 + 4 = base + 20 := by grind
  -- pcFree helpers
  let pvMB := publicValuesIs oldPV ** memBufferIs bufPtr words
  have hpvMB : pvMB.pcFree := pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)
  -- Step 1: LI x5 (base → base+4), frame = regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB
  have s1 : cpsTriple code base (base + 4) (regOwn .x5) (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) :=
    li_spec_gen_own code .x5 _ base (by decide) hf0
  have s1f : cpsTriple code base (base + 4)
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_left code base (base + 4) _ _ _
      (pcFree_sepConj (pcFree_regOwn .x10) (pcFree_sepConj (pcFree_regOwn .x11) (pcFree_sepConj (pcFree_regOwn .x12) hpvMB))) s1
  -- Step 2: LI x10 (base+4 → base+8), frame = .x5 ↦ᵣ 0x02 ** regOwn .x11 ** regOwn .x12 ** pvMB
  have s2core : cpsTriple code (base + 4) (base + 8) (regOwn .x10) (.x10 ↦ᵣ (13 : Word)) := by
    have := li_spec_gen_own code .x10 13 (base + 4) (by decide) hf1
    simp only [h48] at this; exact this
  have s2f : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** regOwn .x11 ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_left code (base + 4) (base + 8) _ _ _
        (pcFree_sepConj (pcFree_regOwn .x11) (pcFree_sepConj (pcFree_regOwn .x12) hpvMB)) s2core)
  -- Step 3: LI x11 (base+8 → base+12), frame = .x5 ↦ᵣ 0x02 ** .x10 ↦ᵣ 13 ** regOwn .x12 ** pvMB
  have s3core : cpsTriple code (base + 8) (base + 12) (regOwn .x11) (.x11 ↦ᵣ bufPtr) := by
    have := li_spec_gen_own code .x11 bufPtr (base + 8) (by decide) hf2
    simp only [h812] at this; exact this
  have s3f : cpsTriple code (base + 8) (base + 12)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_right code (base + 8) (base + 12) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code (base + 8) (base + 12) _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_left code (base + 8) (base + 12) _ _ _
          (pcFree_sepConj (pcFree_regOwn .x12) hpvMB) s3core))
  -- Step 4: LI x12 (base+12 → base+16), frame = .x5 ↦ᵣ 0x02 ** .x10 ↦ᵣ 13 ** .x11 ↦ᵣ bufPtr ** pvMB
  have s4core : cpsTriple code (base + 12) (base + 16) (regOwn .x12) (.x12 ↦ᵣ nbytes) := by
    have := li_spec_gen_own code .x12 nbytes (base + 12) (by decide) hf3
    simp only [h1216] at this; exact this
  have s4f : cpsTriple code (base + 12) (base + 16)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) ** pvMB) :=
    cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x11 ↦ᵣ _) (pcFree_regIs .x11 _)
          (cpsTriple_frame_left code (base + 12) (base + 16) _ _ _ hpvMB s4core)))
  -- Step 5: ECALL (base+16 → base+20)
  have s5 : cpsTriple code (base + 16) (base + 20)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) ** publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
    have := ecall_write_public_spec_gen code bufPtr nbytes oldPV words (base + 16) hf4 hLen hAligned
    simp only [h1620] at this; exact this
  -- Compose all steps
  exact cpsTriple_seq code base (base + 16) (base + 20) _ _ _
    (cpsTriple_seq code base (base + 12) (base + 16) _ _ _
      (cpsTriple_seq code base (base + 8) (base + 12) _ _ _
        (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1f s2f) s3f) s4f) s5

-- ============================================================================
-- Section 5: HelloWorld program instruction fetch lemmas
-- ============================================================================

/-- The helloWorld program as a flat list of instructions. -/
private theorem helloWorld_instrs :
    helloWorld = ([
      Instr.LI .x7 0x100,                              -- 0: base addr
      Instr.LI .x6 0x6C6C6568, Instr.SW .x7 .x6 0,    -- 1-2: "hell"
      Instr.LI .x6 0x6F77206F, Instr.SW .x7 .x6 4,    -- 3-4: "o wo"
      Instr.LI .x6 0x00646C72, Instr.SW .x7 .x6 8,    -- 5-6: "rld\0"
      Instr.LI .x5 (BitVec.ofNat 32 0x02),             -- 7: WRITE setup
      Instr.LI .x10 13,                                 -- 8
      Instr.LI .x11 0x100,                              -- 9
      Instr.LI .x12 11,                                 -- 10
      Instr.ECALL,                                       -- 11: WRITE ecall
      Instr.LI .x5 0,                                   -- 12: HALT setup
      Instr.LI .x10 0,                                  -- 13
      Instr.ECALL                                        -- 14: HALT ecall
    ] : List Instr) := by
  simp only [helloWorld, HALT, WRITE, LI, SW, single, seq, Program]
  simp only [List.cons_append, List.nil_append]
  rfl

private def hwCode : CodeMem := loadProgram 0 helloWorld

private def hwInstrs : List Instr := [
  Instr.LI .x7 0x100,
  Instr.LI .x6 0x6C6C6568, Instr.SW .x7 .x6 0,
  Instr.LI .x6 0x6F77206F, Instr.SW .x7 .x6 4,
  Instr.LI .x6 0x00646C72, Instr.SW .x7 .x6 8,
  Instr.LI .x5 (BitVec.ofNat 32 0x02),
  Instr.LI .x10 13,
  Instr.LI .x11 0x100,
  Instr.LI .x12 11,
  Instr.ECALL,
  Instr.LI .x5 0,
  Instr.LI .x10 0,
  Instr.ECALL
]

private theorem hwCode_eq : hwCode = loadProgram 0 hwInstrs := by
  simp only [hwCode, hwInstrs, helloWorld_instrs]

/-- Fetch instruction at index k from the helloWorld program. -/
private theorem hw_fetch_at (k : Nat) (hk : k < hwInstrs.length)
    (h4k : 4 * k < 2^32) :
    hwCode (BitVec.ofNat 32 (4 * k)) = some (hwInstrs[k]'hk) := by
  rw [hwCode_eq]
  have : (0 : BitVec 32) + BitVec.ofNat 32 (4 * k) = BitVec.ofNat 32 (4 * k) := by
    simp [BitVec.zero_add]
  rw [← this]
  rw [loadProgram_at_index 0 hwInstrs k hk h4k]
  simp [hwInstrs]

private theorem hwInstrs_length : hwInstrs.length = 15 := by
  simp only [hwInstrs, List.length_cons, List.length_nil]

private theorem hw_fetch (k : Nat) (hk : k < 15) (h4k : 4 * k < 2^32) :
    hwCode (BitVec.ofNat 32 (4 * k)) = some (hwInstrs[k]'(by rw [hwInstrs_length]; omega)) :=
  hw_fetch_at k (by rw [hwInstrs_length]; omega) h4k

-- ============================================================================
-- Section 6: Store phase (3 packed word stores)
-- ============================================================================

-- Rearrangement helpers

private theorem swap12 (A B C : Assertion) :
    ∀ h, (A ** B ** C) h → (B ** A ** C) h :=
  fun h hab =>
    sepConj_mono_right (fun h' hca => (sepConj_comm C A h').mp hca) h
      ((sepConj_assoc B C A h).mp ((sepConj_comm A (B ** C) h).mp hab))

private theorem group3 (A B C D : Assertion) :
    ∀ h, (A ** B ** C ** D) h → ((A ** B ** C) ** D) h :=
  fun h hab =>
    (sepConj_assoc A (B ** C) D h).mpr
      (sepConj_mono_right (fun h' => (sepConj_assoc B C D h').mpr) h hab)

private theorem ungroup3 (A B C D : Assertion) :
    ∀ h, ((A ** B ** C) ** D) h → (A ** B ** C ** D) h :=
  fun h hab =>
    sepConj_mono_right (fun h' => (sepConj_assoc B C D h').mp) h
      ((sepConj_assoc A (B ** C) D h).mp hab)

-- Rearrangement lemma for phase 1 pre
private theorem phase1_pre_rearrange (x5 x6 x7 x10 x11 x12 m0 m1 m2 pv : Assertion) :
    ∀ h, (x5 ** x6 ** x7 ** x10 ** x11 ** x12 ** m0 ** m1 ** m2 ** pv) h →
      ((x6 ** x7 ** m0 ** m1 ** m2) ** (x5 ** x10 ** x11 ** x12 ** pv)) h := by
  intro h hab
  sep_perm hab

-- Rearrangement lemma for phase 1 post (reverse direction)
private theorem phase1_post_rearrange (x5 x6' x7' x10 x11 x12 m0' m1' m2' pv : Assertion) :
    ∀ h, ((x6' ** x7' ** m0' ** m1' ** m2') ** (x5 ** x10 ** x11 ** x12 ** pv)) h →
      (x5 ** x6' ** x7' ** x10 ** x11 ** x12 ** m0' ** m1' ** m2' ** pv) h := by
  intro h hab
  sep_perm hab

-- signExtend12 lemmas
private theorem hse0 : (0x100 : Word) + signExtend12 (0 : BitVec 12) = 0x100 := by native_decide
private theorem hse4 : (0x100 : Word) + signExtend12 (4 : BitVec 12) = 0x104 := by native_decide
private theorem hse8 : (0x100 : Word) + signExtend12 (8 : BitVec 12) = 0x108 := by native_decide

-- ============================================================================
-- Section 6a: LI x7 initialization (instruction 0, address 0 → 4)
-- ============================================================================

private theorem storeInit (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 0 4
      (regOwn .x7 ** F)
      ((.x7 ↦ᵣ 0x100) ** F) :=
  cpsTriple_frame_left hwCode 0 4 _ _ F hF
    (li_spec_gen_own hwCode .x7 0x100 0 (by decide) (hw_fetch 0 (by omega) (by omega)))

-- ============================================================================
-- Section 6b: Individual store word steps
-- ============================================================================

-- Step 0: store "hell" at 0x100 (addr 4→12). Uses regOwn .x6 and memOwn.
private theorem storeStep0 (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 4 12
      (regOwn .x6 ** (.x7 ↦ᵣ 0x100) ** memOwn (0x100 : Addr) ** F)
      ((.x6 ↦ᵣ 0x6C6C6568) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** F) := by
  have sc := storeWord_spec_gen_own hwCode 0x6C6C6568 0 0x100 4
    (hw_fetch 1 (by omega) (by omega)) (hw_fetch 2 (by omega) (by omega))
    (by rw [hse0]; native_decide)
  rw [hse0] at sc
  exact cpsTriple_consequence hwCode 4 12 _ _ _ _
    (group3 _ _ _ F) (ungroup3 _ _ _ F)
    (cpsTriple_frame_left hwCode 4 12 _ _ F hF sc)

-- Step 1: store "o wo" at 0x104 (addr 12→20). Uses regOwn .x6 and memOwn.
private theorem storeStep1 (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 12 20
      (regOwn .x6 ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** memOwn (0x104 : Addr) ** F)
      ((.x6 ↦ᵣ 0x6F77206F) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** F) := by
  have sc := storeWord_spec_gen_own hwCode 0x6F77206F 4 0x100 12
    (hw_fetch 3 (by omega) (by omega)) (hw_fetch 4 (by omega) (by omega))
    (by rw [hse4]; native_decide)
  rw [hse4] at sc
  let m0d := (0x100 : Addr) ↦ₘ (0x6C6C6568 : Word)
  have sc_f := cpsTriple_frame_left hwCode 12 20 _ _ (m0d ** F)
    (pcFree_sepConj (pcFree_memIs _ _) hF) sc
  exact cpsTriple_consequence hwCode 12 20 _ _ _ _
    (fun h hab => group3 _ _ _ _ h
      (sepConj_mono_right (sepConj_mono_right (swap12 m0d _ F)) h hab))
    (fun h hab => sepConj_mono_right (sepConj_mono_right (swap12 _ m0d F)) h
      (ungroup3 _ _ _ _ h hab))
    sc_f

-- Step 2: store "rld\0" at 0x108 (addr 20→28). Uses regOwn .x6 and memOwn.
private theorem storeStep2 (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 20 28
      (regOwn .x6 ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** memOwn (0x108 : Addr) ** F)
      ((.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** ((0x108 : Addr) ↦ₘ 0x00646C72) ** F) := by
  have sc := storeWord_spec_gen_own hwCode 0x00646C72 8 0x100 20
    (hw_fetch 5 (by omega) (by omega)) (hw_fetch 6 (by omega) (by omega))
    (by rw [hse8]; native_decide)
  rw [hse8] at sc
  let m0d := (0x100 : Addr) ↦ₘ (0x6C6C6568 : Word)
  let m1d := (0x104 : Addr) ↦ₘ (0x6F77206F : Word)
  let m2v := memOwn (0x108 : Addr)
  let m2d := (0x108 : Addr) ↦ₘ (0x00646C72 : Word)
  have sc_f := cpsTriple_frame_left hwCode 20 28 _ _ (m0d ** m1d ** F)
    (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _) hF)) sc
  exact cpsTriple_consequence hwCode 20 28 _ _ _ _
    (fun h hab => group3 _ _ _ _ h
      (sepConj_mono_right (sepConj_mono_right (swap12 m0d m2v (m1d ** F))) h
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (swap12 m1d m2v F))) h hab)))
    (fun h hab =>
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (swap12 m2d m1d F))) h
        (sepConj_mono_right (sepConj_mono_right (swap12 m2d m0d (m1d ** F))) h
          (ungroup3 _ _ _ _ h hab)))
    sc_f

-- ============================================================================
-- Section 6c: Store phase composition
-- ============================================================================

/-- Store phase with regOwn/memOwn. Composition showcases weakening between steps:
    after each store produces `.x6 ↦ᵣ val`, we weaken back to `regOwn .x6`
    via `cpsTriple_consequence` + `regIs_implies_regOwn` before the next step. -/
theorem storePhase_spec :
    cpsTriple hwCode 0 28
      (regOwn .x6 ** regOwn .x7 **
       memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr))
      ((.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72)) := by
  have hpf_memOwn : ∀ (a : Addr), (memOwn a).pcFree := pcFree_memOwn
  have hpf_memIs : ∀ (a : Addr) (v : Word), ((a ↦ₘ v) : Assertion).pcFree := pcFree_memIs
  -- Step 0: LI x7 0x100 (0 → 4)
  -- Pre: regOwn .x6 ** regOwn .x7 ** memOwn 0x100 ** memOwn 0x104 ** memOwn 0x108
  -- We frame regOwn .x7 with (regOwn .x6 ** memOwn 0x100 ** memOwn 0x104 ** memOwn 0x108)
  have t0 := storeInit
    (regOwn .x6 ** memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr))
    (pcFree_sepConj (pcFree_regOwn .x6) (pcFree_sepConj (hpf_memOwn _) (pcFree_sepConj (hpf_memOwn _) (hpf_memOwn _))))
  -- t0 : regOwn .x7 ** (regOwn .x6 ** memOwn ...) → .x7 ↦ᵣ 0x100 ** (regOwn .x6 ** memOwn ...)
  -- Rearrange pre to match: regOwn .x6 ** regOwn .x7 ** ... → regOwn .x7 ** (regOwn .x6 ** ...)
  have t0' := cpsTriple_consequence hwCode 0 4 _ _ _ _
    (swap12 (regOwn .x6) (regOwn .x7)
      (memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr)))
    (fun _ h => h) t0
  -- Post: .x7 ↦ᵣ 0x100 ** (regOwn .x6 ** memOwn 0x100 ** memOwn 0x104 ** memOwn 0x108)
  -- Rearrange post: → regOwn .x6 ** .x7 ↦ᵣ 0x100 ** memOwn 0x100 ** memOwn 0x104 ** memOwn 0x108
  have t0'' := cpsTriple_consequence hwCode 0 4 _ _ _ _ (fun _ h => h)
    (swap12 (.x7 ↦ᵣ (0x100 : Word)) (regOwn .x6)
      (memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr)))
    t0'
  -- Step 1: store "hell" at 0x100 (4 → 12)
  -- storeStep0 needs: regOwn .x6 ** .x7 ↦ᵣ 0x100 ** memOwn 0x100 ** F
  have t1 := storeStep0
    (memOwn (0x104 : Addr) ** memOwn (0x108 : Addr))
    (pcFree_sepConj (hpf_memOwn _) (hpf_memOwn _))
  have c01 := cpsTriple_seq hwCode 0 4 12 _ _ _ t0'' t1
  -- Post: .x6 ↦ᵣ 0x6C6C6568 ** .x7 ↦ᵣ 0x100 ** 0x100 ↦ₘ 0x6C6C6568 ** memOwn 0x104 ** memOwn 0x108
  -- Weaken .x6 ↦ᵣ 0x6C6C6568 to regOwn .x6 for the next step
  have c01_weak := cpsTriple_consequence hwCode 0 12 _ _ _ _ (fun _ h => h)
    (sepConj_mono_left (regIs_implies_regOwn .x6 0x6C6C6568)) c01
  -- Step 2: store "o wo" at 0x104 (12 → 20)
  -- storeStep1 needs: regOwn .x6 ** .x7 ↦ᵣ 0x100 ** 0x100 ↦ₘ 0x6C6C6568 ** memOwn 0x104 ** F
  have t2 := storeStep1
    (memOwn (0x108 : Addr))
    (hpf_memOwn _)
  have c02 := cpsTriple_seq hwCode 0 12 20 _ _ _ c01_weak t2
  -- Post: .x6 ↦ᵣ 0x6F77206F ** .x7 ↦ᵣ 0x100 ** 0x100 ↦ₘ 0x6C6C6568 ** 0x104 ↦ₘ 0x6F77206F ** memOwn 0x108
  -- Weaken .x6 ↦ᵣ 0x6F77206F to regOwn .x6 for the next step
  have c02_weak := cpsTriple_consequence hwCode 0 20 _ _ _ _ (fun _ h => h)
    (sepConj_mono_left (regIs_implies_regOwn .x6 0x6F77206F)) c02
  -- Step 3: store "rld\0" at 0x108 (20 → 28), with F = empAssertion, then strip emp
  have t3_raw := storeStep2 empAssertion pcFree_emp
  have t3 := cpsTriple_consequence hwCode 20 28 _ _ _ _
    (fun h hab =>
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h' hm => (sepConj_emp_right _ h').mpr hm)))) h hab)
    (fun h hab =>
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h' hm => (sepConj_emp_right _ h').mp hm)))) h hab)
    t3_raw
  exact cpsTriple_seq hwCode 0 20 28 _ _ _ c02_weak t3

-- ============================================================================
-- Section 7: Main HelloWorld CPS Triple
-- ============================================================================

-- Helper: the write phase produces helloWorldBytes
private theorem write_bytes_eq :
    ([0x6C6C6568, 0x6F77206F, 0x00646C72].flatMap
      (fun (w : Word) => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take
      (BitVec.toNat (11 : Word)) = helloWorldBytes := by native_decide

-- Helper: 0x100 aligned
private theorem aligned_0x100 : (0x100 : Word) &&& 3#32 = 0#32 := by native_decide

-- Helper: memBufferIs for 3 words at 0x100 ↔ individual memIs (PartialState level)
private theorem addr_100_plus_4 : (0x100 : Addr) + 4 = 0x104 := by native_decide
private theorem addr_104_plus_4 : (0x104 : Addr) + 4 = 0x108 := by native_decide

private theorem memBufferIs_three_fwd (w0 w1 w2 : Word) :
    ∀ h, (((0x100 : Addr) ↦ₘ w0) ** ((0x104 : Addr) ↦ₘ w1) ** ((0x108 : Addr) ↦ₘ w2)) h →
      (memBufferIs 0x100 [w0, w1, w2]) h := by
  intro h hh
  simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4]
  exact sepConj_mono_right (sepConj_mono_right
    (fun s' h2 => ((sepConj_emp_right _ s').mpr h2))) h hh

private theorem memBufferIs_three_bwd (w0 w1 w2 : Word) :
    ∀ h, (memBufferIs 0x100 [w0, w1, w2]) h →
      (((0x100 : Addr) ↦ₘ w0) ** ((0x104 : Addr) ↦ₘ w1) ** ((0x108 : Addr) ↦ₘ w2)) h := by
  intro h hh
  simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4] at hh
  exact sepConj_mono_right (sepConj_mono_right
    (fun s' h2 => ((sepConj_emp_right _ s').mp h2))) h hh

-- Rearrangement for phase 2 pre: convert memIs to memBufferIs and rearrange
-- Now takes regOwn for x5/x10/x11/x12 and concrete x6'/x7'
private theorem phase2_pre_rearrange_own (x6' x7' : Word) (m0' m1' m2' : Word) (pv : List (BitVec 8)) :
    ∀ h, (regOwn .x5 ** (.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
         regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
         ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
         ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv) h →
      ((.x7 ↦ᵣ x7') ** (.x6 ↦ᵣ x6') ** (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** publicValuesIs pv ** memBufferIs 0x100 [m0', m1', m2'])) h := by
  intro h hab
  simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4, sepConj_emp_left', sepConj_comm',
    sepConj_left_comm'] at hab ⊢
  exact hab

-- Rearrangement for phase 2 post (with regOwn context)
private theorem phase2_post_rearrange_own (x5' x6' x7' x10' x11' x12' : Word) (m0' m1' m2' : Word) (pv' : List (BitVec 8)) :
    ∀ h, ((.x7 ↦ᵣ x7') ** (.x6 ↦ᵣ x6') ** ((.x5 ↦ᵣ x5') ** (.x10 ↦ᵣ x10') ** (.x11 ↦ᵣ x11') ** (.x12 ↦ᵣ x12') ** publicValuesIs pv' ** memBufferIs 0x100 [m0', m1', m2'])) h →
      ((.x5 ↦ᵣ x5') ** (.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
       (.x10 ↦ᵣ x10') ** (.x11 ↦ᵣ x11') ** (.x12 ↦ᵣ x12') **
       ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
       ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv') h := by
  intro h hab
  simp only [memBufferIs, addr_100_plus_4, addr_104_plus_4, sepConj_emp_left', sepConj_comm',
    sepConj_left_comm'] at hab ⊢
  exact hab

-- Rearrangement for phase 3 pre (with weakening x5/x10 to regOwn)
private theorem phase3_pre_rearrange_own (x5 x6' x7' x10 x11 x12 : Word) (m0' m1' m2' : Word) (pv : List (BitVec 8)) :
    ∀ h, ((.x5 ↦ᵣ x5) ** (.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
         (.x10 ↦ᵣ x10) ** (.x11 ↦ᵣ x11) ** (.x12 ↦ᵣ x12) **
         ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
         ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv) h →
      ((regOwn .x5 ** regOwn .x10) ** ((.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
       (.x11 ↦ᵣ x11) ** (.x12 ↦ᵣ x12) **
       ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
       ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv)) h := by
  intro h hab
  have hab' := sepConj_mono_left (regIs_implies_regOwn .x5 x5) h
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (regIs_implies_regOwn .x10 x10)))) h hab)
  sep_perm hab'

-- Rearrangement for phase 3 post
private theorem phase3_post_rearrange_own (x5' x6' x7' x10' x11 x12 : Word) (m0' m1' m2' : Word) (pv : List (BitVec 8)) :
    ∀ h, (((.x5 ↦ᵣ x5') ** (.x10 ↦ᵣ x10')) ** ((.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
         (.x11 ↦ᵣ x11) ** (.x12 ↦ᵣ x12) **
         ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
         ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv)) h →
      ((.x5 ↦ᵣ x5') ** (.x6 ↦ᵣ x6') ** (.x7 ↦ᵣ x7') **
       (.x10 ↦ᵣ x10') ** (.x11 ↦ᵣ x11) ** (.x12 ↦ᵣ x12) **
       ((0x100 : Addr) ↦ₘ m0') ** ((0x104 : Addr) ↦ₘ m1') **
       ((0x108 : Addr) ↦ₘ m2') ** publicValuesIs pv) h := by
  intro h hab
  sep_perm hab

theorem helloWorld_spec (oldPV : List (BitVec 8)) :
    cpsHaltTriple hwCode 0
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr) **
       publicValuesIs oldPV)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ helloWorldBytes)) := by
  -- Instruction fetches for the three phases
  -- Write phase: instructions 7-11 at addresses 28-44
  have hwf7 : hwCode 28 = some (Instr.LI .x5 (BitVec.ofNat 32 0x02)) := hw_fetch 7 (by omega) (by omega)
  have hwf8 : hwCode 32 = some (Instr.LI .x10 13) := hw_fetch 8 (by omega) (by omega)
  have hwf9 : hwCode 36 = some (Instr.LI .x11 0x100) := hw_fetch 9 (by omega) (by omega)
  have hwf10 : hwCode 40 = some (Instr.LI .x12 11) := hw_fetch 10 (by omega) (by omega)
  have hwf11 : hwCode 44 = some Instr.ECALL := hw_fetch 11 (by omega) (by omega)
  -- Halt phase: instructions 12-14 at addresses 48-56
  have hwf12 : hwCode 48 = some (Instr.LI .x5 0) := hw_fetch 12 (by omega) (by omega)
  have hwf13 : hwCode 52 = some (Instr.LI .x10 0) := hw_fetch 13 (by omega) (by omega)
  have hwf14 : hwCode 56 = some Instr.ECALL := hw_fetch 14 (by omega) (by omega)
  -- Address arithmetic
  have h28_32 : (28 : Addr) + 4 = 32 := by native_decide
  have h48_52 : (48 : Addr) + 4 = 52 := by native_decide
  have h52_56 : (52 : Addr) + 4 = 56 := by native_decide
  -- Phase 1: Store (0 → 28)
  -- storePhase_spec now takes regOwn .x6 ** regOwn .x7 ** memOwn ...
  -- Frame: regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pv
  let storeFrame := regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** publicValuesIs oldPV
  have hstoreFramePF : storeFrame.pcFree :=
    pcFree_sepConj (pcFree_regOwn .x5) (pcFree_sepConj (pcFree_regOwn .x10)
      (pcFree_sepConj (pcFree_regOwn .x11) (pcFree_sepConj (pcFree_regOwn .x12) (pcFree_publicValuesIs _))))
  have phase1_core := storePhase_spec
  have phase1 := cpsTriple_frame_left hwCode 0 28 _ _ storeFrame hstoreFramePF phase1_core
  -- Rearrange: regOwn x5 ** regOwn x6 ** regOwn x7 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** memOwn ** memOwn ** memOwn ** pv
  --         → (regOwn x6 ** regOwn x7 ** memOwn ** memOwn ** memOwn) ** (regOwn x5 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** pv)
  have phase1_adj : cpsTriple hwCode 0 28
      (regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       memOwn (0x100 : Addr) ** memOwn (0x104 : Addr) ** memOwn (0x108 : Addr) **
       publicValuesIs oldPV)
      (regOwn .x5 ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) ** publicValuesIs oldPV) := by
    apply cpsTriple_consequence hwCode 0 28 _ _ _ _
      (phase1_pre_rearrange (regOwn .x5) (regOwn .x6) (regOwn .x7)
        (regOwn .x10) (regOwn .x11) (regOwn .x12)
        (memOwn (0x100 : Addr)) (memOwn (0x104 : Addr)) (memOwn (0x108 : Addr)) (publicValuesIs oldPV))
      (phase1_post_rearrange (regOwn .x5) (.x6 ↦ᵣ 0x00646C72) (.x7 ↦ᵣ 0x100)
        (regOwn .x10) (regOwn .x11) (regOwn .x12)
        ((0x100 : Addr) ↦ₘ 0x6C6C6568) ((0x104 : Addr) ↦ₘ 0x6F77206F) ((0x108 : Addr) ↦ₘ 0x00646C72) (publicValuesIs oldPV))
    exact phase1
  -- Phase 2: Write (28 → 48)
  -- write_public_spec_gen now takes regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pv ** memBuf
  -- Current state: regOwn x5 ** x6' ** x7' ** regOwn x10 ** regOwn x11 ** regOwn x12 ** memIs ** memIs ** memIs ** pv
  -- Need: x7' ** x6' ** (regOwn x5 ** regOwn x10 ** regOwn x11 ** regOwn x12 ** pv ** memBufferIs)
  have h28_36 : (28 : Addr) + 8 = 36 := by native_decide
  have h28_40 : (28 : Addr) + 12 = 40 := by native_decide
  have h28_44 : (28 : Addr) + 16 = 44 := by native_decide
  have h28_48 : (28 : Addr) + 20 = 48 := by native_decide
  have h48_56 : (48 : Addr) + 8 = 56 := by native_decide
  have hLen : BitVec.toNat (11 : Word) ≤ 4 * [(0x6C6C6568 : Word), 0x6F77206F, 0x00646C72].length := by native_decide
  have write_core := write_public_spec_gen hwCode (0x100 : Word) (11 : Word)
    oldPV [(0x6C6C6568 : Word), 0x6F77206F, 0x00646C72] 28
    hLen aligned_0x100 hwf7
    (by rw [h28_32]; exact hwf8)
    (by rw [h28_36]; exact hwf9)
    (by rw [h28_40]; exact hwf10)
    (by rw [h28_44]; exact hwf11)
  -- Frame with x6' and x7'
  let x6Post := (.x6 ↦ᵣ (0x00646C72 : Word))
  let x7Post := (.x7 ↦ᵣ (0x100 : Word))
  have write_framed := cpsTriple_frame_right hwCode 28 48 _ _ x7Post (pcFree_regIs .x7 _)
    (cpsTriple_frame_right hwCode 28 48 _ _ x6Post (pcFree_regIs .x6 _) write_core)
  -- Rearrange and convert memBuf ↔ individual memIs
  have phase2 : cpsTriple hwCode 28 48
      (regOwn .x5 ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) ** publicValuesIs oldPV)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ ([(0x6C6C6568 : Word), 0x6F77206F, 0x00646C72].flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (BitVec.toNat (11 : Word)))) := by
    apply cpsTriple_consequence hwCode 28 48 _ _ _ _
      (phase2_pre_rearrange_own 0x00646C72 0x100 0x6C6C6568 0x6F77206F 0x00646C72 oldPV)
      (phase2_post_rearrange_own (BitVec.ofNat 32 0x02) 0x00646C72 0x100 13 0x100 11 0x6C6C6568 0x6F77206F 0x00646C72
        (oldPV ++ ([(0x6C6C6568 : Word), 0x6F77206F, 0x00646C72].flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take (BitVec.toNat (11 : Word))))
    exact write_framed
  -- Convert the write postcondition bytes to helloWorldBytes
  have phase2' : cpsTriple hwCode 28 48
      (regOwn .x5 ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) ** publicValuesIs oldPV)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ helloWorldBytes)) := by
    rw [write_bytes_eq] at phase2; exact phase2
  -- Phase 3: Halt (48 → halts)
  -- halt_spec_gen now takes regOwn .x5 ** regOwn .x10
  -- Current state: x5 ↦ᵣ 0x02 ** x6' ** x7' ** x10 ↦ᵣ 13 ** x11' ** x12' ** memIs ** memIs ** memIs ** pv'
  -- Need to weaken x5 and x10 back to regOwn, then rearrange for halt_spec_gen
  have halt_core := halt_spec_gen hwCode 0 48
    hwf12
    (by rw [h48_52]; exact hwf13)
    (by rw [h48_56]; exact hwf14)
  -- halt_core : cpsHaltTriple hwCode 48 (regOwn .x5 ** regOwn .x10) ((.x5 ↦ᵣ 0) ** (.x10 ↦ᵣ 0))
  -- Frame with everything else
  let haltFrame := (.x6 ↦ᵣ (0x00646C72 : Word)) ** (.x7 ↦ᵣ (0x100 : Word)) **
    (.x11 ↦ᵣ (0x100 : Word)) ** (.x12 ↦ᵣ (11 : Word)) **
    ((0x100 : Addr) ↦ₘ (0x6C6C6568 : Word)) ** ((0x104 : Addr) ↦ₘ (0x6F77206F : Word)) **
    ((0x108 : Addr) ↦ₘ (0x00646C72 : Word)) ** publicValuesIs (oldPV ++ helloWorldBytes)
  have hHaltFramePF : haltFrame.pcFree :=
    pcFree_sepConj (pcFree_regIs .x6 _) (pcFree_sepConj (pcFree_regIs .x7 _)
      (pcFree_sepConj (pcFree_regIs .x11 _) (pcFree_sepConj (pcFree_regIs .x12 _)
        (pcFree_sepConj (pcFree_memIs _ _) (pcFree_sepConj (pcFree_memIs _ _)
          (pcFree_sepConj (pcFree_memIs _ _) (pcFree_publicValuesIs _)))))))
  have halt_framed := cpsHaltTriple_frame_left hwCode 48 _ _ haltFrame hHaltFramePF halt_core
  -- halt_framed: (regOwn x5 ** regOwn x10) ** haltFrame → (x5 ↦ᵣ 0 ** x10 ↦ᵣ 0) ** haltFrame
  -- Weaken x5 and x10 to regOwn via phase3_pre_rearrange_own, then rearrange
  have phase3 : cpsHaltTriple hwCode 48
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ helloWorldBytes))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ helloWorldBytes)) := by
    apply cpsHaltTriple_consequence hwCode 48 _ _ _ _
      (phase3_pre_rearrange_own (BitVec.ofNat 32 0x02) 0x00646C72 0x100 13 0x100 11 0x6C6C6568 0x6F77206F 0x00646C72 (oldPV ++ helloWorldBytes))
      (phase3_post_rearrange_own 0 0x00646C72 0x100 0 0x100 11 0x6C6C6568 0x6F77206F 0x00646C72 (oldPV ++ helloWorldBytes))
    exact halt_framed
  -- Compose all phases
  exact cpsTriple_seq_halt hwCode 0 48 _ _ _
    (cpsTriple_seq hwCode 0 28 48 _ _ _ phase1_adj phase2') phase3

end RiscVMacroAsm.Examples
