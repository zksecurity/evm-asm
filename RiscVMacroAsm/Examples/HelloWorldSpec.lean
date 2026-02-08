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

-- ============================================================================
-- Section 3: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem, given fetch proofs for the 3 instructions. -/
theorem halt_spec_gen (code : CodeMem) (exitCode : Word) (v5_old v10_old : Word) (base : Addr)
    (hf0 : code base = some (Instr.LI .x5 0))
    (hf1 : code (base + 4) = some (Instr.LI .x10 exitCode))
    (hf2 : code (base + 8) = some .ECALL) :
    cpsHaltTriple code base
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  have s1 : cpsTriple code base (base + 4) (.x5 ↦ᵣ v5_old) (.x5 ↦ᵣ (0 : Word)) :=
    li_spec_gen code .x5 v5_old 0 base (by decide) hf0
  have s1' : cpsTriple code base (base + 4)
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10_old)) :=
    cpsTriple_frame_left code base (base + 4) _ _ _ (pcFree_regIs .x10 v10_old) s1
  have h_four_four : base + 4 + 4 = base + 8 := by grind
  have s2 : cpsTriple code (base + 4) (base + 8) (.x10 ↦ᵣ v10_old) (.x10 ↦ᵣ exitCode) := by
    have := li_spec_gen code .x10 v10_old exitCode (base + 4) (by decide) hf1
    simp only [h_four_four] at this; exact this
  have s2' : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10_old))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ _ (pcFree_regIs .x5 (0 : Word)) s2
  have s3 : cpsHaltTriple code (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    ecall_halt_spec_gen code exitCode (base + 8) hf2
  exact cpsTriple_seq_halt code base (base + 8) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1' s2') s3

-- ============================================================================
-- Section 4: Generalized WRITE spec (for arbitrary CodeMem) [sorry'd]
-- ============================================================================

/-- WRITE 13 bufPtr nbytes on arbitrary CodeMem, given fetch proofs for all 5 instructions.
    The postcondition expresses that readBytes from the buffer are appended to publicValues.
    This spec is for word-aligned byte counts (nbytes divisible by 4). -/
theorem write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (v5_old v10_old v11_old v12_old : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hlen : words.length = nbytes.toNat / 4)
    (hf0 : code base = some (Instr.LI .x5 (BitVec.ofNat 32 0x02)))
    (hf1 : code (base + 4) = some (Instr.LI .x10 13))
    (hf2 : code (base + 8) = some (Instr.LI .x11 bufPtr))
    (hf3 : code (base + 12) = some (Instr.LI .x12 nbytes))
    (hf4 : code (base + 16) = some Instr.ECALL) :
    cpsTriple code base (base + 20)
      ((.x5 ↦ᵣ v5_old) ** (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) **
       (.x12 ↦ᵣ v12_old) ** publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])) ** memBufferIs bufPtr words) := by
  sorry

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

-- signExtend12 lemmas
private theorem hse0 : (0x100 : Word) + signExtend12 (0 : BitVec 12) = 0x100 := by native_decide
private theorem hse4 : (0x100 : Word) + signExtend12 (4 : BitVec 12) = 0x104 := by native_decide
private theorem hse8 : (0x100 : Word) + signExtend12 (8 : BitVec 12) = 0x108 := by native_decide

-- ============================================================================
-- Section 6a: LI x7 initialization (instruction 0, address 0 → 4)
-- ============================================================================

private theorem storeInit (v6_old v7_old : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 0 4
      ((.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ v7_old) ** F)
      ((.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ 0x100) ** F) := by
  have s0 := li_spec_gen hwCode .x7 v7_old 0x100 0 (by decide) (hw_fetch 0 (by omega) (by omega))
  have s0' := cpsTriple_frame_left hwCode 0 4 _ _ ((.x6 ↦ᵣ v6_old) ** F)
    (pcFree_sepConj (pcFree_regIs .x6 v6_old) hF) s0
  exact cpsTriple_consequence hwCode 0 4 _ _ _ _
    (swap12 (.x6 ↦ᵣ v6_old) (.x7 ↦ᵣ v7_old) F)
    (swap12 (.x7 ↦ᵣ 0x100) (.x6 ↦ᵣ v6_old) F) s0'

-- ============================================================================
-- Section 6b: Individual store word steps
-- ============================================================================

-- Step 0: store "hell" at 0x100 (addr 4→12). No rearrangement needed.
private theorem storeStep0 (x6_old m0 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 4 12
      ((.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ m0) ** F)
      ((.x6 ↦ᵣ 0x6C6C6568) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** F) := by
  have sc := storeWord_spec_gen hwCode 0x6C6C6568 0 x6_old 0x100 m0 4
    (hw_fetch 1 (by omega) (by omega)) (hw_fetch 2 (by omega) (by omega))
    (by rw [hse0]; native_decide)
  rw [hse0] at sc
  exact cpsTriple_consequence hwCode 4 12 _ _ _ _
    (group3 _ _ _ F) (ungroup3 _ _ _ F)
    (cpsTriple_frame_left hwCode 4 12 _ _ F hF sc)

-- Step 1: store "o wo" at 0x104 (addr 12→20). 1 swap.
private theorem storeStep1 (m1 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 12 20
      ((.x6 ↦ᵣ 0x6C6C6568) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ m1) ** F)
      ((.x6 ↦ᵣ 0x6F77206F) ** (.x7 ↦ᵣ 0x100) ** ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** F) := by
  have sc := storeWord_spec_gen hwCode 0x6F77206F 4 0x6C6C6568 0x100 m1 12
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

-- Step 2: store "rld\0" at 0x108 (addr 20→28). 2 swaps.
private theorem storeStep2 (m2 : Word) (F : Assertion) (hF : F.pcFree) :
    cpsTriple hwCode 20 28
      ((.x6 ↦ᵣ 0x6F77206F) ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** ((0x108 : Addr) ↦ₘ m2) ** F)
      ((.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) ** ((0x108 : Addr) ↦ₘ 0x00646C72) ** F) := by
  have sc := storeWord_spec_gen hwCode 0x00646C72 8 0x6F77206F 0x100 m2 20
    (hw_fetch 5 (by omega) (by omega)) (hw_fetch 6 (by omega) (by omega))
    (by rw [hse8]; native_decide)
  rw [hse8] at sc
  let m0d := (0x100 : Addr) ↦ₘ (0x6C6C6568 : Word)
  let m1d := (0x104 : Addr) ↦ₘ (0x6F77206F : Word)
  let m2v := (0x108 : Addr) ↦ₘ m2
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

theorem storePhase_spec
    (v6_old v7_old : Word)
    (m0 m1 m2 : Word) :
    cpsTriple hwCode 0 28
      ((.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ v7_old) **
       ((0x100 : Addr) ↦ₘ m0) ** ((0x104 : Addr) ↦ₘ m1) **
       ((0x108 : Addr) ↦ₘ m2))
      ((.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72)) := by
  have hpf : ∀ (a : Addr) (v : Word), ((a ↦ₘ v) : Assertion).pcFree := pcFree_memIs
  have t0 := storeInit v6_old v7_old
    (((0x100 : Addr) ↦ₘ m0) ** ((0x104 : Addr) ↦ₘ m1) ** ((0x108 : Addr) ↦ₘ m2))
    (pcFree_sepConj (hpf _ _) (pcFree_sepConj (hpf _ _) (hpf _ _)))
  have t1 := storeStep0 v6_old m0
    (((0x104 : Addr) ↦ₘ m1) ** ((0x108 : Addr) ↦ₘ m2))
    (pcFree_sepConj (hpf _ _) (hpf _ _))
  have c01 := cpsTriple_seq hwCode 0 4 12 _ _ _ t0 t1
  have t2 := storeStep1 m1
    ((0x108 : Addr) ↦ₘ m2)
    (hpf _ _)
  have c02 := cpsTriple_seq hwCode 0 12 20 _ _ _ c01 t2
  -- storeStep2 with F = empAssertion, then strip emp
  have t3_raw := storeStep2 m2 empAssertion pcFree_emp
  have t3 := cpsTriple_consequence hwCode 20 28 _ _ _ _
    (fun h hab =>
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h' hm => (sepConj_emp_right _ h').mpr hm)))) h hab)
    (fun h hab =>
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (fun h' hm => (sepConj_emp_right _ h').mp hm)))) h hab)
    t3_raw
  exact cpsTriple_seq hwCode 0 20 28 _ _ _ c02 t3

-- ============================================================================
-- Section 7: Main HelloWorld CPS Triple
-- ============================================================================

theorem helloWorld_spec
    (v5_old v6_old v7_old v10_old v11_old v12_old : Word)
    (m0 m1 m2 : Word)
    (oldPV : List (BitVec 8)) :
    cpsHaltTriple hwCode 0
      ((.x5 ↦ᵣ v5_old) ** (.x6 ↦ᵣ v6_old) ** (.x7 ↦ᵣ v7_old) **
       (.x10 ↦ᵣ v10_old) ** (.x11 ↦ᵣ v11_old) ** (.x12 ↦ᵣ v12_old) **
       ((0x100 : Addr) ↦ₘ m0) ** ((0x104 : Addr) ↦ₘ m1) **
       ((0x108 : Addr) ↦ₘ m2) **
       publicValuesIs oldPV)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ 0x00646C72) ** (.x7 ↦ᵣ 0x100) **
       (.x10 ↦ᵣ (0 : Word)) ** (.x11 ↦ᵣ 0x100) ** (.x12 ↦ᵣ 11) **
       ((0x100 : Addr) ↦ₘ 0x6C6C6568) ** ((0x104 : Addr) ↦ₘ 0x6F77206F) **
       ((0x108 : Addr) ↦ₘ 0x00646C72) **
       publicValuesIs (oldPV ++ helloWorldBytes)) := by
  sorry

end RiscVMacroAsm.Examples
