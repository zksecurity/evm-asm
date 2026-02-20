/-
  EvmAsm.InstructionSpecs

  Separation logic specifications for each RISC-V instruction using cpsTriple
  (or cpsBranch for conditional branches).

  Each lemma:
  1. States the separation logic spec of a single instruction
  2. Proves it by unfolding the execution semantics

  Key design decisions:
  - Use separating conjunction (**) which implicitly enforces register distinctness
  - Provide multiple specs per instruction for different aliasing patterns
  - Postconditions preserve all source registers to avoid resource dropping
  - x0 writes are handled specially (writing to x0 is a no-op)
-/

import EvmAsm.Basic
import EvmAsm.Instructions
import EvmAsm.SepLogic
import EvmAsm.Execution
import EvmAsm.CPSSpec

namespace EvmAsm

-- ============================================================================
-- ALU Instructions (Register-Register): All Distinct Case
-- ============================================================================

/-- ADD rd, rs1, rs2: rd := rs1 + rs2 (all registers distinct)
    The separating conjunction enforces rd ≠ rs1 ≠ rs2 -/
theorem add_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADD rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADD instruction
  have hfetch : loadProgram base [Instr.ADD rd rs1 rs2] base = some (Instr.ADD rd rs1 rs2) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrs1, hrs2, hrd⟩ := holdsFor_sepConj_regIs_regIs_regIs hinner
  -- Compute next state
  let result := v1 + v2
  have hnext : execInstrBr st (Instr.ADD rd rs1 rs2) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1, hrs2]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADD rd rs1 rs2]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_regIs_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_regIs rd result))) hR) (st.setReg rd result) (base + 4) h1

/-- ADD rd, rd, rs2: rd := rd + rs2 (rd = rs1, rs2 distinct) -/
theorem add_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    let code := loadProgram base [Instr.ADD rd rd rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    let post := (rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADD instruction
  have hfetch : loadProgram base [Instr.ADD rd rd rs2] base = some (Instr.ADD rd rd rs2) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  -- Compute next state
  let result := v1 + v2
  have hnext : execInstrBr st (Instr.ADD rd rd rs2) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrd_val, hrs2_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADD rd rd rs2]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ result) ** (rs2 ↦ᵣ v2) ** R
    -- Rewrite precondition using associativity: ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)) ** R = (rd ↦ᵣ v1) ** ((rs2 ↦ᵣ v2) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_assoc.1 hPR
    -- Apply frame preservation for rd
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    -- Rewrite back using associativity: (rd ↦ᵣ result) ** ((rs2 ↦ᵣ v2) ** R) = ((rd ↦ᵣ result) ** (rs2 ↦ᵣ v2)) ** R
    have h2 := EvmAsm.holdsFor_sepConj_assoc.2 h1
    -- Apply PC preservation
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (base + 4) h2

/-- ADD rd, rs1, rd: rd := rs1 + rd (rd = rs2, rs1 distinct) -/
theorem add_spec_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rs1 ≠ rd) :
    let code := loadProgram base [Instr.ADD rd rs1 rd]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADD instruction
  have hfetch : loadProgram base [Instr.ADD rd rs1 rd] base = some (Instr.ADD rd rs1 rd) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrs1_val, hrd_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  -- Compute next state
  let result := v1 + v2
  have hnext : execInstrBr st (Instr.ADD rd rs1 rd) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1_val, hrd_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADD rd rs1 rd]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rs1 ↦ᵣ v1) ** (rd ↦ᵣ result) ** R
    -- Rearrange: ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2)) ** R = (rd ↦ᵣ v2) ** ((rs1 ↦ᵣ v1) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_pull_second.1 hPR
    -- Apply frame preservation for rd
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs1 ↦ᵣ v1) ** R) hrd_ne_x0 hPR'
    -- Rearrange back: (rd ↦ᵣ result) ** ((rs1 ↦ᵣ v1) ** R) = ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ result)) ** R
    have h2 := EvmAsm.holdsFor_sepConj_pull_second.2 h1
    -- Apply PC preservation
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rd result)) hR) (st.setReg rd result) (base + 4) h2

/-- ADD rd, rd, rd: rd := rd + rd = 2 * rd (all same) -/
theorem add_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADD rd rd rd]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (v + v))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADD instruction
  have hfetch : loadProgram base [Instr.ADD rd rd rd] base = some (Instr.ADD rd rd rd) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  let result := v + v
  have hnext : execInstrBr st (Instr.ADD rd rd rd) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result]
    have hrd_holds := holdsFor_sepConj_elim_left hPR
    have hrd : st.getReg rd = v := (holdsFor_regIs rd v st).mp hrd_holds
    simp [hrd]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADD rd rd rd]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + 4) h1

/-- SUB rd, rs1, rs2: rd := rs1 - rs2 (all registers distinct) -/
theorem sub_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch SUB instruction
  have hfetch : loadProgram base [Instr.SUB rd rs1 rs2] base = some (Instr.SUB rd rs1 rs2) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrs1, hrs2, hrd⟩ := holdsFor_sepConj_regIs_regIs_regIs hinner
  -- Compute next state
  let result := v1 - v2
  have hnext : execInstrBr st (Instr.SUB rd rs1 rs2) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1, hrs2]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.SUB rd rs1 rs2]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_regIs_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_regIs rd result))) hR) (st.setReg rd result) (base + 4) h1

/-- SUB rd, rd, rs2: rd := rd - rs2 -/
theorem sub_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rd rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    let post := (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch SUB instruction
  have hfetch : loadProgram base [Instr.SUB rd rd rs2] base = some (Instr.SUB rd rd rs2) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrd_val : st.getReg rd = v1 := by
    exact (holdsFor_regIs rd v1 st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v2 := by
    exact (holdsFor_regIs rs2 v2 st).mp (holdsFor_sepConj_elim_right hinner)
  -- Compute next state
  let result := v1 - v2
  have hnext : execInstrBr st (Instr.SUB rd rd rs2) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrd_val, hrs2_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.SUB rd rd rs2]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := EvmAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := EvmAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (base + 4) h2

/-- SUB rd, rd, rd: rd := rd - rd = 0 -/
theorem sub_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rd rd]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ 0)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch SUB instruction
  have hfetch : loadProgram base [Instr.SUB rd rd rd] base = some (Instr.SUB rd rd rd) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state (v - v = 0)
  let result : Word := 0
  have hnext : execInstrBr st (Instr.SUB rd rd rd) = (st.setReg rd result).setPC (st.pc + 4) := by
    have hrd_holds := holdsFor_sepConj_elim_left hPR
    have hrd : st.getReg rd = v := (holdsFor_regIs rd v st).mp hrd_holds
    simp [execInstrBr, result, hrd, BitVec.sub_self]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.SUB rd rd rd]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ 0) ** R
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + 4) h1

-- ============================================================================
-- ALU Instructions (Immediate)
-- ============================================================================

/-- ADDI rd, rs1, imm: rd := rs1 + sext(imm) (registers distinct) -/
theorem addi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADDI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADDI instruction
  have hfetch : loadProgram base [Instr.ADDI rd rs1 imm] base = some (Instr.ADDI rd rs1 imm) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v1 := by
    exact (holdsFor_regIs rs1 v1 st).mp (holdsFor_sepConj_elim_left hinner)
  -- Compute next state
  let result := v1 + signExtend12 imm
  have hnext : execInstrBr st (Instr.ADDI rd rs1 imm) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADDI rd rs1 imm]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Rearrange: ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)) ** R → (rd ↦ᵣ v_old) ** ((rs1 ↦ᵣ v1) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_pull_second.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs1 ↦ᵣ v1) ** R) hrd_ne_x0 hPR'
    have h2 := EvmAsm.holdsFor_sepConj_pull_second.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rd result)) hR) (st.setReg rd result) (base + 4) h2

/-- ADDI rd, rd, imm: rd := rd + sext(imm) (same register) -/
theorem addi_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADDI rd rd imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (v + signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch ADDI instruction
  have hfetch : loadProgram base [Instr.ADDI rd rd imm] base = some (Instr.ADDI rd rd imm) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  let result := v + signExtend12 imm
  have hnext : execInstrBr st (Instr.ADDI rd rd imm) = (st.setReg rd result).setPC (st.pc + 4) := by
    have hrd_holds := holdsFor_sepConj_elim_left hPR
    have hrd : st.getReg rd = v := (holdsFor_regIs rd v st).mp hrd_holds
    simp [execInstrBr, result, hrd]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.ADDI rd rd imm]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + 4) h1

-- ============================================================================
-- Upper Immediate Instructions
-- ============================================================================

/-- LUI rd, imm: rd := imm << 12 -/
theorem lui_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LUI rd imm]
    let entry := base
    let exit_ := base + 4
    let result := (imm.zeroExtend 32 : Word) <<< 12
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch LUI instruction
  have hfetch : loadProgram base [Instr.LUI rd imm] base = some (Instr.LUI rd imm) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  let result := (imm.zeroExtend 32 : Word) <<< 12
  have hnext : execInstrBr st (Instr.LUI rd imm) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.LUI rd imm]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + 4) h1

/-- AUIPC rd, imm: rd := PC + (imm << 12) -/
theorem auipc_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.AUIPC rd imm]
    let entry := base
    let exit_ := base + 4
    let result := base + ((imm.zeroExtend 32 : Word) <<< 12)
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch AUIPC instruction
  have hfetch : loadProgram base [Instr.AUIPC rd imm] base = some (Instr.AUIPC rd imm) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  let result := base + ((imm.zeroExtend 32 : Word) <<< 12)
  have hnext : execInstrBr st (Instr.AUIPC rd imm) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hpc]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.AUIPC rd imm]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · -- stepN 1 reaches the computed state
    simp [stepN, hstep, Option.bind]
  · -- PC = exit_
    simp [MachineState.setPC]
  · -- Postcondition holds: (rd ↦ᵣ result) ** R
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + 4) h1

-- ============================================================================
-- Memory Instructions
-- ============================================================================

/-- LW rd, offset(rs1): rd := mem[rs1 + sext(offset)] (registers distinct) -/
theorem lw_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.LW rd rs1 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (addr ↦ₘ mem_val)
    let post := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch LW instruction
  have hfetch : loadProgram base [Instr.LW rd rs1 offset] base = some (Instr.LW rd rs1 offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v_addr := by
    exact (holdsFor_regIs rs1 v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  have hmem_val : st.getMem (v_addr + signExtend12 offset) = mem_val := by
    exact (holdsFor_memIs _ _ st).mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hinner))
  -- Compute next state
  let result := mem_val
  have hnext : execInstrBr st (Instr.LW rd rs1 offset) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1_val, hmem_val]
  -- Execute one step (LW checks isValidMemAccess)
  have hstep : step (loadProgram base [Instr.LW rd rs1 offset]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    have := step_lw _ _ _ _ _ (by rw [hpc]; exact hfetch) (by rw [hrs1_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    -- rd is the second element: pull it to front, apply setReg, push back
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_assoc.mp h1
    have h3 := holdsFor_sepConj_regIs_setReg (v' := result) (R := ((v_addr + signExtend12 offset ↦ₘ mem_val) ** ((rs1 ↦ᵣ v_addr) ** R))) hrd_ne_x0 h2
    have h4 := holdsFor_sepConj_assoc.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rd result) (pcFree_memIs _ mem_val))) hR)
      (st.setReg rd result) (base + 4) h5

/-- LW rd, offset(rd): rd := mem[rd + sext(offset)] (same register) -/
theorem lw_spec_same (rd : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.LW rd rd offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rd ↦ᵣ v_addr) ** (addr ↦ₘ mem_val)
    let post := (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch LW instruction
  have hfetch : loadProgram base [Instr.LW rd rd offset] base = some (Instr.LW rd rd offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrd_val : st.getReg rd = v_addr := by
    exact (holdsFor_regIs rd v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  have hmem_val : st.getMem (v_addr + signExtend12 offset) = mem_val := by
    exact (holdsFor_memIs _ _ st).mp (holdsFor_sepConj_elim_right hinner)
  -- Compute next state
  let result := mem_val
  have hnext : execInstrBr st (Instr.LW rd rd offset) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrd_val, hmem_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.LW rd rd offset]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    have := step_lw _ _ _ _ _ (by rw [hpc]; exact hfetch) (by rw [hrd_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    -- Rearrange: ((rd ↦ᵣ v_addr) ** (addr ↦ₘ mem_val)) ** R → (rd ↦ᵣ v_addr) ** ((addr ↦ₘ mem_val) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := ((v_addr + signExtend12 offset ↦ₘ mem_val) ** R)) hrd_ne_x0 hPR'
    have h2 := EvmAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_memIs _ mem_val)) hR)
      (st.setReg rd result) (base + 4) h2

/-- SW rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 (registers distinct) -/
theorem sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.SW rs1 rs2 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ mem_old)
    let post := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch SW instruction
  have hfetch : loadProgram base [Instr.SW rs1 rs2 offset] base = some (Instr.SW rs1 rs2 offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v_addr := by
    exact (holdsFor_regIs rs1 v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v_data := by
    exact (holdsFor_regIs rs2 v_data st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hinner))
  -- Compute next state
  let addr := v_addr + signExtend12 offset
  have hnext : execInstrBr st (Instr.SW rs1 rs2 offset) = (st.setMem addr v_data).setPC (st.pc + 4) := by
    simp [execInstrBr, addr, hrs1_val, hrs2_val]
  -- Execute one step (SW checks isValidMemAccess)
  have hstep : step (loadProgram base [Instr.SW rs1 rs2 offset]) st = some ((st.setMem addr v_data).setPC (base + 4)) := by
    have := step_sw _ _ _ _ _ (by rw [hpc]; exact hfetch) (by rw [hrs1_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setMem addr v_data).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    -- Memory is the third element: pull to front, apply setMem, push back
    -- Rearrange: ((rs1 ** (rs2 ** mem)) ** R) → ((rs2 ** mem) ** (rs1 ** R)) → (mem ** (rs2 ** (rs1 ** R)))
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    -- h2 : (addr ↦ₘ mem_old) ** ((rs2 ↦ᵣ v_data) ** ((rs1 ↦ᵣ v_addr) ** R))
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v_data) h2
    -- h3 : (addr ↦ₘ v_data) ** ((rs2 ↦ᵣ v_data) ** ((rs1 ↦ᵣ v_addr) ** R))
    -- Rearrange back
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    -- h5 : ((rs1 ↦ᵣ v_addr) ** ((rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data))) ** R
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rs2 v_data) (pcFree_memIs _ v_data))) hR)
      (st.setMem addr v_data) (base + 4) h5

/-- SW rs, offset(rs): mem[rs + sext(offset)] := rs (same register) -/
theorem sw_spec_same (rs : Reg) (v : Word) (mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.SW rs rs offset]
    let entry := base
    let exit_ := base + 4
    let addr := v + signExtend12 offset
    let pre := (rs ↦ᵣ v) ** (addr ↦ₘ mem_old)
    let post := (rs ↦ᵣ v) ** (addr ↦ₘ v)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch SW instruction
  have hfetch : loadProgram base [Instr.SW rs rs offset] base = some (Instr.SW rs rs offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs_val : st.getReg rs = v := by
    exact (holdsFor_regIs rs v st).mp (holdsFor_sepConj_elim_left hinner)
  -- Compute next state
  let addr := v + signExtend12 offset
  have hnext : execInstrBr st (Instr.SW rs rs offset) = (st.setMem addr v).setPC (st.pc + 4) := by
    simp [execInstrBr, addr, hrs_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.SW rs rs offset]) st = some ((st.setMem addr v).setPC (base + 4)) := by
    have := step_sw _ _ _ _ _ (by rw [hpc]; exact hfetch) (by rw [hrs_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setMem addr v).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: (rs ↦ᵣ v) ** (addr ↦ₘ v)
    -- Rearrange: ((rs ↦ᵣ v) ** (addr ↦ₘ mem_old)) ** R → (addr ↦ₘ mem_old) ** ((rs ↦ᵣ v) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_pull_second.1 hPR
    have h1 := holdsFor_sepConj_memIs_setMem (v' := v) hPR'
    have h2 := EvmAsm.holdsFor_sepConj_pull_second.2 h1
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs v) (pcFree_memIs _ v)) hR)
      (st.setMem addr v) (base + 4) h2

-- ============================================================================
-- Branch Instructions (use cpsBranch for two exits)
-- ============================================================================

/-- BEQ rs1, rs2, offset: branch if rs1 = rs2 (registers distinct) -/
theorem beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BEQ rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.BEQ rs1 rs2 offset] base = some (Instr.BEQ rs1 rs2 offset) := by
    simp [loadProgram, BitVec.sub_self]
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v1 :=
    (holdsFor_regIs rs1 v1 st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v2 :=
    (holdsFor_regIs rs2 v2 st).mp (holdsFor_sepConj_elim_right hinner)
  have hstep : step (loadProgram base [Instr.BEQ rs1 rs2 offset]) st =
      some (execInstrBr st (Instr.BEQ rs1 rs2 offset)) := by
    unfold step; rw [hpc, hfetch]
  by_cases heq : v1 = v2
  · -- Branch taken: v1 = v2
    have hnext : execInstrBr st (Instr.BEQ rs1 rs2 offset) = st.setPC (base + signExtend13 offset) := by
      simp [execInstrBr, hrs1_val, hrs2_val, hpc, heq]
    refine ⟨1, st.setPC (base + signExtend13 offset), ?_, ?_⟩
    · simp [stepN, hstep, hnext, Option.bind]
    · left; refine ⟨by simp [MachineState.setPC], ?_⟩
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      have hpq' := sepConj_mono_left (sepConj_mono_right
        (fun h hq => (sepConj_pure_right _ _ h).mpr ⟨hq, heq⟩)) hp hpq
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_pure _))) hR)
        st (base + signExtend13 offset) ⟨hp, hcompat, hpq'⟩
  · -- Branch not taken: v1 ≠ v2
    have hnext : execInstrBr st (Instr.BEQ rs1 rs2 offset) = st.setPC (base + 4) := by
      simp [execInstrBr, hrs1_val, hrs2_val, hpc, beq_eq_false_iff_ne.mpr heq]
    refine ⟨1, st.setPC (base + 4), ?_, ?_⟩
    · simp [stepN, hstep, hnext, Option.bind]
    · right; refine ⟨by simp [MachineState.setPC], ?_⟩
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      have hpq' := sepConj_mono_left (sepConj_mono_right
        (fun h hq => (sepConj_pure_right _ _ h).mpr ⟨hq, heq⟩)) hp hpq
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_pure _))) hR)
        st (base + 4) ⟨hp, hcompat, hpq'⟩

/-- BEQ rs, rs, offset: branch if rs = rs (always taken, same register) -/
theorem beq_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    let code := loadProgram base [Instr.BEQ rs rs offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs ↦ᵣ v)
    cpsBranch code entry pre
      taken_exit (rs ↦ᵣ v)
      not_taken_exit (rs ↦ᵣ v) := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.BEQ rs rs offset] base = some (Instr.BEQ rs rs offset) := by
    simp [loadProgram, BitVec.sub_self]
  have hrs_holds := holdsFor_sepConj_elim_left hPR
  have hrs_val : st.getReg rs = v := (holdsFor_regIs rs v st).mp hrs_holds
  -- BEQ rs rs is always taken (rs == rs = true)
  have hnext : execInstrBr st (Instr.BEQ rs rs offset) = st.setPC (base + signExtend13 offset) := by
    simp [execInstrBr, hrs_val, hpc]
  have hstep : step (loadProgram base [Instr.BEQ rs rs offset]) st =
      some (st.setPC (base + signExtend13 offset)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext]
  refine ⟨1, st.setPC (base + signExtend13 offset), ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · left; exact ⟨by simp [MachineState.setPC],
      holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rs v) hR) st (base + signExtend13 offset) hPR⟩

/-- BNE rs1, rs2, offset: branch if rs1 ≠ rs2 (registers distinct) -/
theorem bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BNE rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.BNE rs1 rs2 offset] base = some (Instr.BNE rs1 rs2 offset) := by
    simp [loadProgram, BitVec.sub_self]
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v1 :=
    (holdsFor_regIs rs1 v1 st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v2 :=
    (holdsFor_regIs rs2 v2 st).mp (holdsFor_sepConj_elim_right hinner)
  have hstep : step (loadProgram base [Instr.BNE rs1 rs2 offset]) st =
      some (execInstrBr st (Instr.BNE rs1 rs2 offset)) := by
    unfold step; rw [hpc, hfetch]
  by_cases heq : v1 = v2
  · -- Branch not taken: v1 = v2
    have hnext : execInstrBr st (Instr.BNE rs1 rs2 offset) = st.setPC (base + 4) := by
      simp [execInstrBr, hrs1_val, hrs2_val, hpc, heq]
    refine ⟨1, st.setPC (base + 4), ?_, ?_⟩
    · simp [stepN, hstep, hnext, Option.bind]
    · right; refine ⟨by simp [MachineState.setPC], ?_⟩
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      have hpq' := sepConj_mono_left (sepConj_mono_right
        (fun h hq => (sepConj_pure_right _ _ h).mpr ⟨hq, heq⟩)) hp hpq
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_pure _))) hR)
        st (base + 4) ⟨hp, hcompat, hpq'⟩
  · -- Branch taken: v1 ≠ v2
    have hnext : execInstrBr st (Instr.BNE rs1 rs2 offset) = st.setPC (base + signExtend13 offset) := by
      simp [execInstrBr, hrs1_val, hrs2_val, hpc, bne_iff_ne.mpr heq]
    refine ⟨1, st.setPC (base + signExtend13 offset), ?_, ?_⟩
    · simp [stepN, hstep, hnext, Option.bind]
    · left; refine ⟨by simp [MachineState.setPC], ?_⟩
      obtain ⟨hp, hcompat, hpq⟩ := hPR
      have hpq' := sepConj_mono_left (sepConj_mono_right
        (fun h hq => (sepConj_pure_right _ _ h).mpr ⟨hq, heq⟩)) hp hpq
      exact holdsFor_pcFree_setPC
        (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_sepConj (pcFree_regIs rs2 v2) (pcFree_pure _))) hR)
        st (base + signExtend13 offset) ⟨hp, hcompat, hpq'⟩

/-- BNE rs, rs, offset: branch if rs ≠ rs (never taken, same register) -/
theorem bne_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    let code := loadProgram base [Instr.BNE rs rs offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs ↦ᵣ v)
    cpsBranch code entry pre
      taken_exit (rs ↦ᵣ v)
      not_taken_exit (rs ↦ᵣ v) := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.BNE rs rs offset] base = some (Instr.BNE rs rs offset) := by
    simp [loadProgram, BitVec.sub_self]
  have hrs_holds := holdsFor_sepConj_elim_left hPR
  have hrs_val : st.getReg rs = v := (holdsFor_regIs rs v st).mp hrs_holds
  -- BNE rs rs is never taken (rs != rs = false)
  have hnext : execInstrBr st (Instr.BNE rs rs offset) = st.setPC (base + 4) := by
    simp [execInstrBr, hrs_val, hpc]
  have hstep : step (loadProgram base [Instr.BNE rs rs offset]) st =
      some (st.setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext]
  refine ⟨1, st.setPC (base + 4), ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · right; exact ⟨by simp [MachineState.setPC],
      holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rs v) hR) st (base + 4) hPR⟩

-- ============================================================================
-- Jump Instructions
-- ============================================================================

/-- JAL rd, offset: rd := PC + 4; PC := PC + sext(offset) -/
theorem jal_spec (rd : Reg) (v_old : Word) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JAL rd offset]
    let entry := base
    let exit_ := base + signExtend21 offset
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch JAL instruction
  have hfetch : loadProgram base [Instr.JAL rd offset] base = some (Instr.JAL rd offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  let result := base + 4
  have hnext : execInstrBr st (Instr.JAL rd offset) = (st.setReg rd result).setPC (base + signExtend21 offset) := by
    simp [execInstrBr, result, hpc]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.JAL rd offset]) st = some ((st.setReg rd result).setPC (base + signExtend21 offset)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext]
  refine ⟨1, (st.setReg rd result).setPC (base + signExtend21 offset), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) (base + signExtend21 offset) h1

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 (distinct) -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rs1 offset]
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch JALR instruction
  have hfetch : loadProgram base [Instr.JALR rd rs1 offset] base = some (Instr.JALR rd rs1 offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register values from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v1 := by
    exact (holdsFor_regIs rs1 v1 st).mp (holdsFor_sepConj_elim_left hinner)
  -- Compute next state
  let result := base + 4
  have hnext : execInstrBr st (Instr.JALR rd rs1 offset) = (st.setReg rd result).setPC ((v1 + signExtend12 offset) &&& ~~~1) := by
    simp [execInstrBr, result, hpc, hrs1_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.JALR rd rs1 offset]) st = some ((st.setReg rd result).setPC ((v1 + signExtend12 offset) &&& ~~~1)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext]
  refine ⟨1, (st.setReg rd result).setPC ((v1 + signExtend12 offset) &&& ~~~1), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Rearrange: ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)) ** R → (rd ↦ᵣ v_old) ** ((rs1 ↦ᵣ v1) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_pull_second.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs1 ↦ᵣ v1) ** R) hrd_ne_x0 hPR'
    have h2 := EvmAsm.holdsFor_sepConj_pull_second.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v1) (pcFree_regIs rd result)) hR) (st.setReg rd result) ((v1 + signExtend12 offset) &&& ~~~1) h2

/-- JALR rd, rd, offset: rd := PC + 4; PC := (rd + sext(offset)) & ~1 (same) -/
theorem jalr_spec_same (rd : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rd offset]
    let entry := base
    let exit_ := (v + signExtend12 offset) &&& (~~~1)
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch JALR instruction
  have hfetch : loadProgram base [Instr.JALR rd rd offset] base = some (Instr.JALR rd rd offset) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register value from precondition
  have hrd_holds := holdsFor_sepConj_elim_left hPR
  have hrd_val : st.getReg rd = v := (holdsFor_regIs rd v st).mp hrd_holds
  -- Compute next state
  let result := base + 4
  have hnext : execInstrBr st (Instr.JALR rd rd offset) = (st.setReg rd result).setPC ((v + signExtend12 offset) &&& ~~~1) := by
    simp [execInstrBr, result, hpc, hrd_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.JALR rd rd offset]) st = some ((st.setReg rd result).setPC ((v + signExtend12 offset) &&& ~~~1)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext]
  refine ⟨1, (st.setReg rd result).setPC ((v + signExtend12 offset) &&& ~~~1), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR) (st.setReg rd result) ((v + signExtend12 offset) &&& ~~~1) h1

-- ============================================================================
-- Pseudo Instructions
-- ============================================================================

/-- MV rd, rs: rd := rs (pseudo for ADDI rd, rs, 0) -/
theorem mv_spec (rd rs : Reg) (v v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MV rd rs]
    let entry := base
    let exit_ := base + 4
    let pre := (rs ↦ᵣ v) ** (rd ↦ᵣ v_old)
    let post := (rs ↦ᵣ v) ** (rd ↦ᵣ v)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch MV instruction
  have hfetch : loadProgram base [Instr.MV rd rs] base = some (Instr.MV rd rs) := by
    simp [loadProgram, BitVec.sub_self]
  -- Extract register value from precondition
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs_val : st.getReg rs = v := by
    exact (holdsFor_regIs rs v st).mp (holdsFor_sepConj_elim_left hinner)
  -- Compute next state
  have hnext : execInstrBr st (Instr.MV rd rs) = (st.setReg rd v).setPC (st.pc + 4) := by
    simp [execInstrBr, hrs_val]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.MV rd rs]) st = some ((st.setReg rd v).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd v).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Rearrange: ((rs ↦ᵣ v) ** (rd ↦ᵣ v_old)) ** R → (rd ↦ᵣ v_old) ** ((rs ↦ᵣ v) ** R)
    have hPR' := EvmAsm.holdsFor_sepConj_pull_second.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := v) (R := (rs ↦ᵣ v) ** R) hrd_ne_x0 hPR'
    have h2 := EvmAsm.holdsFor_sepConj_pull_second.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs v) (pcFree_regIs rd v)) hR) (st.setReg rd v) (base + 4) h2

/-- LI rd, imm: rd := imm (pseudo for loading immediate) -/
theorem li_spec (rd : Reg) (v_old imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LI rd imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ imm)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR st hPR hpc
  -- Fetch LI instruction
  have hfetch : loadProgram base [Instr.LI rd imm] base = some (Instr.LI rd imm) := by
    simp [loadProgram, BitVec.sub_self]
  -- Compute next state
  have hnext : execInstrBr st (Instr.LI rd imm) = (st.setReg rd imm).setPC (st.pc + 4) := by
    simp [execInstrBr]
  -- Execute one step
  have hstep : step (loadProgram base [Instr.LI rd imm]) st = some ((st.setReg rd imm).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd imm).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have h1 := holdsFor_sepConj_regIs_setReg (v' := imm) hrd_ne_x0 hPR
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd imm) hR) (st.setReg rd imm) (base + 4) h1

/-- NOP: no operation (pseudo for ADDI x0, x0, 0) -/
theorem nop_spec (base : Addr) :
    let code := loadProgram base [Instr.NOP]
    let entry := base
    let exit_ := base + 4
    cpsTriple code entry exit_
      empAssertion
      empAssertion := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.NOP] base = some Instr.NOP := by
    simp [loadProgram, BitVec.sub_self]
  have hstep : step (loadProgram base [Instr.NOP]) st = some (execInstr st Instr.NOP) := by
    unfold step; rw [hpc, hfetch]; rfl
  have hnext : execInstr st Instr.NOP = st.setPC (st.pc + 4) := by
    simp [execInstr]
  refine ⟨1, st.setPC (st.pc + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, hnext, Option.bind]
  · simp [MachineState.setPC, hpc]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree_emp hR) st (st.pc + 4) hPR

-- ============================================================================
-- System Instructions
-- ============================================================================

/-- FENCE: memory fence (NOP in single-hart zkVM) -/
theorem fence_spec (base : Addr) :
    let code := loadProgram base [Instr.FENCE]
    let entry := base
    let exit_ := base + 4
    cpsTriple code entry exit_
      empAssertion
      empAssertion := by
  simp only
  intro R hR st hPR hpc
  have hfetch : loadProgram base [Instr.FENCE] base = some Instr.FENCE := by
    simp [loadProgram, BitVec.sub_self]
  have hstep : step (loadProgram base [Instr.FENCE]) st = some (execInstr st Instr.FENCE) := by
    unfold step; rw [hpc, hfetch]; rfl
  have hnext : execInstr st Instr.FENCE = st.setPC (st.pc + 4) := by
    simp [execInstr]
  refine ⟨1, st.setPC (st.pc + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, hnext, Option.bind]
  · simp [MachineState.setPC, hpc]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree_emp hR) st (st.pc + 4) hPR

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Instruction Specifications Summary

  This module provides separation logic specifications for RISC-V instructions
  using CPS-style specifications with built-in frame rule.

  ### Key Design Decisions

  1. **Separating Conjunction (**)**: Used to enforce register distinctness implicitly.
     If we have `(rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)`, this can only be satisfied when
     rs1 ≠ rd, because separating conjunction requires disjoint resources.

  2. **Multiple Specs per Instruction**: Each instruction has multiple specs for
     different aliasing patterns (e.g., `add_spec`, `add_spec_rd_eq_rs1`,
     `add_spec_all_same`). This avoids:
     - Resource dropping (losing rs1, rs2 in postcondition)
     - Contradictions when registers alias

  3. **Frame Preservation**: All source registers appear in both pre and post
     conditions with their correct values, so the frame rule works properly.

  4. **x0 Handling**: All specs require `rd ≠ .x0` since writes to x0 are no-ops.

  ### Example Pattern

  For `ADD rd, rs1, rs2`:
  - `add_spec`: rd, rs1, rs2 all distinct (uses `** ** **`)
  - `add_spec_rd_eq_rs1`: rd = rs1 ≠ rs2 (uses `**`, rd appears once)
  - `add_spec_rd_eq_rs2`: rd = rs2 ≠ rs1 (uses `**`, rd appears once)
  - `add_spec_all_same`: rd = rs1 = rs2 (single register)

  This pattern applies to all ALU and memory instructions.
-/

-- ============================================================================
-- Ownership variants (regOwn / memOwn)
-- ============================================================================

/-! ### regOwn / memOwn variants

These specs replace the meaningless `v_old` / `mem_old` parameter with
`regOwn r` or `memOwn a`, expressing "we own the resource, value unspecified".
Each is a one-liner delegating to the original spec via a CPS lifting helper.
-/

-- Tail-position regOwn (P ** regOwn rd)

theorem add_spec_own (rd rs1 rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADD rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs1_3, hrest4⟩ := hpre1
  obtain ⟨h5, h6, hd56, hu56, hrs2_5, ⟨v_old, hrd6⟩⟩ := hrest4
  exact add_spec rd rs1 rs2 v1 v2 v_old base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12,
      ⟨h3, h4, hd34, hu34, hrs1_3, ⟨h5, h6, hd56, hu56, hrs2_5, hrd6⟩⟩, hR2⟩ hpc

theorem sub_spec_own (rd rs1 rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs1_3, hrest4⟩ := hpre1
  obtain ⟨h5, h6, hd56, hu56, hrs2_5, ⟨v_old, hrd6⟩⟩ := hrest4
  exact sub_spec rd rs1 rs2 v1 v2 v_old base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12,
      ⟨h3, h4, hd34, hu34, hrs1_3, ⟨h5, h6, hd56, hu56, hrs2_5, hrd6⟩⟩, hR2⟩ hpc

theorem addi_spec_own (rd rs1 : Reg) (v1 : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADDI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs1_3, ⟨v_old, hrd4⟩⟩ := hpre1
  exact addi_spec rd rs1 v1 v_old imm base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12, ⟨h3, h4, hd34, hu34, hrs1_3, hrd4⟩, hR2⟩ hpc

theorem jalr_spec_own (rd rs1 : Reg) (v1 : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rs1 offset]
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs1_3, ⟨v_old, hrd4⟩⟩ := hpre1
  exact jalr_spec rd rs1 v1 v_old offset base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12, ⟨h3, h4, hd34, hu34, hrs1_3, hrd4⟩, hR2⟩ hpc

theorem mv_spec_own (rd rs : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MV rd rs]
    let entry := base
    let exit_ := base + 4
    let pre := (rs ↦ᵣ v) ** regOwn rd
    let post := (rs ↦ᵣ v) ** (rd ↦ᵣ v)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs_3, ⟨v_old, hrd4⟩⟩ := hpre1
  exact mv_spec rd rs v v_old base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12, ⟨h3, h4, hd34, hu34, hrs_3, hrd4⟩, hR2⟩ hpc

-- Tail-position memOwn (P ** memOwn addr)

theorem sw_spec_own (rs1 rs2 : Reg) (v_addr v_data : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.SW rs1 rs2 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn addr
    let post := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs1_3, hrest4⟩ := hpre1
  obtain ⟨h5, h6, hd56, hu56, hrs2_5, ⟨mem_old, hmem6⟩⟩ := hrest4
  exact sw_spec rs1 rs2 v_addr v_data mem_old offset base hvalid R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12,
      ⟨h3, h4, hd34, hu34, hrs1_3, ⟨h5, h6, hd56, hu56, hrs2_5, hmem6⟩⟩, hR2⟩ hpc

theorem sw_spec_same_own (rs : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.SW rs rs offset]
    let entry := base
    let exit_ := base + 4
    let addr := v + signExtend12 offset
    let pre := (rs ↦ᵣ v) ** memOwn addr
    let post := (rs ↦ᵣ v) ** (addr ↦ₘ v)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hpre1, hR2⟩ := hPR
  obtain ⟨h3, h4, hd34, hu34, hrs_3, ⟨mem_old, hmem4⟩⟩ := hpre1
  exact sw_spec_same rs v mem_old offset base hvalid R hR s
    ⟨hp, hcompat, h1, h2, hd12, hu12, ⟨h3, h4, hd34, hu34, hrs_3, hmem4⟩, hR2⟩ hpc

-- Standalone regOwn (regOwn rd is the entire precondition)

theorem lui_spec_own (rd : Reg) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LUI rd imm]
    let entry := base
    let exit_ := base + 4
    let result := BitVec.zeroExtend 32 imm <<< 12
    let pre := regOwn rd
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨v_old, hrd1⟩, hR2⟩ := hPR
  exact lui_spec rd v_old imm base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd, hu, hrd1, hR2⟩ hpc

theorem auipc_spec_own (rd : Reg) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.AUIPC rd imm]
    let entry := base
    let exit_ := base + 4
    let result := base + BitVec.zeroExtend 32 imm <<< 12
    let pre := regOwn rd
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨v_old, hrd1⟩, hR2⟩ := hPR
  exact auipc_spec rd v_old imm base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd, hu, hrd1, hR2⟩ hpc

theorem jal_spec_own (rd : Reg) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JAL rd offset]
    let entry := base
    let exit_ := base + signExtend21 offset
    let pre := regOwn rd
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨v_old, hrd1⟩, hR2⟩ := hPR
  exact jal_spec rd v_old offset base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd, hu, hrd1, hR2⟩ hpc

theorem li_spec_own (rd : Reg) (imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LI rd imm]
    let entry := base
    let exit_ := base + 4
    let pre := regOwn rd
    let post := (rd ↦ᵣ imm)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨v_old, hrd1⟩, hR2⟩ := hPR
  exact li_spec rd v_old imm base hrd_ne_x0 R hR s
    ⟨hp, hcompat, h1, h2, hd, hu, hrd1, hR2⟩ hpc

-- Middle-position regOwn (regOwn rd is between other assertions)

theorem lw_spec_own (rd rs1 : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let code := loadProgram base [Instr.LW rd rs1 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** regOwn rd ** (addr ↦ₘ mem_val)
    let post := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  simp only
  intro R hR s hPR hpc
  -- Decompose: ((rs1 ↦ᵣ v_addr) ** regOwn rd ** (addr ↦ₘ mem_val)) ** R
  obtain ⟨hp, hcompat, hPown_R⟩ := hPR
  -- Outer sepConj: (pre ** R)
  obtain ⟨h1, h2, hd12, hunion12, hpre1, hR2⟩ := hPown_R
  -- Inner: (rs1 ↦ᵣ v_addr) ** (regOwn rd ** (addr ↦ₘ mem_val))
  obtain ⟨h3, h4, hd34, hunion34, hrs1_3, hown_mem4⟩ := hpre1
  -- regOwn rd ** (addr ↦ₘ mem_val)
  obtain ⟨h5, h6, hd56, hunion56, ⟨v_old, hrd5⟩, hmem6⟩ := hown_mem4
  -- Reconstruct with regIs instead of regOwn
  have hPR' : (((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (v_addr + signExtend12 offset ↦ₘ mem_val)) ** R).holdsFor s :=
    ⟨hp, hcompat, h1, h2, hd12, hunion12,
      ⟨h3, h4, hd34, hunion34, hrs1_3, ⟨h5, h6, hd56, hunion56, hrd5, hmem6⟩⟩, hR2⟩
  exact lw_spec rd rs1 v_addr v_old mem_val offset base hrd_ne_x0 hvalid R hR s hPR' hpc

end EvmAsm
