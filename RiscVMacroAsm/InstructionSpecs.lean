/-
  RiscVMacroAsm.InstructionSpecs

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

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm

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
  -- First, derive register distinctness from the sepConj structure
  have h_pre := holdsFor_sepConj_elim_left hPR
  -- Derive inequalities from disjoint conditions (by destructuring temporarily)
  have hne12 : rs1 ≠ rs2 := by
    obtain ⟨_, _, h_rs1, h_rs2_rd, hd_outer, _, hrs1_holds, hrs2_rd_holds⟩ := h_pre
    obtain ⟨h_rs2, h_rd, hd_inner, hunion_inner, hrs2_holds, hrd_holds⟩ := hrs2_rd_holds
    simp only [regIs] at hrs1_holds hrs2_holds hrd_holds
    subst hrs1_holds hrs2_holds hrd_holds hunion_inner
    have := disjoint_left_of_disjoint_union_right hd_outer
    exact singletonReg_disjoint_imp_ne this
  have hne13 : rs1 ≠ rd := by
    obtain ⟨_, _, h_rs1, h_rs2_rd, hd_outer, _, hrs1_holds, hrs2_rd_holds⟩ := h_pre
    obtain ⟨h_rs2, h_rd, hd_inner, hunion_inner, hrs2_holds, hrd_holds⟩ := hrs2_rd_holds
    simp only [regIs] at hrs1_holds hrs2_holds hrd_holds
    subst hrs1_holds hrs2_holds hrd_holds hunion_inner
    have := disjoint_of_union_disjoint_right hd_inner hd_outer.symm
    exact singletonReg_disjoint_imp_ne this.symm
  have hne23 : rs2 ≠ rd := by
    obtain ⟨_, _, _, _, _, _, _, hrs2_rd_holds⟩ := h_pre
    obtain ⟨h_rs2, h_rd, hd_inner, _, hrs2_holds, hrd_holds⟩ := hrs2_rd_holds
    simp only [regIs] at hrs2_holds hrd_holds
    subst hrs2_holds hrd_holds
    exact singletonReg_disjoint_imp_ne hd_inner
  -- Extract register values using the new lemma
  have ⟨hrs1, hrs2, hrd_old⟩ := holdsFor_sepConj_regIs_regIs_regIs hne12 hne13 hne23 h_pre
  -- Compute the instruction execution
  let result := v1 + v2
  have hfetch : loadProgram base [Instr.ADD rd rs1 rs2] base = some (Instr.ADD rd rs1 rs2) := by
    simp [loadProgram, BitVec.sub_self]
  have hnext : execInstrBr st (Instr.ADD rd rs1 rs2) = (st.setReg rd result).setPC (st.pc + 4) := by
    simp [execInstrBr, result, hrs1, hrs2]
  have hstep : step (loadProgram base [Instr.ADD rd rs1 rs2]) st = some ((st.setReg rd result).setPC (base + 4)) := by
    unfold step; rw [hpc, hfetch]; simp [hnext, hpc]
  refine ⟨1, (st.setReg rd result).setPC (base + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Postcondition: TODO - needs frame recombination infrastructure
    sorry

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
    have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    -- Apply frame preservation for rd
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    -- Rewrite back using associativity: (rd ↦ᵣ result) ** ((rs2 ↦ᵣ v2) ** R) = ((rd ↦ᵣ result) ** (rs2 ↦ᵣ v2)) ** R
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
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
    have hPR' := RiscVMacroAsm.holdsFor_sepConj_pull_second.1 hPR
    -- Apply frame preservation for rd
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs1 ↦ᵣ v1) ** R) hrd_ne_x0 hPR'
    -- Rearrange back: (rd ↦ᵣ result) ** ((rs1 ↦ᵣ v1) ** R) = ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ result)) ** R
    have h2 := RiscVMacroAsm.holdsFor_sepConj_pull_second.2 h1
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
  sorry

/-- SUB rd, rd, rs2: rd := rd - rs2 -/
theorem sub_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rd rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    let post := (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)
    cpsTriple code entry exit_ pre post := by
  sorry

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
  sorry

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
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LW rd rs1 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (addr ↦ₘ mem_val)
    let post := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- LW rd, offset(rd): rd := mem[rd + sext(offset)] (same register) -/
theorem lw_spec_same (rd : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LW rd rd offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rd ↦ᵣ v_addr) ** (addr ↦ₘ mem_val)
    let post := (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SW rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 (registers distinct) -/
theorem sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Addr) :
    let code := loadProgram base [Instr.SW rs1 rs2 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ mem_old)
    let post := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SW rs, offset(rs): mem[rs + sext(offset)] := rs (same register) -/
theorem sw_spec_same (rs : Reg) (v : Word) (mem_old : Word) (offset : BitVec 12) (base : Addr) :
    let code := loadProgram base [Instr.SW rs rs offset]
    let entry := base
    let exit_ := base + 4
    let addr := v + signExtend12 offset
    let pre := (rs ↦ᵣ v) ** (addr ↦ₘ mem_old)
    let post := (rs ↦ᵣ v) ** (addr ↦ₘ v)
    cpsTriple code entry exit_ pre post := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 (distinct) -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rs1 offset]
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- JALR rd, rd, offset: rd := PC + 4; PC := (rd + sext(offset)) & ~1 (same) -/
theorem jalr_spec_same (rd : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rd offset]
    let entry := base
    let exit_ := (v + signExtend12 offset) &&& (~~~1)
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple code entry exit_ pre post := by
  sorry

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
  sorry

/-- LI rd, imm: rd := imm (pseudo for loading immediate) -/
theorem li_spec (rd : Reg) (v_old imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LI rd imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ imm)
    cpsTriple code entry exit_ pre post := by
  sorry

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

end RiscVMacroAsm
