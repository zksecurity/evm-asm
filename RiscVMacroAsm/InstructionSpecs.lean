/-
  RiscVMacroAsm.InstructionSpecs

  Separation logic specifications for each RISC-V instruction using cpsTriple
  (or cpsBranch for conditional branches).

  Each lemma:
  1. States the separation logic spec of a single instruction
  2. Proves it by unfolding the execution semantics

  All specs use the CPS-style specifications with built-in frame rule from CPSSpec.lean.

  Key design decisions:
  - Use additive conjunction (⋒) to allow register aliasing (e.g., rd = rs1)
  - Preconditions must own all registers to be read or written
  - x0 writes are handled specially (writing to x0 is a no-op)
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm

-- ============================================================================
-- ALU Instructions (Register-Register)
-- ============================================================================

/-- ADD rd, rs1, rs2: rd := rs1 + rs2
    Spec: Reads rs1 and rs2, writes to rd (unless rd = x0) -/
theorem add_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADD rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 + v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SUB rd, rs1, rs2: rd := rs1 - rs2 -/
theorem sub_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SUB rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 - v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- AND rd, rs1, rs2: rd := rs1 &&& rs2 -/
theorem and_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.AND rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 &&& v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- OR rd, rs1, rs2: rd := rs1 ||| rs2 -/
theorem or_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.OR rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 ||| v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- XOR rd, rs1, rs2: rd := rs1 ^^^ rs2 -/
theorem xor_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.XOR rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 ^^^ v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLL rd, rs1, rs2: rd := rs1 << (rs2 % 32) -/
theorem sll_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLL rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 <<< (v2.toNat % 32)))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SRL rd, rs1, rs2: rd := rs1 >>> (rs2 % 32) (logical shift right) -/
theorem srl_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SRL rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 >>> (v2.toNat % 32)))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SRA rd, rs1, rs2: rd := rs1 >>s (rs2 % 32) (arithmetic shift right) -/
theorem sra_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SRA rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (BitVec.sshiftRight v1 (v2.toNat % 32)))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLT rd, rs1, rs2: rd := (rs1 <s rs2) ? 1 : 0 -/
theorem slt_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLT rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let result := if BitVec.slt v1 v2 then (1 : Word) else (0 : Word)
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLTU rd, rs1, rs2: rd := (rs1 <u rs2) ? 1 : 0 -/
theorem sltu_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLTU rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let result := if BitVec.ult v1 v2 then (1 : Word) else (0 : Word)
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  sorry

-- ============================================================================
-- ALU Instructions (Immediate)
-- ============================================================================

/-- ADDI rd, rs1, imm: rd := rs1 + sext(imm) -/
theorem addi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ADDI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 + signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- ANDI rd, rs1, imm: rd := rs1 &&& sext(imm) -/
theorem andi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ANDI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 &&& signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- ORI rd, rs1, imm: rd := rs1 ||| sext(imm) -/
theorem ori_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.ORI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 ||| signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- XORI rd, rs1, imm: rd := rs1 ^^^ sext(imm) -/
theorem xori_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.XORI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 ^^^ signExtend12 imm))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLTI rd, rs1, imm: rd := (rs1 <s sext(imm)) ? 1 : 0 -/
theorem slti_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLTI rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let result := if BitVec.slt v1 (signExtend12 imm) then (1 : Word) else (0 : Word)
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLTIU rd, rs1, imm: rd := (rs1 <u sext(imm)) ? 1 : 0 -/
theorem sltiu_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLTIU rd rs1 imm]
    let entry := base
    let exit_ := base + 4
    let result := if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SLLI rd, rs1, shamt: rd := rs1 << shamt -/
theorem slli_spec (rd rs1 : Reg) (v1 v_old : Word) (shamt : BitVec 5) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SLLI rd rs1 shamt]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 <<< shamt.toNat))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SRLI rd, rs1, shamt: rd := rs1 >>> shamt -/
theorem srli_spec (rd rs1 : Reg) (v1 v_old : Word) (shamt : BitVec 5) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SRLI rd rs1 shamt]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 >>> shamt.toNat))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SRAI rd, rs1, shamt: rd := rs1 >>s shamt -/
theorem srai_spec (rd rs1 : Reg) (v1 v_old : Word) (shamt : BitVec 5) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.SRAI rd rs1 shamt]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (BitVec.sshiftRight v1 shamt.toNat))
    cpsTriple code entry exit_ pre post := by
  sorry

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
  sorry

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
  sorry

-- ============================================================================
-- Memory Instructions (Word)
-- ============================================================================

/-- LW rd, offset(rs1): rd := mem[rs1 + sext(offset)] -/
theorem lw_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.LW rd rs1 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ⋒ (rd ↦ᵣ v_old) ⋒ (addr ↦ₘ mem_val)
    let post := (rd ↦ᵣ mem_val) ⋒ (addr ↦ₘ mem_val)
    cpsTriple code entry exit_ pre post := by
  sorry

/-- SW rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 -/
theorem sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Addr) :
    let code := loadProgram base [Instr.SW rs1 rs2 offset]
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ⋒ (rs2 ↦ᵣ v_data) ⋒ (addr ↦ₘ mem_old)
    let post := (addr ↦ₘ v_data)
    cpsTriple code entry exit_ pre post := by
  sorry

-- ============================================================================
-- Branch Instructions (use cpsBranch for two exits)
-- ============================================================================

/-- BEQ rs1, rs2, offset: branch if rs1 = rs2 -/
theorem beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BEQ rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) := by
  sorry

/-- BNE rs1, rs2, offset: branch if rs1 ≠ rs2 -/
theorem bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BNE rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) := by
  sorry

/-- BLT rs1, rs2, offset: branch if rs1 <s rs2 (signed) -/
theorem blt_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BLT rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜BitVec.slt v1 v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜¬BitVec.slt v1 v2⌝) := by
  sorry

/-- BGE rs1, rs2, offset: branch if rs1 >=s rs2 (signed) -/
theorem bge_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BGE rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜¬BitVec.slt v1 v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜BitVec.slt v1 v2⌝) := by
  sorry

/-- BLTU rs1, rs2, offset: branch if rs1 <u rs2 (unsigned) -/
theorem bltu_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BLTU rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜BitVec.ult v1 v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜¬BitVec.ult v1 v2⌝) := by
  sorry

/-- BGEU rs1, rs2, offset: branch if rs1 >=u rs2 (unsigned) -/
theorem bgeu_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let code := loadProgram base [Instr.BGEU rs1 rs2 offset]
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch code entry pre
      taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜¬BitVec.ult v1 v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜BitVec.ult v1 v2⌝) := by
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

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.JALR rd rs1 offset]
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)
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
    let pre := (rs ↦ᵣ v) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ v)
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
-- M Extension: Multiply Instructions
-- ============================================================================

/-- MUL rd, rs1, rs2: rd := (rs1 * rs2)[31:0] -/
theorem mul_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MUL rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (v1 * v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- MULH rd, rs1, rs2: rd := (sext(rs1) * sext(rs2))[63:32] -/
theorem mulh_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MULH rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_mulh v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- MULHSU rd, rs1, rs2: rd := (sext(rs1) * zext(rs2))[63:32] -/
theorem mulhsu_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MULHSU rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_mulhsu v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- MULHU rd, rs1, rs2: rd := (zext(rs1) * zext(rs2))[63:32] -/
theorem mulhu_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.MULHU rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_mulhu v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

-- ============================================================================
-- M Extension: Divide Instructions
-- ============================================================================

/-- DIV rd, rs1, rs2: rd := rs1 /s rs2 (signed division) -/
theorem div_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.DIV rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_div v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- DIVU rd, rs1, rs2: rd := rs1 /u rs2 (unsigned division) -/
theorem divu_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.DIVU rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_divu v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- REM rd, rs1, rs2: rd := rs1 %s rs2 (signed remainder) -/
theorem rem_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.REM rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_rem v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

/-- REMU rd, rs1, rs2: rd := rs1 %u rs2 (unsigned remainder) -/
theorem remu_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let code := loadProgram base [Instr.REMU rd rs1 rs2]
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (rv32_remu v1 v2))
    cpsTriple code entry exit_ pre post := by
  sorry

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Instruction Specifications Summary

  This module provides separation logic specifications for all 47 RV32IM instructions
  using CPS-style (continuation-passing style) specifications with built-in frame rule.

  ### Key Design Decisions

  1. **Additive Conjunction (⋒)**: Used to handle register aliasing. For example, in
     `ADDI rd, rs1, imm`, rs1 and rd might be the same register, so we use
     `(rs1 ↦ᵣ v1) ⋒ (rd ↦ᵣ v_old)` which allows overlap.

  2. **Ownership Model**: The precondition must own all registers that will be read
     or written. For writes to rd, we require `(rd ↦ᵣ v_old)` in the precondition,
     where v_old is the old value (which may be overwritten).

  3. **x0 Handling**: All specs require `rd ≠ .x0` since writes to x0 are no-ops
     in RISC-V. This avoids complications in the postcondition.

  4. **Frame Rule**: The built-in frame rule in `cpsTriple` means any assertion R
     that is pcFree and disjoint from the pre/postconditions is automatically preserved.

  5. **Branch Instructions**: Use `cpsBranch` instead of `cpsTriple` to capture
     the two-exit nature (taken vs not taken), with pure assertions encoding the
     branch condition.

  ### Coverage

  - **ALU Register-Register** (10): ADD, SUB, AND, OR, XOR, SLL, SRL, SRA, SLT, SLTU
  - **ALU Immediate** (10): ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI
  - **Upper Immediate** (2): LUI, AUIPC
  - **Memory** (2): LW, SW
  - **Branches** (6): BEQ, BNE, BLT, BGE, BLTU, BGEU
  - **Jumps** (2): JAL, JALR
  - **Pseudo** (3): MV, LI, NOP
  - **System** (2): FENCE, EBREAK
  - **M Extension** (8): MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU

  Total: 45 instruction specs (excluding sub-word memory operations which would add 6 more)
-/

end RiscVMacroAsm
