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
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple entry exit_ pre post := by
  sorry

/-- ADD rd, rd, rs2: rd := rd + rs2 (rd = rs1, rs2 distinct) -/
theorem add_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    let post := (rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)
    cpsTriple entry exit_ pre post := by
  sorry

/-- ADD rd, rs1, rd: rd := rs1 + rd (rd = rs2, rs1 distinct) -/
theorem add_spec_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hne : rs1 ≠ rd) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple entry exit_ pre post := by
  sorry

/-- ADD rd, rd, rd: rd := rd + rd = 2 * rd (all same) -/
theorem add_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (v + v))
    cpsTriple entry exit_ pre post := by
  sorry

/-- SUB rd, rs1, rs2: rd := rs1 - rs2 (all registers distinct) -/
theorem sub_spec (rd rs1 rs2 : Reg) (v1 v2 v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))
    cpsTriple entry exit_ pre post := by
  sorry

/-- SUB rd, rd, rs2: rd := rd - rs2 -/
theorem sub_spec_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    let post := (rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)
    cpsTriple entry exit_ pre post := by
  sorry

/-- SUB rd, rd, rd: rd := rd - rd = 0 -/
theorem sub_spec_all_same (rd : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ 0)
    cpsTriple entry exit_ pre post := by
  sorry

-- ============================================================================
-- ALU Instructions (Immediate)
-- ============================================================================

/-- ADDI rd, rs1, imm: rd := rs1 + sext(imm) (registers distinct) -/
theorem addi_spec (rd rs1 : Reg) (v1 v_old : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))
    cpsTriple entry exit_ pre post := by
  sorry

/-- ADDI rd, rd, imm: rd := rd + sext(imm) (same register) -/
theorem addi_spec_same (rd : Reg) (v : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (v + signExtend12 imm))
    cpsTriple entry exit_ pre post := by
  sorry

-- ============================================================================
-- Upper Immediate Instructions
-- ============================================================================

/-- LUI rd, imm: rd := imm << 12 -/
theorem lui_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let result := (imm.zeroExtend 32 : Word) <<< 12
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple entry exit_ pre post := by
  sorry

/-- AUIPC rd, imm: rd := PC + (imm << 12) -/
theorem auipc_spec (rd : Reg) (v_old : Word) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let result := base + ((imm.zeroExtend 32 : Word) <<< 12)
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ result)
    cpsTriple entry exit_ pre post := by
  sorry

-- ============================================================================
-- Memory Instructions
-- ============================================================================

/-- LW rd, offset(rs1): rd := mem[rs1 + sext(offset)] (registers distinct) -/
theorem lw_spec (rd rs1 : Reg) (v_addr v_old mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** (addr ↦ₘ mem_val)
    let post := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple entry exit_ pre post := by
  sorry

/-- LW rd, offset(rd): rd := mem[rd + sext(offset)] (same register) -/
theorem lw_spec_same (rd : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rd ↦ᵣ v_addr) ** (addr ↦ₘ mem_val)
    let post := (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple entry exit_ pre post := by
  sorry

/-- SW rs2, offset(rs1): mem[rs1 + sext(offset)] := rs2 (registers distinct) -/
theorem sw_spec (rs1 rs2 : Reg) (v_addr v_data mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ mem_old)
    let post := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    cpsTriple entry exit_ pre post := by
  sorry

/-- SW rs, offset(rs): mem[rs + sext(offset)] := rs (same register) -/
theorem sw_spec_same (rs : Reg) (v : Word) (mem_old : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v + signExtend12 offset
    let pre := (rs ↦ᵣ v) ** (addr ↦ₘ mem_old)
    let post := (rs ↦ᵣ v) ** (addr ↦ₘ v)
    cpsTriple entry exit_ pre post := by
  sorry

-- ============================================================================
-- Branch Instructions (use cpsBranch for two exits)
-- ============================================================================

/-- BEQ rs1, rs2, offset: branch if rs1 = rs2 (registers distinct) -/
theorem beq_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    cpsBranch entry pre
      taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) := by
  sorry

/-- BEQ rs, rs, offset: branch if rs = rs (always taken, same register) -/
theorem beq_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs ↦ᵣ v)
    cpsBranch entry pre
      taken_exit (rs ↦ᵣ v)
      not_taken_exit (rs ↦ᵣ v) := by
  sorry

/-- BNE rs1, rs2, offset: branch if rs1 ≠ rs2 (registers distinct) -/
theorem bne_spec (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word) (base : Addr) :
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2)
    cpsBranch entry pre
      taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      not_taken_exit ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  sorry

/-- BNE rs, rs, offset: branch if rs ≠ rs (never taken, same register) -/
theorem bne_spec_same (rs : Reg) (offset : BitVec 13) (v : Word) (base : Addr) :
    let entry := base
    let taken_exit := base + signExtend13 offset
    let not_taken_exit := base + 4
    let pre := (rs ↦ᵣ v)
    cpsBranch entry pre
      taken_exit (rs ↦ᵣ v)
      not_taken_exit (rs ↦ᵣ v) := by
  sorry

-- ============================================================================
-- Jump Instructions
-- ============================================================================

/-- JAL rd, offset: rd := PC + 4; PC := PC + sext(offset) -/
theorem jal_spec (rd : Reg) (v_old : Word) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + signExtend21 offset
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple entry exit_ pre post := by
  sorry

/-- JALR rd, rs1, offset: rd := PC + 4; PC := (rs1 + sext(offset)) & ~1 (distinct) -/
theorem jalr_spec (rd rs1 : Reg) (v1 v_old : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old)
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))
    cpsTriple entry exit_ pre post := by
  sorry

/-- JALR rd, rd, offset: rd := PC + 4; PC := (rd + sext(offset)) & ~1 (same) -/
theorem jalr_spec_same (rd : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := (v + signExtend12 offset) &&& (~~~1)
    let pre := (rd ↦ᵣ v)
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple entry exit_ pre post := by
  sorry

-- ============================================================================
-- Pseudo Instructions
-- ============================================================================

/-- MV rd, rs: rd := rs (pseudo for ADDI rd, rs, 0) -/
theorem mv_spec (rd rs : Reg) (v v_old : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs ↦ᵣ v) ** (rd ↦ᵣ v_old)
    let post := (rs ↦ᵣ v) ** (rd ↦ᵣ v)
    cpsTriple entry exit_ pre post := by
  sorry

/-- LI rd, imm: rd := imm (pseudo for loading immediate) -/
theorem li_spec (rd : Reg) (v_old imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rd ↦ᵣ v_old)
    let post := (rd ↦ᵣ imm)
    cpsTriple entry exit_ pre post := by
  sorry

/-- NOP: no operation (pseudo for ADDI x0, x0, 0) -/
theorem nop_spec (base : Addr) :
    let entry := base
    let exit_ := base + 4
    cpsTriple entry exit_
      empAssertion
      empAssertion := by
  sorry

-- ============================================================================
-- System Instructions
-- ============================================================================

/-- FENCE: memory fence (NOP in single-hart zkVM) -/
theorem fence_spec (base : Addr) :
    let entry := base
    let exit_ := base + 4
    cpsTriple entry exit_
      empAssertion
      empAssertion := by
  sorry

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
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 + v2))
    cpsTriple entry exit_ pre post := by
  sorry

theorem sub_spec_own (rd rs1 rs2 : Reg) (v1 v2 : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 - v2))
    cpsTriple entry exit_ pre post := by
  sorry

theorem addi_spec_own (rd rs1 : Reg) (v1 : Word) (imm : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs1 ↦ᵣ v1) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))
    cpsTriple entry exit_ pre post := by
  sorry

theorem jalr_spec_own (rd rs1 : Reg) (v1 : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := (v1 + signExtend12 offset) &&& (~~~1)
    let pre := (rs1 ↦ᵣ v1) ** regOwn rd
    let post := (rs1 ↦ᵣ v1) ** (rd ↦ᵣ (base + 4))
    cpsTriple entry exit_ pre post := by
  sorry

theorem mv_spec_own (rd rs : Reg) (v : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := (rs ↦ᵣ v) ** regOwn rd
    let post := (rs ↦ᵣ v) ** (rd ↦ᵣ v)
    cpsTriple entry exit_ pre post := by
  sorry

-- Tail-position memOwn (P ** memOwn addr)

theorem sw_spec_own (rs1 rs2 : Reg) (v_addr v_data : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn addr
    let post := (rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** (addr ↦ₘ v_data)
    cpsTriple entry exit_ pre post := by
  sorry

theorem sw_spec_same_own (rs : Reg) (v : Word) (offset : BitVec 12) (base : Addr)
    (hvalid : isValidMemAccess (v + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v + signExtend12 offset
    let pre := (rs ↦ᵣ v) ** memOwn addr
    let post := (rs ↦ᵣ v) ** (addr ↦ₘ v)
    cpsTriple entry exit_ pre post := by
  sorry

-- Standalone regOwn (regOwn rd is the entire precondition)

theorem lui_spec_own (rd : Reg) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let result := BitVec.zeroExtend 32 imm <<< 12
    let pre := regOwn rd
    let post := (rd ↦ᵣ result)
    cpsTriple entry exit_ pre post := by
  sorry

theorem auipc_spec_own (rd : Reg) (imm : BitVec 20) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let result := base + BitVec.zeroExtend 32 imm <<< 12
    let pre := regOwn rd
    let post := (rd ↦ᵣ result)
    cpsTriple entry exit_ pre post := by
  sorry

theorem jal_spec_own (rd : Reg) (offset : BitVec 21) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + signExtend21 offset
    let pre := regOwn rd
    let post := (rd ↦ᵣ (base + 4))
    cpsTriple entry exit_ pre post := by
  sorry

theorem li_spec_own (rd : Reg) (imm : Word) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    let entry := base
    let exit_ := base + 4
    let pre := regOwn rd
    let post := (rd ↦ᵣ imm)
    cpsTriple entry exit_ pre post := by
  sorry

-- Middle-position regOwn (regOwn rd is between other assertions)

theorem lw_spec_own (rd rs1 : Reg) (v_addr mem_val : Word) (offset : BitVec 12) (base : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    let entry := base
    let exit_ := base + 4
    let addr := v_addr + signExtend12 offset
    let pre := (rs1 ↦ᵣ v_addr) ** regOwn rd ** (addr ↦ₘ mem_val)
    let post := (rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** (addr ↦ₘ mem_val)
    cpsTriple entry exit_ pre post := by
  sorry

end EvmAsm
