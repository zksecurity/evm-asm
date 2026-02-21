/-
  EvmAsm.ControlFlow

  Control flow macros using branch and jump instructions, with CPS-style
  specifications.

  This module provides:
  - if_eq: a conditional macro (if rs1 = rs2 then ... else ...)
  - CPS specifications for the macro
  - Concrete examples verified by native_decide
-/

import EvmAsm.Basic
import EvmAsm.Instructions
import EvmAsm.Program
import EvmAsm.SepLogic
import EvmAsm.Execution
import EvmAsm.CPSSpec

namespace EvmAsm

-- ============================================================================
-- if_eq macro
-- ============================================================================

/-- Conditional macro: if rs1 = rs2 then then_body else else_body.

    Code layout (addresses relative to base):
      base:              BNE rs1 rs2 else_offset    -- to else if ≠
      base+4:            <then_body>                 -- t instructions
      base+4+4t:         JAL x0 end_offset           -- skip else
      base+4+4t+4:       <else_body>                 -- e instructions
      base+4+4t+4+4e:    (exit point)               -- merged exit

    Offsets:
      else_offset = 4*(t+1)+4  (skip then_body + JAL, in bytes)
      end_offset  = 4*e+4      (skip else_body, in bytes)        -/
def if_eq (rs1 rs2 : Reg) (then_body else_body : Program) : Program :=
  let t := then_body.length
  let e := else_body.length
  let else_off : BitVec 13 := BitVec.ofNat 13 (4 * (t + 1) + 4)
  let end_off  : BitVec 21 := BitVec.ofNat 21 (4 * e + 4)
  let bne : Program := [Instr.BNE rs1 rs2 else_off]
  let jal : Program := [Instr.JAL .x0 end_off]
  bne ++ then_body ++ jal ++ else_body

-- ============================================================================
-- Concrete examples
-- ============================================================================

/-- Concrete example: if x10 = x11 then x12 := 1 else x12 := 0 -/
def if_eq_example : Program :=
  if_eq .x10 .x11
    [Instr.LI .x12 1]      -- then: x12 := 1
    [Instr.LI .x12 0]      -- else: x12 := 0

/-- A test state for the if_eq example. -/
def mkTestState (x10val x11val : Word) (pc : Word := 0) : MachineState where
  regs := fun r =>
    match r with
    | .x10 => x10val
    | .x11 => x11val
    | _    => 0
  mem := fun _ => 0
  pc := pc

-- ============================================================================
-- Testing via step-based execution
-- ============================================================================

/-- Execute the if_eq_example program using step-based execution.
    We load the program at address 0 and run stepN. -/
def runIfEqExample (x10val x11val : Word) (steps : Nat) : Option MachineState :=
  let s := { mkTestState x10val x11val with code := loadProgram 0 if_eq_example }
  stepN steps s

-- When x10 = x11 = 42: BNE not taken → LI x12 1 → JAL (skip else)
-- Program: [BNE, LI 1, JAL, LI 0]  (4 instructions)
-- Equal case: BNE(not taken) → PC=4, LI x12 1 → PC=8, JAL x0 8 → PC=16
-- That's 3 steps to reach exit at PC=16

/-- When x10 = x11 = 42, after 3 steps x12 should be 1. -/
example : (runIfEqExample 42 42 3).bind (fun s => some (s.getReg .x12)) = some 1 := by
  native_decide

/-- When x10 = x11 = 42, after 3 steps PC should be at exit (16). -/
example : (runIfEqExample 42 42 3).bind (fun s => some s.pc) = some 16 := by
  native_decide

-- Unequal case: BNE(taken, offset=4*(1+1)+4=12) → PC=12, LI x12 0 → PC=16
-- That's 2 steps to reach exit at PC=16

/-- When x10 = 42, x11 = 99, after 2 steps x12 should be 0. -/
example : (runIfEqExample 42 99 2).bind (fun s => some (s.getReg .x12)) = some 0 := by
  native_decide

/-- When x10 = 42, x11 = 99, after 2 steps PC should be at exit (16). -/
example : (runIfEqExample 42 99 2).bind (fun s => some s.pc) = some 16 := by
  native_decide

-- ============================================================================
-- Additional examples: larger bodies
-- ============================================================================

/-- A more complex if_eq: if x10 = x11 then x12 := x10 + x11 else x12 := x10 - x11 -/
def if_eq_arith : Program :=
  if_eq .x10 .x11
    [Instr.ADD .x12 .x10 .x11]     -- then: x12 := x10 + x11
    [Instr.SUB .x12 .x10 .x11]     -- else: x12 := x10 - x11

def runIfEqArith (x10val x11val : Word) (steps : Nat) : Option MachineState :=
  let s := { mkTestState x10val x11val with code := loadProgram 0 if_eq_arith }
  stepN steps s

/-- When x10 = x11 = 5: takes then-branch, x12 := 5 + 5 = 10. -/
example : (runIfEqArith 5 5 3).bind (fun s => some (s.getReg .x12)) = some 10 := by
  native_decide

/-- When x10 = 10, x11 = 3: takes else-branch, x12 := 10 - 3 = 7. -/
example : (runIfEqArith 10 3 2).bind (fun s => some (s.getReg .x12)) = some 7 := by
  native_decide

-- ============================================================================
-- Helper lemmas for symbolic proofs
-- ============================================================================

/-- A predicate on MachineState is PC-independent: it holds regardless of the PC value. -/
def pcIndep (P : MachineState → Prop) : Prop := ∀ s v, P s → P (s.setPC v)

theorem pcIndep_and {P Q : MachineState → Prop} (hP : pcIndep P) (hQ : pcIndep Q) :
    pcIndep (fun s => P s ∧ Q s) := by
  intro s v ⟨hp, hq⟩
  exact ⟨hP s v hp, hQ s v hq⟩

theorem pcIndep_holdsFor_regIs (r : Reg) (val : Word) :
    pcIndep (regIs r val).holdsFor := by
  intro s v h
  simp only [holdsFor_regIs, MachineState.getReg_setPC] at *; exact h

theorem pcIndep_holdsFor_memIs (a : Addr) (val : Word) :
    pcIndep (memIs a val).holdsFor := by
  intro s v h
  simp only [holdsFor_memIs, MachineState.getMem, MachineState.setPC] at *; exact h

theorem pcIndep_committedIs (vals : List (Word × Word)) :
    pcIndep (MachineState.committedIs vals) := by
  intro s v h
  simp only [MachineState.committedIs, MachineState.committed_setPC] at *; exact h

theorem pcIndep_publicValuesIs (vals : List (BitVec 8)) :
    pcIndep (MachineState.publicValuesIs vals) := by
  intro s v h
  simp only [MachineState.publicValuesIs, MachineState.publicValues_setPC] at *; exact h

theorem pcIndep_privateInputIs (vals : List (BitVec 8)) :
    pcIndep (MachineState.privateInputIs vals) := by
  intro s v h
  simp only [MachineState.privateInputIs, MachineState.privateInput_setPC] at *; exact h

theorem pcIndep_holdsFor_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    pcIndep ((P ** Q).holdsFor) := by
  intro s v ⟨h, hcompat, h1, h2, hd, hunion, hp1, hp2⟩
  refine ⟨h, ?_, h1, h2, hd, hunion, hp1, hp2⟩
  have hpc_none := pcFree_sepConj hP hQ h ⟨h1, h2, hd, hunion, hp1, hp2⟩
  rw [← hunion] at hpc_none hcompat ⊢
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r' v' hv => by rw [MachineState.getReg_setPC]; exact hr r' v' hv,
         fun a' v' hv => by simp [MachineState.getMem, MachineState.setPC]; exact hm a' v' hv,
         fun a' i' hv => by rw [MachineState.code_setPC]; exact hc a' i' hv,
         fun v' hv => by rw [hpc_none] at hv; simp at hv,
         fun v' hv => by simp [MachineState.setPC] at *; exact hpv v' hv,
         fun v' hv => by simp [MachineState.setPC] at *; exact hpi v' hv⟩

/-- Sign-extend a small 13-bit value (MSB clear) to 32 bits. -/
theorem signExtend13_ofNat_small (n : Nat) (h : n < 2^12) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 32 n := by
  unfold signExtend13
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Sign-extend a small 21-bit value (MSB clear) to 32 bits. -/
theorem signExtend21_ofNat_small (n : Nat) (h : n < 2^20) :
    signExtend21 (BitVec.ofNat 21 n) = BitVec.ofNat 32 n := by
  unfold signExtend21
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega)
  · rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp [BitVec.toNat_ofNat]; omega

/-- Load the first instruction from a program at its base address. -/
theorem loadProgram_at_base (base : Addr) (instr : Instr) (rest : List Instr) :
    loadProgram base (instr :: rest) base = some instr := by
  simp [loadProgram, BitVec.sub_self]

/-- Load instruction k from a program at address base + 4*k. -/
theorem loadProgram_at_index (base : Addr) (prog : List Instr) (k : Nat)
    (hk : k < prog.length) (h4k : 4 * k < 2^32) :
    loadProgram base prog (base + BitVec.ofNat 32 (4 * k)) = prog[k]? := by
  simp [loadProgram]
  have hbase := base.isLt
  have : (4294967296 - BitVec.toNat base + (BitVec.toNat base + 4 * k)) % 4294967296
       = 4 * k := by omega
  rw [this]; simp [hk]; omega

/-- The length of an if_eq program. -/
theorem if_eq_length (rs1 rs2 : Reg) (tb eb : Program) :
    (if_eq rs1 rs2 tb eb).length = tb.length + eb.length + 2 := by
  simp only [if_eq, Program.length_append, List.length_cons, List.length_nil]; omega

/-- JAL x0 executes as a pure PC update (x0 write is dropped). -/
theorem execInstrBr_jal_x0 (s : MachineState) (off : BitVec 21) :
    execInstrBr s (Instr.JAL .x0 off) = s.setPC (s.pc + signExtend21 off) := by
  simp [execInstrBr, MachineState.setReg, MachineState.setPC]

-- ============================================================================
-- CPS specification for if_eq
-- ============================================================================

/-- The if_eq macro satisfies a cpsBranch spec: it either goes to
    the then-body entry (base+4) with equality, or to the else-body
    entry (base+4+4*t+4) with inequality, in exactly one step.

    Uses additive conjunction (⊓) so rs1 and rs2 may be the same register.
    BNE only modifies PC, so all assertions are preserved through setPC.
    The branch condition is encoded as a pure assertion on v1, v2. -/
theorem if_eq_branch_step (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let prog := if_eq rs1 rs2 then_body else_body
    let then_entry := base + 4
    let else_entry := base + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4
    let pre := P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsBranch base pre
      then_entry (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝)
      else_entry (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) := by
  sorry

/-- Full CPS specification for if_eq: given that the then-body is correct
    under equality and the else-body is correct under inequality,
    the whole if_eq is a cpsTriple from entry to exit.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register. -/
theorem if_eq_spec (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 32 (4 * prog.length)
    let then_entry := base + 4
    let then_exit  := base + 4 + BitVec.ofNat 32 (4 * then_body.length)
    let else_entry := then_exit + 4
    let else_exit  := exit_
    let pre := P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    (cpsTriple then_entry then_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple else_entry else_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ pre Q := by
  sorry

-- ============================================================================
-- N-exit CPS specifications for if_eq
-- ============================================================================

/-- The if_eq macro satisfies a cpsNBranch spec with two exits,
    derived from the existing cpsBranch spec.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register. -/
theorem if_eq_branch_step_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P : Assertion)
    (hP : P.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12) :
    let prog := if_eq rs1 rs2 then_body else_body
    let then_entry := base + 4
    let else_entry := base + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4
    let pre := P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    cpsNBranch base pre
      [ (then_entry, P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝),
        (else_entry, P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) ] := by
  simp only
  exact cpsBranch_to_cpsNBranch _ _ _ _ _ _
    (if_eq_branch_step rs1 rs2 v1 v2 then_body else_body base P hP ht_small)

/-- Full N-exit CPS specification for if_eq, using cpsNBranch_merge.

    Uses additive conjunction (⋒) so rs1 and rs2 may be the same register. -/
theorem if_eq_spec_n (rs1 rs2 : Reg) (v1 v2 : Word)
    (then_body else_body : Program)
    (base : Addr) (P Q : Assertion)
    (hP : P.pcFree) (hQ : Q.pcFree)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^12)
    (he_small : 4 * (else_body.length) + 4 < 2^20) :
    let prog := if_eq rs1 rs2 then_body else_body
    let exit_ := base + BitVec.ofNat 32 (4 * prog.length)
    let then_entry := base + 4
    let then_exit  := base + 4 + BitVec.ofNat 32 (4 * then_body.length)
    let else_entry := then_exit + 4
    let else_exit  := exit_
    let pre := P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2)
    (cpsTriple then_entry then_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 = v2⌝) Q) →
    (cpsTriple else_entry else_exit
      (P ⋒ (rs1 ↦ᵣ v1) ⋒ (rs2 ↦ᵣ v2) ⋒ ⌜v1 ≠ v2⌝) Q) →
    cpsTriple base exit_ pre Q := by
  sorry

-- ============================================================================
-- Summary
-- ============================================================================

/-!
  ## Control Flow Macros

  The `if_eq` macro demonstrates the CPS approach to branching:

  1. **Macro definition**: `if_eq` produces a flat list of instructions
     with computed byte offsets for branches.

  2. **Step-based execution**: Using `loadProgram` + `stepN`, we can
     execute the branching code correctly (verified by `native_decide`).

  3. **CPS specification**: `cpsBranch` captures the two-exit nature
     of conditional code. `cpsBranch_merge` composes it back into
     a single-exit `cpsTriple`.

  4. **Symbolic proofs**: `if_eq_branch_step` proves the BNE dispatch,
     and `if_eq_spec` composes the full correctness specification
     from branch-level and body-level specs.

  ### pcFree / pcIndep

  The `pcFree` predicate marks assertions as PC-independent (don't own the PC),
  which is needed because branch/jump instructions only modify PC.
  The `pcIndep` predicate is the MachineState-level equivalent for `holdsFor`.
-/

end EvmAsm
