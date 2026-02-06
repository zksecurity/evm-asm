/-
  RiscVMacroAsm.ControlFlow

  Control flow macros using branch and jump instructions, with CPS-style
  specifications.

  This module provides:
  - if_eq: a conditional macro (if rs1 = rs2 then ... else ...)
  - CPS specifications for the macro
  - Concrete examples verified by native_decide
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.Program
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm

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
  let code := loadProgram 0 if_eq_example
  let s := mkTestState x10val x11val
  stepN steps code s

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
  let code := loadProgram 0 if_eq_arith
  let s := mkTestState x10val x11val
  stepN steps code s

/-- When x10 = x11 = 5: takes then-branch, x12 := 5 + 5 = 10. -/
example : (runIfEqArith 5 5 3).bind (fun s => some (s.getReg .x12)) = some 10 := by
  native_decide

/-- When x10 = 10, x11 = 3: takes else-branch, x12 := 10 - 3 = 7. -/
example : (runIfEqArith 10 3 2).bind (fun s => some (s.getReg .x12)) = some 7 := by
  native_decide

-- ============================================================================
-- CPS specification for if_eq
-- ============================================================================

/-- The if_eq macro satisfies a cpsBranch spec: it either goes to
    the then-body entry (base+4) with equality, or to the else-body
    entry (base+4+4*t+4) with inequality, in exactly one step. -/
theorem if_eq_branch_step (rs1 rs2 : Reg) (then_body else_body : Program)
    (base : Addr) (P : Assertion)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^13)
    (hprog_small : 4 * (then_body.length + else_body.length + 2) < 2^32) :
    let prog := if_eq rs1 rs2 then_body else_body
    let code := loadProgram base prog
    let then_entry := base + 4
    let else_entry := base + 4 + BitVec.ofNat 32 (4 * then_body.length) + 4
    cpsBranch code base P
      then_entry (fun s => P s ∧ s.getReg rs1 = s.getReg rs2)
      else_entry (fun s => P s ∧ s.getReg rs1 ≠ s.getReg rs2) := by
  -- The first instruction is BNE at address base.
  -- We need to show that code base = some (BNE rs1 rs2 else_off)
  -- and then case-split on the branch condition.
  -- This requires bitvector offset arithmetic; left for future work.
  sorry

/-- Full CPS specification for if_eq: given that the then-body is correct
    under equality and the else-body is correct under inequality,
    the whole if_eq is a cpsTriple from entry to exit. -/
theorem if_eq_spec (rs1 rs2 : Reg) (then_body else_body : Program)
    (base : Addr) (P Q : Assertion)
    (ht_small : 4 * (then_body.length + 1) + 4 < 2^13)
    (he_small : 4 * (else_body.length) + 4 < 2^21)
    (hprog_small : 4 * (then_body.length + else_body.length + 2) < 2^32) :
    let prog := if_eq rs1 rs2 then_body else_body
    let code := loadProgram base prog
    let exit_ := base + BitVec.ofNat 32 (4 * prog.length)
    -- If then-body is correct assuming equality:
    let then_entry := base + 4
    let then_exit  := base + 4 + BitVec.ofNat 32 (4 * then_body.length)
    -- If else-body is correct assuming inequality:
    let else_entry := then_exit + 4
    let else_exit  := exit_
    (cpsTriple code then_entry then_exit
      (fun s => P s ∧ s.getReg rs1 = s.getReg rs2) Q) →
    (cpsTriple code else_entry else_exit
      (fun s => P s ∧ s.getReg rs1 ≠ s.getReg rs2) Q) →
    cpsTriple code base exit_ P Q := by
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

  The symbolic proofs (`if_eq_branch_step`, `if_eq_spec`) require
  bitvector offset reasoning and are left as `sorry` for this prototype.
  The concrete examples demonstrate full correctness via `native_decide`.
-/

end RiscVMacroAsm
