/-
  RiscVMacroAsm.Examples.Commit

  COMMIT syscall (SP1 convention) examples.
-/

import RiscVMacroAsm.Execution

namespace RiscVMacroAsm.Examples

-- ============================================================================
-- COMMIT syscall (SP1 convention)
-- ============================================================================

/-- A program that commits a value then halts. -/
def commit_and_halt : Program :=
  LI .x10 42 ;;
  LI .x11 0 ;;
  LI .x5 0x10 ;;     -- t0 := COMMIT
  single .ECALL ;;   -- commit (continues)
  LI .x5 0 ;;        -- t0 := HALT
  single .ECALL       -- halt

def commit_and_halt_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After the commit step (4 instructions to set up + ECALL), execution continues. -/
example : let code := loadProgram 0 commit_and_halt
          let steps := 4  -- LI x10, LI x11, LI x5, ECALL (commit)
          (stepN steps code commit_and_halt_state).isSome = true := by
  native_decide

/-- After all steps up to halt, the next step returns none (halted). -/
example : let code := loadProgram 0 commit_and_halt
          let steps := commit_and_halt.length - 1  -- run up to halt ECALL
          (stepN steps code commit_and_halt_state).bind (fun s =>
            step code s) = none := by
  native_decide

/-- At the halt point, a0 (x10) still contains 42. -/
example : let code := loadProgram 0 commit_and_halt
          let steps := commit_and_halt.length - 1
          (stepN steps code commit_and_halt_state).bind (fun s =>
            some (s.getReg .x10)) = some 42 := by
  native_decide

/-- After running commit_and_halt, the committed output is [(42, 0)]. -/
example : let code := loadProgram 0 commit_and_halt
          let steps := 4  -- run through the COMMIT ECALL
          (stepN steps code commit_and_halt_state).bind (fun s =>
            some s.committed) = some [(42, 0)] := by
  native_decide

-- ============================================================================
-- Two commits in sequence
-- ============================================================================

/-- A program that commits two values then halts. -/
def commit_twice_and_halt : Program :=
  COMMIT 42 0 ;; COMMIT 99 1 ;; HALT 0

def commit_twice_state : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- After running commit_twice_and_halt, the committed output is [(42, 0), (99, 1)]. -/
example : let code := loadProgram 0 commit_twice_and_halt
          let steps := 8  -- two COMMITs (4 steps each)
          (stepN steps code commit_twice_state).bind (fun s =>
            some s.committed) = some [(42, 0), (99, 1)] := by
  native_decide

/-- After all steps including halt, committed output is preserved. -/
example : let code := loadProgram 0 commit_twice_and_halt
          let steps := commit_twice_and_halt.length - 1
          (stepN steps code commit_twice_state).bind (fun s =>
            some s.committed) = some [(42, 0), (99, 1)] := by
  native_decide

end RiscVMacroAsm.Examples
