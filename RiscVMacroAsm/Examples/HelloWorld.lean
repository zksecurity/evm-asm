/-
  RiscVMacroAsm.Examples.HelloWorld

  A "hello world" program that stores ASCII characters to memory
  and outputs them via the SP1 WRITE syscall, with formal verification
  of output correctness and termination.
-/

import RiscVMacroAsm.Execution
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.CPSSpec

namespace RiscVMacroAsm.Examples

-- "hello world" as a list of ASCII word values (one char per 32-bit word)
def helloWorldChars : List Word :=
  [0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64]

-- The hello world program:
--   1. Store ASCII characters to memory at 0x100
--   2. WRITE fd=13 (public values), buf=0x100, nbytes=44
--   3. HALT with exit code 0
def helloWorld : Program :=
  LI .x7 0x100 ;;
  LI .x6 0x68 ;; SW .x7 .x6 0 ;;    -- 'h'
  LI .x6 0x65 ;; SW .x7 .x6 4 ;;    -- 'e'
  LI .x6 0x6C ;; SW .x7 .x6 8 ;;    -- 'l'
  LI .x6 0x6C ;; SW .x7 .x6 12 ;;   -- 'l'
  LI .x6 0x6F ;; SW .x7 .x6 16 ;;   -- 'o'
  LI .x6 0x20 ;; SW .x7 .x6 20 ;;   -- ' '
  LI .x6 0x77 ;; SW .x7 .x6 24 ;;   -- 'w'
  LI .x6 0x6F ;; SW .x7 .x6 28 ;;   -- 'o'
  LI .x6 0x72 ;; SW .x7 .x6 32 ;;   -- 'r'
  LI .x6 0x6C ;; SW .x7 .x6 36 ;;   -- 'l'
  LI .x6 0x64 ;; SW .x7 .x6 40 ;;   -- 'd'
  WRITE 13 0x100 44 ;;
  HALT 0

def helloInitState : MachineState where
  regs := fun _ => 0
  mem := fun _ => 0
  pc := 0

/-- The program is 31 instructions long. -/
example : helloWorld.length = 31 := by native_decide

/-- After 30 steps, publicValues contains the ASCII values of "hello world". -/
example : (stepN 30 (loadProgram 0 helloWorld) helloInitState).bind
    (fun s => some s.publicValues) = some helloWorldChars := by
  native_decide

/-- After 30 steps, the next step is HALT. -/
example : ((stepN 30 (loadProgram 0 helloWorld) helloInitState).bind
    (fun s => step (loadProgram 0 helloWorld) s)).isNone = true := by
  native_decide

/-- CPS-style specification: hello world outputs the correct characters and halts. -/
theorem helloWorld_spec :
    cpsHaltTriple (loadProgram 0 helloWorld) 0
      (fun s => s = helloInitState)
      (fun s => s.publicValues = helloWorldChars) := by
  intro s hpre hpc; subst hpre
  have h : (stepN 30 (loadProgram 0 helloWorld) helloInitState).isSome = true := by
    native_decide
  exact ⟨30, (stepN 30 (loadProgram 0 helloWorld) helloInitState).get h,
    (Option.some_get h).symm, by native_decide +revert, by native_decide +revert⟩

/-- Legacy specification: hello world outputs the correct characters and halts. -/
theorem helloWorld_correct :
    let code := loadProgram 0 helloWorld
    (∀ s, stepN 30 code helloInitState = some s →
      (publicValuesIs helloWorldChars).holdsFor s)
    ∧
    ((stepN 30 code helloInitState).bind (fun s => step code s)).isNone = true
    := by
  refine ⟨?_, by native_decide⟩
  intro s hs
  rw [holdsFor_publicValuesIs]
  have h : (stepN 30 (loadProgram 0 helloWorld) helloInitState).bind
      (fun s => some s.publicValues) = some helloWorldChars := by native_decide
  rw [hs, Option.bind_some] at h
  exact Option.some_inj.mp h

/-- The memory buffer holds 'h' at 0x100 and 'd' at 0x128 after execution. -/
theorem helloWorld_buffer_spec :
    ∀ s, stepN 30 (loadProgram 0 helloWorld) helloInitState = some s →
      ((0x100 : Addr) ↦ₘ (0x68 : Word)).holdsFor s ∧  -- 'h'
      ((0x128 : Addr) ↦ₘ (0x64 : Word)).holdsFor s     -- 'd'
    := by
  intro s hs
  simp only [holdsFor_memIs]
  constructor
  · have h : (stepN 30 (loadProgram 0 helloWorld) helloInitState).bind
        (fun s => some (s.getMem 0x100)) = some (0x68 : Word) := by native_decide
    rw [hs, Option.bind_some] at h
    exact Option.some_inj.mp h
  · have h : (stepN 30 (loadProgram 0 helloWorld) helloInitState).bind
        (fun s => some (s.getMem 0x128)) = some (0x64 : Word) := by native_decide
    rw [hs, Option.bind_some] at h
    exact Option.some_inj.mp h

end RiscVMacroAsm.Examples
