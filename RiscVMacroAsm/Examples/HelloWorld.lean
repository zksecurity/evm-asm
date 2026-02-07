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

end RiscVMacroAsm.Examples
