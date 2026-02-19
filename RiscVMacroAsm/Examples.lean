/-
  RiscVMacroAsm.Examples

  Demonstration of using the macro assembler to build small programs
  and verify their behavior. Each example is in its own file.
-/

import RiscVMacroAsm.Examples.Swap
import RiscVMacroAsm.Examples.Zero
import RiscVMacroAsm.Examples.Multiply
import RiscVMacroAsm.Examples.LoadModifyStore
import RiscVMacroAsm.Examples.Combining
import RiscVMacroAsm.Examples.Halting
import RiscVMacroAsm.Examples.Commit
import RiscVMacroAsm.Examples.Write
import RiscVMacroAsm.Examples.FullPipeline
import RiscVMacroAsm.Examples.HelloWorld
import RiscVMacroAsm.Examples.Echo

-- 256-bit EVM operations
import RiscVMacroAsm.Evm.Basic
import RiscVMacroAsm.Evm.Stack
import RiscVMacroAsm.Evm.Bitwise
import RiscVMacroAsm.Evm.And
import RiscVMacroAsm.Evm.Or
import RiscVMacroAsm.Evm.Xor
import RiscVMacroAsm.Evm.Not
import RiscVMacroAsm.Evm.Arithmetic
import RiscVMacroAsm.Evm.ArithmeticSpec
import RiscVMacroAsm.Evm.Comparison
import RiscVMacroAsm.Evm.ComparisonSpec
