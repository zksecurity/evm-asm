/-
  EvmAsm.Examples

  Demonstration of using the macro assembler to build small programs
  and verify their behavior. Each example is in its own file.
-/

import EvmAsm.Examples.Swap
import EvmAsm.Examples.Zero
import EvmAsm.Examples.Multiply
import EvmAsm.Examples.LoadModifyStore
import EvmAsm.Examples.Combining
import EvmAsm.Examples.Halting
import EvmAsm.Examples.Commit
import EvmAsm.Examples.Write
import EvmAsm.Examples.FullPipeline
import EvmAsm.Examples.HelloWorld
import EvmAsm.Examples.Echo

-- 256-bit EVM operations
import EvmAsm.Evm.Basic
import EvmAsm.Evm.Stack
import EvmAsm.Evm.Bitwise
import EvmAsm.Evm.And
import EvmAsm.Evm.Or
import EvmAsm.Evm.Xor
import EvmAsm.Evm.Not
import EvmAsm.Evm.Arithmetic
import EvmAsm.Evm.ArithmeticSpec
import EvmAsm.Evm.Comparison
import EvmAsm.Evm.ComparisonSpec
import EvmAsm.Evm.StackOps
import EvmAsm.Evm.Shift
import EvmAsm.Evm.ShiftSpec
