/-
  EvmAsm.Stateless.VM.Stack

  Per-frame EVM value stack (1024 × 256-bit slots). The opcode
  handlers in `EvmAsm/Evm64/{Pop, Push, Dup, Swap}/Program.lean`
  already implement the per-opcode stack semantics. This file is
  the per-frame book-keeping shim:

  - `stack_base` pointer in the frame (start of 32 KiB block).
  - `stack_ptr`  current top-of-stack offset.

  Stack overflow (push when ptr == 1024) and underflow (pop when
  ptr == 0) are checked at opcode dispatch via fixed bounds; on
  violation the interpreter routes to a frame-level revert (NOT
  to `unimplemented_exit` -- stack errors are an STF outcome).

  Working RAM: `EVM_VALUE_STACK` (1 MiB total, sliced per frame).

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.VM.Stack

-- TODO(stateless-vm): expose stack initialisation +
-- overflow/underflow guards.

end EvmAsm.Stateless.VM.Stack
