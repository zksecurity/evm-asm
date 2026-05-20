/-
  EvmAsm.Stateless.VM

  Umbrella for the EVM interpreter subtree of the stateless guest.
  Mirrors `forks/amsterdam/vm/` (interpreter.py + instructions/ +
  memory.py + stack.py + precompiled_contracts/ + gas.py).

  ## Subtree

  - `Interpreter.lean`  — top-level `execute_message` dispatch loop.
                          Reuses the M5b dispatch table at
                          `EvmAsm/Codegen/Programs.lean` (256-entry
                          jump table) as the concrete dispatcher.
  - `Message.lean`      — message frame record (caller / callee /
                          value / data / depth, gas).
  - `Memory.lean`       — EVM memory model (MLOAD/MSTORE/MSTORE8
                          dispatch already covered by `Evm64/MLoad`,
                          `Evm64/MStore`, `Evm64/MStore8`; this
                          file is the per-frame book-keeping shim).
  - `Stack.lean`        — EVM value stack (POP/PUSH/DUP/SWAP
                          opcodes already in `Evm64/{Pop, Push,
                          Dup, Swap}`; this file binds them into
                          a frame).
  - `Precompiles.lean`  — dispatch for precompile addresses
                          0x01..0x14. **Every call routes to
                          `unimplemented_exit` with reason code
                          `REASON_PRECOMPILE + precompile_id`**
                          per the project scope (precompiles are
                          out of scope for the first STF wire-up;
                          tests that trigger a precompile call
                          deliberately exit with that reason).
  - `Spec.lean`         — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K12.
-/

import EvmAsm.Stateless.VM.Interpreter
import EvmAsm.Stateless.VM.Message
import EvmAsm.Stateless.VM.Memory
import EvmAsm.Stateless.VM.Stack
import EvmAsm.Stateless.VM.Precompiles
import EvmAsm.Stateless.VM.Spec
