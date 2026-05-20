/-
  EvmAsm.Stateless

  Umbrella for the `run_stateless_guest` port of
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py`.

  PR1 (this commit): minimal compiling scaffold (memory layout +
  Unimplemented exit + top-level Entry stub + placeholder spec).
  Follow-up PRs flesh out the sub-trees listed in the plan file
  (`SSZ/`, `Headers/`, `Witness/`, `State/`, `ExecutionEngine/`,
  `Block/`, `Transaction/`, `VM/`, `Bridges/`).
-/

import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Stateless.Unimplemented
import EvmAsm.Stateless.Entry
import EvmAsm.Stateless.EntrySpec
