/-
  EvmAsm.Evm64.AddMod.Program

  ADDMOD opcode (`ADDMOD(a, b, N)` = (a + b) mod N under EVM
  rules, with `N = 0` returning `0`) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0).

  The actual `evm_addmod : Program` will be defined in slice
  evm-asm-sord. Per `docs/91-addmod-mulmod-survey.md` the algorithm reuses
  the existing `evm_div_callable` / `evm_mod_callable` shims after a
  pre-divide widening pass.

  This file currently has no `evm_addmod` definition; later slices will
  add it without breaking the umbrella import graph.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: `evm_addmod : Program` lands in slice 3 (evm-asm-sord).
-- See `docs/91-addmod-mulmod-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
