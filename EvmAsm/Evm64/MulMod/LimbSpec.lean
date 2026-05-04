/-
  EvmAsm.Evm64.MulMod.LimbSpec

  Per-block / per-limb cpsTriple specs for MULMOD sub-blocks (operand
  widening, callable-divide JAL, result narrowing).

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Per-block specs land in slice evm-asm-m4wu and below.

end EvmAsm.Evm64
