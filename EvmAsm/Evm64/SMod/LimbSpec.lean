/-
  EvmAsm.Evm64.SMod.LimbSpec

  Per-block / per-limb cpsTriple specs for SMOD sub-blocks (sign
  extraction, abs negation, callable-modulo JAL, sign-correction).

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). Per
  `OPCODE_TEMPLATE.md`, each sub-block will get exactly one cpsTriple
  lemma once the Compose layer pins the layout.
-/

import EvmAsm.Evm64.SMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Per-block specs land in slice evm-asm-bjnb and below.

end EvmAsm.Evm64
