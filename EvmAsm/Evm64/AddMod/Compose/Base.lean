/-
  EvmAsm.Evm64.AddMod.Compose.Base

  Shared composition infrastructure for ADDMOD: `addmodCode` (the union
  of all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `addmodCode`, and shared length lemmas.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Concrete
  definitions will be added once `evm_addmod` is laid out (slice
  evm-asm-sord) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Evm64.AddMod.LimbSpec
import EvmAsm.Evm64.AddMod.AddrNorm

namespace EvmAsm.Evm64.AddMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

-- Composition helpers (skipBlock subsumptions, length lemmas, etc.)
-- land alongside the Compose/<Phase>.lean files in later slices.

end EvmAsm.Evm64.AddMod.Compose
