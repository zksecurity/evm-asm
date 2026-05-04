/-
  EvmAsm.Evm64.MulMod.Compose.Base

  Shared composition infrastructure for MULMOD: `mulmodCode` (the union
  of all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `mulmodCode`, and shared length lemmas.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). Concrete
  definitions will be added once `evm_mulmod` is laid out (slice
  evm-asm-m4wu) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Evm64.MulMod.LimbSpec
import EvmAsm.Evm64.MulMod.AddrNorm

namespace EvmAsm.Evm64.MulMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

-- Composition helpers (skipBlock subsumptions, length lemmas, etc.)
-- land alongside the Compose/<Phase>.lean files in later slices.

end EvmAsm.Evm64.MulMod.Compose
