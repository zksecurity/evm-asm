/-
  EvmAsm.Evm64.SMod.Compose.Base

  Shared composition infrastructure for SMOD: `smodCode` (the union of
  all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `smodCode`, and shared length lemmas.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). Concrete
  definitions will be added once `evm_smod` is laid out (slice
  evm-asm-bjnb) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Evm64.SMod.LimbSpec
import EvmAsm.Evm64.SMod.AddrNorm

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

-- Composition helpers (skipBlock subsumptions, length lemmas, etc.)
-- land alongside the Compose/<Phase>.lean files in later slices.

end EvmAsm.Evm64.SMod.Compose
