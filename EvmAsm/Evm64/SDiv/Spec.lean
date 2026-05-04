/-
  EvmAsm.Evm64.SDiv.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_sdiv`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). The
  actual `evm_sdiv_stack_spec_within` theorem lands in slice
  evm-asm-01uh and is composed from the verified shared bridge with
  the boundary blocks.
-/

import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SDiv.Compose

-- Placeholder: `evm_sdiv_stack_spec_within` lands in slice 4
-- (evm-asm-01uh). The signed-division correctness lemma
-- `EvmWord.sdiv_correct` is added in slice 3 (evm-asm-kvs4).

end EvmAsm.Evm64
