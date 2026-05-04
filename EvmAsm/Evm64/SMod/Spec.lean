/-
  EvmAsm.Evm64.SMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_smod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). The
  actual `evm_smod_stack_spec_within` theorem lands in slice
  evm-asm-bjnb and is composed from the verified shared bridge with
  the boundary blocks. The signed-modulo correctness lemma
  `EvmWord.smod_correct` is also added in that slice.
-/

import EvmAsm.Evm64.SMod.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose

-- Placeholder: `evm_smod_stack_spec_within` lands in slice 5
-- (evm-asm-bjnb).

end EvmAsm.Evm64
