/-
  EvmAsm.Evm64.AddMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_addmod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0). The
  actual `evm_addmod_stack_spec_within` theorem lands in slice
  evm-asm-sord and is composed from the verified shared bridge with
  the boundary blocks. The addmod-correctness lemma
  `EvmWord.addmod_correct` is added in an earlier slice (see
  parent task evm-asm-z7qm).
-/

import EvmAsm.Evm64.AddMod.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.AddMod.Compose

-- Placeholder: `evm_addmod_stack_spec_within` lands in slice evm-asm-sord.

end EvmAsm.Evm64
