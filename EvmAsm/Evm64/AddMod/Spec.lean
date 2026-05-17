/-
  EvmAsm.Evm64.AddMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_addmod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  The general `evm_addmod_stack_spec_within` theorem lands in slice
  evm-asm-sord and is composed from the verified shared bridge with
  the boundary blocks. The addmod-correctness lemma
  `EvmWord.addmod_correct` is added in an earlier slice (see
  parent task evm-asm-z7qm).

  Architecture notes for N=0 case (bead evm-asm-a32mz):
  - When N=0, the mod callable follows the zeroPath: stores zeros at
    x12+32..x12+56 WITHOUT advancing x12.
  - cc_ret preserves x1=(base+128) through the zeroPath.
  - After cc_ret, the epilogue at base+128 advances x12 by 32.
  - Net: x12 goes sp → sp+32 (prologue) → sp+32 (zeroPath) → sp+64 (epilogue).
  - Result (zero) sits at sp+64 = final x12. Correct for ADDMOD pop-3-push-1.
  - Infrastructure available: evm_mod_callable_bzero_preserving_x1_spec
    (from DivMod/Callable.lean, PR #4616) enables the proof.
  - Next step: write the dispatch-bridge connecting evmAddModPhase1Phase2LimbPost
    to divModStackDispatchPre for the N=0 case.
-/

import EvmAsm.Evm64.AddMod.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.AddMod.Compose

-- Placeholder: `evm_addmod_stack_spec_within` lands in slice evm-asm-sord.
-- The N=0 partial case is tracked in bead evm-asm-a32mz.

end EvmAsm.Evm64
