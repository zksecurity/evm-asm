/-
  EvmAsm.Evm64.DivMod.N4StackSpec

  This module is intentionally inert while the n=4 call-addback path is being
  repaired. The old dispatcher wrappers depended transitively on
  `n4CallAddbackBeqSemanticHolds`, which is false for the current algorithm.

  The predicate itself remains in `Spec/CallAddback.lean` as the Phase 2a target
  marker; the stack-surface wrappers will be rebuilt after the addback loop is
  corrected.
-/

namespace EvmAsm.Evm64

end EvmAsm.Evm64
