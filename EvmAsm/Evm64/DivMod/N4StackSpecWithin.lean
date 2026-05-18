/-
  EvmAsm.Evm64.DivMod.N4StackSpecWithin

  This module is intentionally inert while the n=4 call-addback path is being
  repaired. The old dispatcher-surface wrappers depended on the n=4 stack
  wrappers in `N4StackSpec.lean`, which in turn depended transitively on the
  false `n4CallAddbackBeqSemanticHolds` premise.
-/

namespace EvmAsm.Evm64

end EvmAsm.Evm64
