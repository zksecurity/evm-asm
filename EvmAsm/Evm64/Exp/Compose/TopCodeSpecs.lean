/-
  EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

  Small top-level EXP code-bundle specs split out of `Compose/Base.lean` to
  keep the base composition module under the Compose file-size guardrail.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBase
import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks
import EvmAsm.Evm64.Exp.Compose.TopIterSubs
import EvmAsm.Evm64.Exp.Compose.TopLoopControl
import EvmAsm.Evm64.Exp.Compose.TopCallSubs
import EvmAsm.Evm64.Exp.Compose.TopJalBlocks
import EvmAsm.Evm64.Exp.Compose.TopSquaringMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.TopCondMulMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.TopPairBlocks
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.SquaringCallSeq

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

end EvmAsm.Evm64.Exp.Compose
