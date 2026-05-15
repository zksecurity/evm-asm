/-
  EvmAsm.Evm64.Exp.Compose.FullLoop

  Small full-loop prep helpers for EXP.  The static EXP body contains JALs to
  the out-of-line `mul_callable`, so full-loop composition needs a code bundle
  that contains both the top-level EXP program and the callable multiply body.
-/

import EvmAsm.Evm64.Exp.Compose.WithMulCode
import EvmAsm.Evm64.Exp.Compose.LoopControlBlocks
import EvmAsm.Evm64.Exp.Compose.SquaringMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulSkipBlock
import EvmAsm.Evm64.Exp.Compose.SquaringCallPath
import EvmAsm.Evm64.Exp.Compose.CondMulCallPath
import EvmAsm.Evm64.Exp.Compose.SquaringCallBlock
import EvmAsm.Evm64.Exp.Compose.CondMulCallBlock
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64 (Assertion CodeReq cpsBranchWithin
  cpsBranchWithin_extend_code cpsTripleWithin cpsTripleWithin_extend_code
  memOwn regOwn signExtend12 signExtend13 signExtend21)

end EvmAsm.Evm64.Exp.Compose
