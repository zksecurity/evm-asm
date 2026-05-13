/-
  EvmAsm.Evm64.SDiv

  Umbrella for the SDIV opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SDiv`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `sdiv_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.SDiv.AddrNormAttr
import EvmAsm.Evm64.SDiv.Layout
import EvmAsm.Evm64.SDiv.Args
import EvmAsm.Evm64.SDiv.ArgsStackDecode
import EvmAsm.Evm64.SDiv.StackExecutionBridge
import EvmAsm.Evm64.SDiv.HandlerBridge
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm
import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Evm64.SDiv.Compose.Bridges
import EvmAsm.Evm64.SDiv.Compose.DivisorAbsSequence
import EvmAsm.Evm64.SDiv.Compose.SignXorSequence
import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.SignFrame
import EvmAsm.Evm64.SDiv.Compose.Words
import EvmAsm.Evm64.SDiv.Compose.DispatchViews
import EvmAsm.Evm64.SDiv.Compose.BzeroPost
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatch
import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix
import EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFree
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchZeroDivisor
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SDiv.Spec
