/-
  EvmAsm.Evm64.Exp

  Umbrella for the EXP opcode subtree (GH #92). Re-exports the top-level
  spec; downstream consumers should `import EvmAsm.Evm64.Exp` and not
  reach into sub-modules directly.

  AddrNormAttr is imported first (per AGENTS.md `register_simp_attr`
  ordering rule) so the `exp_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.Exp.AddrNormAttr
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Exp.Gas
import EvmAsm.Evm64.Exp.Args
import EvmAsm.Evm64.Exp.ArgsStackDecode
import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.MarshalPair
import EvmAsm.Evm64.Exp.SquaringCall
import EvmAsm.Evm64.Exp.SquaringCallSeq
import EvmAsm.Evm64.Exp.SquaringMarshalPairPost
import EvmAsm.Evm64.Exp.SquaringPairThenMulCall
import EvmAsm.Evm64.Exp.CondMulMarshalPair
import EvmAsm.Evm64.Exp.CondMulCall
import EvmAsm.Evm64.Exp.CondMulCallSeq
import EvmAsm.Evm64.Exp.CondMulPairThenMulCall
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Evm64.Exp.Compose.Base
import EvmAsm.Evm64.Exp.Compose.EvmExpCode
import EvmAsm.Evm64.Exp.Compose.TopCodeSubs
import EvmAsm.Evm64.Exp.Compose.LoopCodeSpecs
import EvmAsm.Evm64.Exp.Compose.TopBoundaryBlocks
import EvmAsm.Evm64.Exp.Compose.TopIterSubs
import EvmAsm.Evm64.Exp.Compose.TopCodeSpecs
import EvmAsm.Evm64.Exp.Compose.WithMulCode
import EvmAsm.Evm64.Exp.Compose.LoopControlBlocks
import EvmAsm.Evm64.Exp.Compose.SquaringMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulMarshalBlocks
import EvmAsm.Evm64.Exp.Compose.CondMulSkipBlock
import EvmAsm.Evm64.Exp.Compose.SquaringCallPath
import EvmAsm.Evm64.Exp.Compose.CondMulCallPath
import EvmAsm.Evm64.Exp.Compose.SquaringCallBlock
import EvmAsm.Evm64.Exp.Compose.CondMulCallBlock
import EvmAsm.Evm64.Exp.Compose.FullLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitWithMul
import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopCanonical
import EvmAsm.Evm64.Exp.Compose.SavedBitCondMulCall
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkip
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulSkipCanonical
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCondCanonical
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostPcFree
import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge
import EvmAsm.Evm64.Exp.Layout
import EvmAsm.Evm64.Exp.Spec
import EvmAsm.Evm64.Exp.StackExecutionBridge
