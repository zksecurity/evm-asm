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

theorem expTopIterSquaringAddr (base : Word) :
    (base + 40 : Word) = base + 28 + 12 := by
  bv_omega


theorem expTopIterCondMulAddr (base : Word) :
    (base + 144 : Word) = base + 28 + 116 := by
  bv_omega


theorem expTopIterSavedBitSquaringAddr (base : Word) :
    (base + 44 : Word) = base + 28 + 16 := by
  bv_omega


theorem expTopIterSavedBitCondMulAddr (base : Word) :
    (base + 148 : Word) = base + 28 + 120 := by
  bv_omega


theorem expTopIterSavedBitLoopBackAddr (base : Word) :
    (base + 256 : Word) = base + 28 + 228 := by
  bv_omega


theorem expTopIterLoopBackAddr (base : Word) :
    (base + 252 : Word) = base + 28 + 224 := by
  bv_omega


theorem expTopSquaringFactor2Addr (base : Word) :
    (base + 72 : Word) = base + 40 + 32 := by
  bv_omega


theorem expTopSquaringSquareAddr (base : Word) :
    (base + 104 : Word) = base + 40 + 64 := by
  bv_omega


theorem expTopSquaringRestoreAddr (base : Word) :
    (base + 108 : Word) = base + 40 + 68 := by
  bv_omega


theorem expTopCondMulCallStartAddr (base : Word) :
    (base + 148 : Word) = base + 144 + 4 := by
  bv_omega


theorem expTopCondMulFactor2Addr (base : Word) :
    (base + 180 : Word) = base + 148 + 32 := by
  bv_omega


theorem expTopCondMulFactor2Addr_symm (base : Word) :
    ((base + 148 : Word) + 32) = base + 180 := by
  bv_omega


theorem expTopCondMulSquareAddr (base : Word) :
    (base + 212 : Word) = base + 148 + 64 := by
  bv_omega


theorem expTopCondMulRestoreAddr (base : Word) :
    (base + 216 : Word) = base + 148 + 68 := by
  bv_omega


theorem expTopPointerAdvanceNextPc (base : Word) :
    ((base + 24 : Word) + 4) = base + 28 := by
  bv_omega


theorem expTopPointerRestoreNextPc (base : Word) :
    ((base + 260 : Word) + 4) = base + 264 := by
  bv_omega


theorem expTopEpilogueNextPc (base : Word) :
    ((base + 264 : Word) + 36) = base + 300 := by
  bv_omega


theorem expTopSavedBitEpilogueEntryNextPc (base : Word) :
    ((base + 264 : Word) + 4) = base + 268 := by
  bv_omega


theorem expTopSavedBitEpilogueNextPc (base : Word) :
    ((base + 268 : Word) + 36) = base + 304 := by
  bv_omega


theorem expTopIterBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  bv_omega


theorem expTopSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  bv_omega


theorem expTopLoopBackNextPc (base : Word) :
    ((base + 252 : Word) + 8) = base + 260 := by
  bv_omega


theorem expTopCondMulBeqNextPc (base : Word) :
    ((base + 144 : Word) + 4) = base + 148 := by
  bv_omega


theorem expTopSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  bv_omega


theorem expTopCondMulMarshalPairNextPc (base : Word) :
    ((base + 148 : Word) + 64) = base + 212 := by
  bv_omega

end EvmAsm.Evm64.Exp.Compose
