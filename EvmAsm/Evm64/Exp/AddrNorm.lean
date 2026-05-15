/-
  EvmAsm.Evm64.Exp.AddrNorm

  Address-normalization simp set for EXP composition proofs.

  Skeleton placeholder (GH #92, beads slice evm-asm-cf2c). The
  `@[exp_addr, grind =]`-tagged atomic facts will be added once the
  Compose layer (Exp/Compose/Loop.lean) starts emitting concrete address
  arithmetic. For now this file just imports the shared `Rv64.AddrNorm`
  base and the attribute declaration so downstream files can already
  open the namespace.
-/

import EvmAsm.Rv64.AddrNorm
import EvmAsm.Evm64.Exp.AddrNormAttr
import Std.Tactic.BVDecide

namespace EvmAsm.Evm64.Exp.AddrNorm

@[exp_addr, grind =] theorem exp_se13_108 :
    EvmAsm.Rv64.signExtend13 (108 : BitVec 13) = (108 : Word) := by decide

@[exp_addr, grind =] theorem exp_se13_neg228 :
    EvmAsm.Rv64.signExtend13 ((-228 : BitVec 13)) = (18446744073709551388 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_neg64 :
    EvmAsm.Rv64.signExtend12 ((-64 : BitVec 12)) = (18446744073709551552 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_neg56 :
    EvmAsm.Rv64.signExtend12 ((-56 : BitVec 12)) = (18446744073709551560 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_neg48 :
    EvmAsm.Rv64.signExtend12 ((-48 : BitVec 12)) = (18446744073709551568 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_neg40 :
    EvmAsm.Rv64.signExtend12 ((-40 : BitVec 12)) = (18446744073709551576 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_neg32 :
    EvmAsm.Rv64.signExtend12 ((-32 : BitVec 12)) = (18446744073709551584 : Word) := by decide

@[exp_addr, grind =] theorem exp_se12_256 :
    EvmAsm.Rv64.signExtend12 (256 : BitVec 12) = (256 : Word) := by decide

attribute [exp_addr]
  EvmAsm.Rv64.signExtend12_0 EvmAsm.Rv64.signExtend12_1
  EvmAsm.Rv64.signExtend12_8 EvmAsm.Rv64.signExtend12_16
  EvmAsm.Rv64.signExtend12_24 EvmAsm.Rv64.signExtend12_32
  EvmAsm.Rv64.signExtend12_40 EvmAsm.Rv64.signExtend12_48
  EvmAsm.Rv64.signExtend12_56 EvmAsm.Rv64.signExtend12_64
  EvmAsm.Rv64.signExtend12_neg16
  EvmAsm.Rv64.signExtend12_4095 EvmAsm.Rv64.signExtend12_4088
  EvmAsm.Rv64.signExtend12_4080 EvmAsm.Rv64.signExtend12_4072
  EvmAsm.Rv64.signExtend12_4064 EvmAsm.Rv64.signExtend12_4056
  EvmAsm.Rv64.signExtend12_4048 EvmAsm.Rv64.signExtend12_4040
  EvmAsm.Rv64.signExtend12_4032 EvmAsm.Rv64.signExtend12_4024
  EvmAsm.Rv64.signExtend12_4016 EvmAsm.Rv64.signExtend12_4008
  EvmAsm.Rv64.signExtend12_4000 EvmAsm.Rv64.signExtend12_3992
  EvmAsm.Rv64.signExtend12_3984 EvmAsm.Rv64.signExtend12_3976
  EvmAsm.Rv64.signExtend12_3968 EvmAsm.Rv64.signExtend12_3960
  EvmAsm.Rv64.signExtend12_3952 EvmAsm.Rv64.signExtend12_3944

@[exp_addr, grind =] theorem expAddr0 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 0#12 : Word) = addr := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr8 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 8#12 : Word) = addr + 8#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr16 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 16#12 : Word) = addr + 16#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr24 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 24#12 : Word) = addr + 24#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr32 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 32#12 : Word) = addr + 32#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr40 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 40#12 : Word) = addr + 40#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr48 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 48#12 : Word) = addr + 48#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAddr56 (addr : Word) :
    (addr + EvmAsm.Rv64.signExtend12 56#12 : Word) = addr + 56#64 := by
  unfold EvmAsm.Rv64.signExtend12; bv_decide

@[exp_addr, grind =] theorem expAdd32Add8 (addr : Word) :
    (addr + 32#64 + 8 : Word) = addr + 40#64 := by
  bv_decide

@[exp_addr, grind =] theorem expAdd32Add16 (addr : Word) :
    (addr + 32#64 + 16 : Word) = addr + 48#64 := by
  bv_decide

@[exp_addr, grind =] theorem expAdd32Add24 (addr : Word) :
    (addr + 32#64 + 24 : Word) = addr + 56#64 := by
  bv_decide

@[exp_addr, grind =] theorem expFullLoopCondMulCallAddr (base : Word) :
    (base + 148 : Word) = base + 144 + 4 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitCondMulTakenAddr (base : Word) :
    (base + 152 : Word) = base + 148 + 4 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitTwoMulCondMulTakenAddr (base : Word) :
    (base + 152 : Word) = (base + 28) + 120 + 4 := by
  bv_decide

@[exp_addr, grind =] theorem expTwoMulSkipLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  bv_decide

@[exp_addr, grind =] theorem expTwoMulCondMulCallExitPc (base : Word) :
    ((base + 152 : Word) + 104) = base + 256 := by
  bv_decide

@[exp_addr, grind =] theorem expLoopBackNextPc (base : Word) :
    ((base + 24 : Word) + 8) = base + 32 := by
  bv_decide

@[exp_addr, grind =] theorem expLoopSquareReturnPc (base : Word) :
    ((base + 12 : Word) + 4) = base + 16 := by
  bv_decide

@[exp_addr, grind =] theorem expLoopCondMulReturnPc (base : Word) :
    ((base + 16 : Word) + 8) = base + 24 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitSquaringPrefixExitPc (base : Word) :
    ((base + 44 : Word) + 104) = base + 148 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitSaveEntryAddr (base : Word) :
    (base + 40 : Word) = (base + 28) + 12 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitCondMulBeqEntryAddr (base : Word) :
    (base + 148 : Word) = (base + 28) + 120 := by
  bv_decide

@[exp_addr, grind =] theorem expSavedBitSquaringEntryAddr (base : Word) :
    (base + 44 : Word) = (base + 28) + 16 := by
  bv_decide

@[exp_addr, grind =] theorem expTopPointerAdvanceNextPc (base : Word) :
    ((base + 24 : Word) + 4) = base + 28 := by
  bv_decide

@[exp_addr, grind =] theorem expTopPointerRestoreNextPc (base : Word) :
    ((base + 260 : Word) + 4) = base + 264 := by
  bv_decide

@[exp_addr, grind =] theorem expTopEpilogueNextPc (base : Word) :
    ((base + 264 : Word) + 36) = base + 300 := by
  bv_decide

@[exp_addr, grind =] theorem expTopSavedBitEpilogueEntryNextPc (base : Word) :
    ((base + 264 : Word) + 4) = base + 268 := by
  bv_decide

@[exp_addr, grind =] theorem expTopSavedBitEpilogueNextPc (base : Word) :
    ((base + 268 : Word) + 36) = base + 304 := by
  bv_decide

@[exp_addr, grind =] theorem expTopIterBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  bv_decide

@[exp_addr, grind =] theorem expTopSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  bv_decide

@[exp_addr, grind =] theorem expTopLoopBackNextPc (base : Word) :
    ((base + 252 : Word) + 8) = base + 260 := by
  bv_decide

@[exp_addr, grind =] theorem expTopCondMulBeqNextPc (base : Word) :
    ((base + 144 : Word) + 4) = base + 148 := by
  bv_decide

@[exp_addr, grind =] theorem expTopSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  bv_decide

@[exp_addr, grind =] theorem expTopCondMulMarshalPairNextPc (base : Word) :
    ((base + 148 : Word) + 64) = base + 212 := by
  bv_decide

@[exp_addr, grind =] theorem expTopSquaringSquareReturnPc (base : Word) :
    ((base + 104 : Word) + 4) = base + 108 := by
  bv_decide

@[exp_addr, grind =] theorem expTopCondMulSquareReturnPc (base : Word) :
    ((base + 212 : Word) + 4) = base + 216 := by
  bv_decide

@[exp_addr, grind =] theorem expBaseAdd40Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 40 : Word) &&& 1 = 0 := by bv_decide

@[exp_addr, grind =] theorem expBaseAdd44Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 44 : Word) &&& 1 = 0 := by bv_decide

@[exp_addr, grind =] theorem expBaseAdd148Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 148 : Word) &&& 1 = 0 := by bv_decide

@[exp_addr, grind =] theorem expBaseAdd152Aligned
    (base : Word) (hbase : base &&& 1 = 0) :
    (base + 152 : Word) &&& 1 = 0 := by bv_decide

end EvmAsm.Evm64.Exp.AddrNorm
