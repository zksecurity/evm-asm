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

namespace EvmAsm.Evm64.Exp.AddrNorm

open EvmAsm.Rv64

attribute [exp_addr]
  signExtend12_0 signExtend12_1 signExtend12_8 signExtend12_16
  signExtend12_24 signExtend12_32 signExtend12_40 signExtend12_48
  signExtend12_56 signExtend12_64
  signExtend12_neg16
  signExtend12_4095 signExtend12_4088 signExtend12_4080 signExtend12_4072
  signExtend12_4064 signExtend12_4056 signExtend12_4048 signExtend12_4040
  signExtend12_4032 signExtend12_4024 signExtend12_4016 signExtend12_4008
  signExtend12_4000 signExtend12_3992 signExtend12_3984 signExtend12_3976
  signExtend12_3968 signExtend12_3960 signExtend12_3952 signExtend12_3944

end EvmAsm.Evm64.Exp.AddrNorm
