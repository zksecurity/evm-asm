/-
  EvmAsm.Evm64.SMod.AddrNorm

  Address-normalization simp set for SMOD composition proofs.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). The
  `@[smod_addr, grind =]`-tagged atomic facts will be added once the
  Compose layer (`SMod/Compose/...`) starts emitting concrete address
  arithmetic. For now this file just imports the shared `Rv64.AddrNorm`
  base and the attribute declaration so downstream files can already
  open the namespace.
-/

import EvmAsm.Rv64.AddrNorm
import EvmAsm.Evm64.SMod.AddrNormAttr

namespace EvmAsm.Evm64.SMod.AddrNorm

open EvmAsm.Rv64

end EvmAsm.Evm64.SMod.AddrNorm
