/-
  EvmAsm.Evm64.SDiv.AddrNorm

  Address-normalization simp set for SDIV composition proofs.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). The
  `@[sdiv_addr, grind =]`-tagged atomic facts will be added once the
  Compose layer (`SDiv/Compose/...`) starts emitting concrete address
  arithmetic. For now this file just imports the shared `Rv64.AddrNorm`
  base and the attribute declaration so downstream files can already
  open the namespace.
-/

import EvmAsm.Rv64.AddrNorm
import EvmAsm.Evm64.SDiv.AddrNormAttr

namespace EvmAsm.Evm64.SDiv.AddrNorm

open EvmAsm.Rv64

end EvmAsm.Evm64.SDiv.AddrNorm
