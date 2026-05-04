/-
  EvmAsm.Evm64.SMod.Program

  Signed remainder opcode SMOD (`SMOD(a, b)` = signed-remainder under EVM
  rules) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6).

  The actual `evm_smod : Program` will be defined in slice
  evm-asm-bjnb. Per `docs/sdiv-smod-design.md` the algorithm is

      1. extract sign of each operand (top bit of limb 3)
      2. conditionally two's-complement negate operands so both are
         non-negative; remember `sign(a)`
      3. JAL to an `evm_mod_callable` shim (LP64) for unsigned modulo
      4. conditionally negate the remainder based on `sign(a)`
         (EVM SMOD takes the sign of the dividend)

  This file currently has no `evm_smod` definition; later slices will
  add it without breaking the umbrella import graph.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: `evm_smod : Program` lands in slice 5 (evm-asm-bjnb).
-- See `docs/sdiv-smod-design.md` for the algorithm and reuse points.

end EvmAsm.Evm64
