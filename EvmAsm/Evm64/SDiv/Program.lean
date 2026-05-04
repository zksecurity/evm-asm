/-
  EvmAsm.Evm64.SDiv.Program

  Signed division opcode SDIV (`SDIV(a, b)` = signed-quotient under EVM
  rules) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6).

  The actual `evm_sdiv : Program` will be defined in slice
  evm-asm-01uh. Per `docs/sdiv-smod-design.md` the algorithm is

      1. extract sign of each operand (top bit of limb 3)
      2. conditionally two's-complement negate operands so both are
         non-negative; remember the sign-pair
      3. JAL to an `evm_div_callable` shim (LP64) for unsigned division
      4. conditionally negate the quotient based on `sign(a) XOR sign(b)`
      5. apply the SDIV(-2^255, -1) = -2^255 fast-path overflow rule

  This file currently has no `evm_sdiv` definition; later slices will
  add it without breaking the umbrella import graph.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: `evm_sdiv : Program` lands in slice 4 (evm-asm-01uh).
-- See `docs/sdiv-smod-design.md` for the algorithm and reuse points.

end EvmAsm.Evm64
