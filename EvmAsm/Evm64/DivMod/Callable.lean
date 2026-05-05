/-
  EvmAsm.Evm64.DivMod.Callable

  LP64-callable shims around `evm_div` / `evm_mod`.

  Per `docs/sdiv-smod-design.md` §3 (corrected layout, PR #2376), the
  shim is **not** `evm_div ;; cc_ret`: appending `cc_ret` to the program
  text would place it at byte 1268, unreachable from `evm_div`'s exit
  PC. Instead we **replace the NOP** at the existing exit slot with
  `cc_ret`, keeping every other instruction at exactly the same offset
  (so internal branch targets — including `divK_loopBody`'s
  `subr_off = 556` into `divK_div128` — remain valid).

      evm_div  := … ;; ADDI .x0 .x0 0       ;; divK_div128
      evm_div_callable
              := … ;; cc_ret                 ;; divK_div128

  Same total instruction count (1:1 NOP↔cc_ret swap), same byte length
  (1276 bytes = 319 instructions), same exit PC (the slot that holds
  the swapped instruction sits at the same byte offset as the original
  NOP).

  This file is **prep slice A** for evm-asm-8pfe / GH #90: it
  introduces only the Program definitions and length lemmas.
  Code-region helpers, sub-code lemmas and the
  `_function_spec` round-trip will land in follow-up slices.

  Reference: GH #90 (parent evm-asm-34sg), beads slice evm-asm-0tnux.
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program definitions
-- ============================================================================

/-- LP64-callable wrapper for `evm_div`: swap the NOP at the exit slot
    with `cc_ret`. Every other phase / sub-block, including the
    appended `divK_div128` subroutine and all internal branch offsets,
    is kept at exactly the same instruction index as in `evm_div`. -/
def evm_div_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128

/-- LP64-callable wrapper for `evm_mod`: same shape as
    `evm_div_callable`, with `divK_mod_epilogue` for the remainder
    output. -/
def evm_mod_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128

end EvmAsm.Evm64
