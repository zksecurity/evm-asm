/-
  EvmAsm.Evm64.AddMod.Program

  ADDMOD opcode (`ADDMOD(a, b, N)` = (a + b) mod N under EVM
  rules, with `N = 0` returning `0`) as a 64-bit RISC-V program.

  Skeleton placeholder for GH #91 (beads slice evm-asm-w1s0).

  Slice `evm-asm-4gq5y` lands the first two building blocks of the
  decomposition described in `docs/91-addmod-mulmod-survey.md` §5.1:

  * `evm_addmod_prologue` — fold `a + b` into the second operand slot
    using the existing 4-limb `evm_add` Program. After this block, the
    EVM stack is `[a + b (mod 2^256), N, …]` and `x12` has advanced by
    +32. The 257th carry-out bit produced by the limb-3 add of
    `evm_add` is left in scratch register `x5` (per
    `EvmAsm/Evm64/Add/Program.lean`); the next block parks it in `x7`.
  * `evm_addmod_phase1_carry` — copy the 257th carry bit from `x5`
    (where `evm_add` deposits it) into the dedicated scratch register
    `x7`, freeing `x5` for the modulus-reduction phase that follows
    (which reuses `x5..x6/x11` as inner-loop scratch).

  The actual top-level `evm_addmod : Program` will be assembled in a
  later slice (`evm-asm-xl2jn`); this file currently only carries the
  prologue + phase 1 sub-programs and their length lemmas.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Evm64.Add.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- ADDMOD prologue: fold `a + b` (mod 2^256) into the second-from-top
    EVM stack slot using the existing 4-limb `evm_add` Program. On
    entry: stack top-to-bottom is `[a, b, N, …]` (32 bytes each, with
    `a` at `x12 + 0`, `b` at `x12 + 32`, `N` at `x12 + 64`). On exit:
    `x12` has advanced by +32 and the top two cells are
    `[a + b (mod 2^256), N, …]`; `N` at the original `x12 + 64` is
    untouched (it now sits at the new `x12 + 32`).

    Note: `evm_add` is reused verbatim — it performs the limb-by-limb
    schoolbook add and finishes with `ADDI x12, x12, 32`. Crucially,
    `evm_add`'s final block leaves the limb-3 carry-out bit (i.e. the
    257th bit of `a.toNat + b.toNat`) in scratch register `x5` via
    the trailing `OR x5, x11, x6` (see `EvmAsm/Evm64/Add/Program.lean`
    line 36). `evm_addmod_phase1_carry` consumes that bit immediately.

    Length: identical to `evm_add` (30 instructions: 5 + 3·8 + 1
    trailing `ADDI`). -/
def evm_addmod_prologue : Program :=
  evm_add

theorem evm_addmod_prologue_length :
    evm_addmod_prologue.length = 30 := by decide

theorem evm_addmod_prologue_byte_length :
    4 * evm_addmod_prologue.length = 120 := by
  rw [evm_addmod_prologue_length]

/-- ADDMOD phase 1 — park the 257th carry bit into the dedicated
    scratch register `x7`.

    On entry (immediately after `evm_addmod_prologue` = `evm_add`):
    `x5` holds the 257th carry-out bit of `a.toNat + b.toNat` (`0` or
    `1`), per the trailing `OR x5, x11, x6` in `evm_add`'s limb-3
    block. The remainder of ADDMOD wants this bit in `x7` so that
    `x5..x6/x11` are free as scratch for the upcoming modulus
    reduction phase.

    Implementation: a single register move `x7 := x5`, encoded as
    `ADDI x7, x5, 0` (the canonical RV64 `MV` pseudo-instruction
    spelling already used elsewhere in the codebase, e.g.
    `EvmAsm/Rv64/RLP/Phase3LongList.lean`).

    1 instruction. -/
def evm_addmod_phase1_carry : Program :=
  ADDI .x7 .x5 0

theorem evm_addmod_phase1_carry_length :
    evm_addmod_phase1_carry.length = 1 := by decide

theorem evm_addmod_phase1_carry_byte_length :
    4 * evm_addmod_phase1_carry.length = 4 := by
  rw [evm_addmod_phase1_carry_length]

end EvmAsm.Evm64
