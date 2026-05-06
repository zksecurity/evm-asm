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

-- ============================================================================
-- Slice 3b — Phase 2 (modulus reduction) + Epilogue program skeletons
-- ============================================================================
--
-- Per `docs/91-addmod-mulmod-survey.md` §5.1, after the prologue + phase 1
-- finish, the runtime state is:
--
--   * `x12 = sp + 32` (advanced by `evm_add`'s trailing `ADDI x12, x12, 32`)
--   * Top stack cell at `x12 + 0..24` holds `r := (a + b) (mod 2^256)`
--   * Stack cell at `x12 + 32..58` holds `N` (the modulus) — untouched
--   * `x7` holds the 257th carry bit `c ∈ {0, 1}` of `a.toNat + b.toNat`
--
-- The remaining work decomposes into three bite-sized blocks (as four
-- separate `Program`s here, plus the assembled phase-2 wrapper in slice
-- 3c). All branch / call distances are passed in as `BitVec`-typed
-- parameters so the assembled `evm_addmod` Program in slice 3c
-- (`evm-asm-xl2jn`) can pin the concrete offsets without re-rolling
-- this file.
--
-- This slice introduces only the program text and length lemmas; per
-- `evm-asm-f027s` acceptance, no `cpsTriple` proofs are required.
-- The actual stack-level `evm_addmod_stack_spec` is the job of slice 3d
-- (`evm-asm-s7v49`).

/-- Phase 2 — short-circuit test for `N = 0`.

    OR-folds the four 64-bit limbs of `N` (currently at `x12 + 32..56`,
    since the prologue advanced `x12` by 32 and `N` was originally the
    third stack cell) into scratch register `x6`, then takes a
    forward `BEQ x6, x0, skipOff` branch to the zero-store path when
    `N` is identically zero. The `BEQ` byte offset `skipOff` is the
    distance from this BEQ instruction to the entry of
    `evm_addmod_phase2_zero_path`; the concrete value is pinned in
    slice 3c when `evm_addmod` is assembled.

    8 instructions:

      LD  x6, x12, 32     -- N limb 0
      LD  x5, x12, 40     -- N limb 1
      OR  x6, x6, x5
      LD  x5, x12, 48     -- N limb 2
      OR  x6, x6, x5
      LD  x5, x12, 56     -- N limb 3
      OR  x6, x6, x5
      BEQ x6, x0, skipOff -- if N = 0, branch to zero-store path
-/
def evm_addmod_phase2_n_zero_test (skipOff : BitVec 13) : Program :=
  LD .x6 .x12 32 ;;
  LD .x5 .x12 40 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 48 ;;
  OR' .x6 .x6 .x5 ;;
  LD .x5 .x12 56 ;;
  OR' .x6 .x6 .x5 ;;
  single (.BEQ .x6 .x0 skipOff)

theorem evm_addmod_phase2_n_zero_test_length (skipOff : BitVec 13) :
    (evm_addmod_phase2_n_zero_test skipOff).length = 8 := by
  show ((((((((LD .x6 .x12 32 ;; LD .x5 .x12 40) ;; OR' .x6 .x6 .x5) ;;
              LD .x5 .x12 48) ;; OR' .x6 .x6 .x5) ;;
            LD .x5 .x12 56) ;; OR' .x6 .x6 .x5) ;;
          single (.BEQ .x6 .x0 skipOff)) : Program).length = 8
  simp only [seq, Program.length_append]
  rfl

theorem evm_addmod_phase2_n_zero_test_byte_length (skipOff : BitVec 13) :
    4 * (evm_addmod_phase2_n_zero_test skipOff).length = 32 := by
  rw [evm_addmod_phase2_n_zero_test_length]

/-- Phase 2 — modulus-reduction call site.

    Single-instruction near `JAL` invocation of `evm_mod_callable`
    (the LP64 shim around `evm_mod`, see
    `EvmAsm/Evm64/DivMod/Callable.lean`). The full reduction
    pipeline per the survey is

       1. compute `m := 2^256 mod N`        (a near-call to `evm_mod`)
       2. compute `(c · m + r) mod N`       (a second near-call to
                                              `evm_mod` after a
                                              257-bit accumulate)

    Both call sites share the same `JAL x1, modOff` shape; this
    block is a single such call. The surrounding scaffolding
    (argument marshalling, post-call result move, the conditional
    use of the carry bit `c`) lives in slice 3c (`evm-asm-xl2jn`)
    when the loop layout is final.

    The `modOff : BitVec 21` parameter is the signed 21-bit byte
    offset from the JAL site to the entry of `evm_mod_callable`;
    the concrete numeric value is pinned in slice 3c.

    1 instruction. -/
def evm_addmod_phase2_mod_call (modOff : BitVec 21) : Program :=
  JAL .x1 modOff

theorem evm_addmod_phase2_mod_call_length (modOff : BitVec 21) :
    (evm_addmod_phase2_mod_call modOff).length = 1 := rfl

theorem evm_addmod_phase2_mod_call_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_phase2_mod_call modOff).length = 4 := by
  rw [evm_addmod_phase2_mod_call_length]

/-- Phase 2 — composite reduce body (the non-zero-N path).

    Sequences the modulus-reduction call into a structural block.
    For the no-proofs slice we keep this thin: a single
    `JAL x1, modOff` near-call. Slice 3c may either wrap this in
    additional marshalling instructions or replace it with a richer
    composition of `evm_addmod_phase2_mod_call` invocations once the
    full m / accumulate pipeline is laid out.

    Currently 1 instruction; the parameter shape is fixed so slice
    3c does not need to re-derive offsets if the body grows.

    The trailing `JAL x0, exitOff` (an unconditional branch past the
    zero-store path to the epilogue entry) is *not* part of this
    block — slice 3c emits it inline so that the zero-store path
    can BEQ-skip exactly past the reduce body without extra
    bookkeeping. -/
def evm_addmod_phase2_reduce (modOff : BitVec 21) : Program :=
  evm_addmod_phase2_mod_call modOff

theorem evm_addmod_phase2_reduce_length (modOff : BitVec 21) :
    (evm_addmod_phase2_reduce modOff).length = 1 := rfl

theorem evm_addmod_phase2_reduce_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod_phase2_reduce modOff).length = 4 := by
  rw [evm_addmod_phase2_reduce_length]

/-- Phase 2 — zero-store path (taken when `N = 0`).

    On entry: `x12 = sp + 32`, the result cell is at `x12 + 32 .. 56`
    (currently holding `N = 0`, but we overwrite to be explicit and
    to make the instruction sequence symmetric with the non-zero
    path's writeback). 4 `SD x12, x0, k` stores write zero into
    each of the four output limbs; the epilogue (separate block)
    handles the trailing `ADDI x12, x12, 32` that ADDMOD shares
    between both paths.

    4 instructions. -/
def evm_addmod_phase2_zero_path : Program :=
  SD .x12 .x0 32 ;;
  SD .x12 .x0 40 ;;
  SD .x12 .x0 48 ;;
  SD .x12 .x0 56

theorem evm_addmod_phase2_zero_path_length :
    evm_addmod_phase2_zero_path.length = 4 := by decide

theorem evm_addmod_phase2_zero_path_byte_length :
    4 * evm_addmod_phase2_zero_path.length = 16 := by
  rw [evm_addmod_phase2_zero_path_length]

/-- ADDMOD epilogue: shared writeback / pointer-advance suffix that
    runs after either the reduce-via-mod path or the zero-store path
    has placed the 256-bit result into the four limb cells at
    `x12 + 32 .. 56`.

    On entry: `x12 = sp + 32` (advanced once by the prologue's
    `evm_add`), result at `x12 + 32..58`. On exit: `x12 = sp + 64`
    (the original ADDMOD top-of-stack after popping `[a, b, N]` and
    pushing one cell), with the result now occupying `x12 + 0..24`.

    A single `ADDI x12, x12, 32` performs the final pointer advance.
    The result limbs are already in place from the upstream blocks —
    the epilogue does not move data, only the pointer.

    1 instruction. -/
def evm_addmod_epilogue : Program :=
  ADDI .x12 .x12 32

theorem evm_addmod_epilogue_length :
    evm_addmod_epilogue.length = 1 := by decide

theorem evm_addmod_epilogue_byte_length :
    4 * evm_addmod_epilogue.length = 4 := by
  rw [evm_addmod_epilogue_length]

-- ============================================================================
-- Slice 3c — top-level `evm_addmod` Program assembly + length lemmas
-- ============================================================================
--
-- This slice glues the four block skeletons (prologue / phase1 carry /
-- phase2 reduce / epilogue) into the top-level `evm_addmod` Program.
-- The phase-2 modulus-reduction call site takes a signed 21-bit byte
-- offset `modOff` to the entry of `evm_mod_callable`; the concrete
-- numeric value is pinned by the surrounding caller frame and is
-- threaded through unchanged here.
--
-- Per the slice acceptance, this is glue only — no `cpsTriple` proofs.
-- The eventual `evm_addmod_stack_spec` is the job of slice 3d
-- (`evm-asm-s7v49`); it consumes the per-block byte-offset lemmas
-- proved here to align block entries with PC values.
--
-- Block layout (instruction index → byte offset within `evm_addmod`):
--
--   prologue      : instr  0 .. 29  (length 30, bytes   0 ..119)
--   phase1_carry  : instr 30        (length  1, byte  120)
--   phase2_reduce : instr 31        (length  1, byte  124)
--   epilogue      : instr 32        (length  1, byte  128)
--   end           : instr 33        (              byte 132)
--
-- The phase-2 zero-path / `phase2_n_zero_test` blocks defined above
-- are *not* part of this skeleton — the linear assembly here matches
-- the slice description exactly. A richer assembly that wires in the
-- `N = 0` short-circuit branch will be folded in at slice 3d when the
-- runtime branch shape stabilises.

/-- Top-level ADDMOD program: prologue ;; phase1 carry ;; phase2 reduce
    (one near-call to `evm_mod_callable`) ;; epilogue. The `modOff`
    parameter is the signed 21-bit byte offset from the phase-2 JAL
    site to the entry of `evm_mod_callable`; it is pinned by the
    surrounding dispatcher frame. -/
def evm_addmod (modOff : BitVec 21) : Program :=
  evm_addmod_prologue ;;
  evm_addmod_phase1_carry ;;
  evm_addmod_phase2_reduce modOff ;;
  evm_addmod_epilogue

theorem evm_addmod_length (modOff : BitVec 21) :
    (evm_addmod modOff).length = 33 := by
  show ((((evm_addmod_prologue ;; evm_addmod_phase1_carry) ;;
            evm_addmod_phase2_reduce modOff) ;;
          evm_addmod_epilogue) : Program).length = 33
  simp only [seq, Program.length_append,
    evm_addmod_prologue_length, evm_addmod_phase1_carry_length,
    evm_addmod_phase2_reduce_length, evm_addmod_epilogue_length]

theorem evm_addmod_byte_length (modOff : BitVec 21) :
    4 * (evm_addmod modOff).length = 132 := by
  rw [evm_addmod_length]

/-- Byte offset of the prologue block within `evm_addmod`. -/
theorem evm_addmod_prologue_byte_off : 4 * 0 = 0 := by rfl

/-- Byte offset of the phase-1 carry block within `evm_addmod`. -/
theorem evm_addmod_phase1_carry_byte_off : 4 * 30 = 120 := by rfl

/-- Byte offset of the phase-2 reduce block within `evm_addmod`. -/
theorem evm_addmod_phase2_reduce_byte_off : 4 * 31 = 124 := by rfl

/-- Byte offset of the epilogue block within `evm_addmod`. -/
theorem evm_addmod_epilogue_byte_off : 4 * 32 = 128 := by rfl

/-- Byte offset immediately after the full `evm_addmod` program. -/
theorem evm_addmod_end_byte_off : 4 * 33 = 132 := by rfl

/-- Sanity check: the assembled `evm_addmod` length equals the sum of
    its four sub-block lengths. Picks an arbitrary `modOff` since the
    `evm_addmod_phase2_reduce` length is independent of it. -/
example : (evm_addmod 0).length =
    evm_addmod_prologue.length +
    evm_addmod_phase1_carry.length +
    (evm_addmod_phase2_reduce 0).length +
    evm_addmod_epilogue.length := by
  native_decide

end EvmAsm.Evm64
