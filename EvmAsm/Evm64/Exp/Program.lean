/-
  EvmAsm.Evm64.Exp.Program

  256-bit EVM EXP opcode (`EXP(a, b) = a^b mod 2^256`) as a 64-bit RISC-V
  program.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c).

  The actual Program will be defined in the Program-definition slice
  (evm-asm-ahaz). Per `docs/92-exp-survey.md` the algorithm is binary
  square-and-multiply over 256 bits of exponent, invoking `evm_mul`
  (made callable via a `cc_ret` shim) once per squaring and conditionally
  once per set bit. The full bytecode will be assembled from sub-blocks
  `exp_prologue`, `exp_square_block`, `exp_cond_mul_block`, `exp_iter_body`,
  `exp_loop`, `exp_epilogue`.

  This file currently has no `evm_exp` definition; later slices will add
  it without breaking the umbrella import graph.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Iteration sub-blocks (#92 slice 3a, beads evm-asm-dl98)
-- ============================================================================
--
-- Per `docs/92-exp-survey.md` §4 the per-iteration body of the
-- square-and-multiply loop decomposes into three sub-blocks:
--
--     exp_iter_body :=
--       exp_bit_test_block ;;     -- x10 := bit i of b; advance bit cursor
--       exp_square_block ;;       -- result := result * result   (JAL mul_callable)
--       exp_cond_mul_block        -- if x10 == 0 skip; else result := result * a
--                                 --   (BEQ ;; JAL mul_callable)
--
-- This slice introduces the three sub-blocks as parameterized `Program`s.
-- Argument-marshalling (copying `result` / `a` into the LP64 a/b slots
-- expected by `mul_callable`) and the surrounding 256-iteration loop scaffold
-- land in later slices (evm-asm-ahaz / evm-asm-mtj3 / evm-asm-w5mk).
--
-- Register usage (provisional, refined when slice 3b wires marshalling):
--   x5  — current limb of exponent b, shifted right one bit per iteration
--   x6  — remaining bits in the current limb (init 64, refilled at limb boundary)
--   x10 — current bit value (0 or 1) after `exp_bit_test_block`
--   x12 — EVM stack pointer (LP64 a2)
--   x1  — return address (set by `JAL .x1 …` into `mul_callable`)
--
-- The `mulOff : BitVec 21` parameter is the signed JAL offset from the JAL
-- site to the entry of `mul_callable`. The actual numeric value is pinned
-- once `evm_exp` is laid out (slice evm-asm-ahaz).

/-- Single iteration of the bit-cursor: extract the low bit of `x5` into
    `x10`, then shift `x5` right by one and decrement the remaining-bits
    counter `x6`. 3 instructions. -/
def exp_bit_test_block : Program :=
  ANDI .x10 .x5 1 ;;
  SRLI .x5 .x5 1 ;;
  ADDI .x6 .x6 (-1)

/-- Always-on squaring step: invoke `mul_callable` via a near `JAL`.
    Argument marshalling (placing both factors at the LP64 input slots
    relative to `x12`) is handled by the surrounding scaffold; this block
    is just the call. 1 instruction. -/
def exp_square_block (mulOff : BitVec 21) : Program :=
  JAL .x1 mulOff

/-- Conditional multiply by base `a`: if the current bit `x10` is zero,
    branch past the JAL using `skipOff` (the byte offset from the BEQ to
    the instruction immediately after the JAL). Otherwise fall through
    into a near `JAL` to `mul_callable`. 2 instructions. -/
def exp_cond_mul_block (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  BEQ .x10 .x0 skipOff ;;
  JAL .x1 mulOff

-- ----------------------------------------------------------------------------
-- Length lemmas
-- ----------------------------------------------------------------------------

theorem exp_bit_test_block_length : exp_bit_test_block.length = 3 := by decide

theorem exp_square_block_length (mulOff : BitVec 21) :
    (exp_square_block mulOff).length = 1 := rfl

theorem exp_cond_mul_block_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_block mulOff skipOff).length = 2 := rfl

-- ----------------------------------------------------------------------------
-- Per-iteration composite: exp_iter_body (#92 slice 3b, beads evm-asm-hdov)
-- ----------------------------------------------------------------------------
--
-- One full iteration of the square-and-multiply loop body, composed from the
-- three sub-blocks introduced in slice 3a. Per `docs/92-exp-survey.md` §4,
-- the iteration body decomposes as:
--
--     exp_iter_body :=
--       exp_bit_test_block ;;       -- 3 instr: x10 := bit i of b; advance cursor
--       exp_square_block mulOff ;;  -- 1 instr: result := result * result
--       exp_cond_mul_block mulOff skipOff
--                                   -- 2 instr: if x10 == 0 skip, else result := result * a
--
-- Total: 6 instructions per iteration. Argument-marshalling (copying
-- `result` / `a` into the LP64 a0/a1 slots expected by `mul_callable`) is
-- still handled by the surrounding 256-iteration scaffold introduced in
-- evm-asm-ahaz / evm-asm-w5mk; this slice is structural composition only.

/-- One full iteration of the EXP square-and-multiply loop body: bit test,
    unconditional squaring (JAL into `mul_callable`), conditional multiply
    by base `a` (BEQ-skipped JAL). 6 instructions.

    `mulOff` is the signed JAL offset to `mul_callable` (shared between the
    two JAL sites in this iteration; both call sites are at the same
    program-relative position when expanded across the loop, but the actual
    numeric value is pinned once `evm_exp` is laid out in slice
    evm-asm-ahaz). `skipOff` is the BEQ branch offset that skips past the
    second JAL when the current exponent bit is zero. -/
def exp_iter_body (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  exp_bit_test_block ;;
  exp_square_block mulOff ;;
  exp_cond_mul_block mulOff skipOff

theorem exp_iter_body_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_iter_body mulOff skipOff).length = 6 := by
  show ((exp_bit_test_block ;; exp_square_block mulOff) ;;
        exp_cond_mul_block mulOff skipOff).length = 6
  simp only [seq, Program.length_append, exp_bit_test_block_length,
    exp_square_block_length, exp_cond_mul_block_length]

theorem exp_iter_body_byte_length (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_iter_body mulOff skipOff).length = 24 := by
  rw [exp_iter_body_length]

-- ----------------------------------------------------------------------------
-- Loop-back tail: counter decrement + backward BNE (#92 slice 3c, beads
-- evm-asm-46ue)
-- ----------------------------------------------------------------------------
--
-- The square-and-multiply loop runs for exactly 256 iterations (one per bit
-- of the 256-bit exponent). Per `docs/92-exp-survey.md` §4 ("Iteration
-- counter via decrement-and-branch"), the master iteration counter lives in
-- a dedicated register (`x9`), initialized to 256 by the prologue, and the
-- bottom of every iteration decrements it and branches back to the top of
-- the loop body while it is still nonzero.
--
-- `exp_loop_back` packages those two trailing instructions as a standalone
-- `Program` block so the surrounding scaffold (`evm_exp`, slice
-- evm-asm-ahaz) and the loop-composition spec (slice evm-asm-w5mk) can
-- compose it independently of `exp_iter_body` and pin the concrete
-- backward `backOff` once `evm_exp` is laid out.
--
-- Register usage:
--   x9 — master iteration counter (decremented by 1 each iteration; loop
--        exits when it reaches 0). Distinct from `x6` in `exp_bit_test_block`,
--        which counts remaining bits in the current 64-bit limb of the
--        exponent and is refilled at limb boundaries by separate
--        scaffolding.
--
-- The `backOff : BitVec 13` parameter is the *signed* 13-bit BNE offset from
-- the BNE site back to the top of the iteration body. The offset is
-- byte-counted (4 bytes per RV64 instruction) and negative for a backward
-- branch. The actual numeric value is pinned in slice evm-asm-ahaz when
-- `evm_exp` is assembled and the loop body length is final.

/-- Tail of the EXP square-and-multiply loop: decrement the master 256-bit
    iteration counter `x9` by 1, then branch back to the top of the loop
    body if `x9` is still nonzero. 2 instructions.

    `backOff` is the signed 13-bit BNE byte offset from the BNE site back
    to the top of the iteration body (negative). The concrete value is
    pinned by the surrounding `evm_exp` layout in slice evm-asm-ahaz. -/
def exp_loop_back (backOff : BitVec 13) : Program :=
  ADDI .x9 .x9 (-1) ;;
  single (.BNE .x9 .x0 backOff)

theorem exp_loop_back_length (backOff : BitVec 13) :
    (exp_loop_back backOff).length = 2 := by
  show (ADDI .x9 .x9 (-1) ;; single (.BNE .x9 .x0 backOff)).length = 2
  rfl

theorem exp_loop_back_byte_length (backOff : BitVec 13) :
    4 * (exp_loop_back backOff).length = 8 := by
  rw [exp_loop_back_length]

-- ----------------------------------------------------------------------------
-- Per-iteration loop block: exp_loop (#92 slice 3d, beads evm-asm-j2h5)
-- ----------------------------------------------------------------------------
--
-- Structural composition of one full square-and-multiply iteration with its
-- trailing counter-decrement + backward branch. This is the unit that the
-- 256-iteration loop scaffold (`evm_exp`, slice evm-asm-ahaz) repeats and that
-- the loop-composition spec (slice evm-asm-w5mk) reasons about.
--
-- Layout (8 instructions = 32 bytes per iteration):
--
--     exp_loop mulOff skipOff backOff :=
--       exp_iter_body  mulOff skipOff ;;   -- 6 instr (bit test + sq + cond mul)
--       exp_loop_back  backOff             -- 2 instr (ADDI x9 -1 ;; BNE)
--
-- The three offsets stay parameters — they are only pinned once `evm_exp` is
-- assembled in slice evm-asm-ahaz and the absolute layout is final. No new
-- specs in this slice; per-block specs (4a/4b/4c/4d) are already merged and
-- the composed cpsTriple lands in slice 5 (evm-asm-w5mk).

/-- One full iteration of the EXP square-and-multiply loop, including the
    iteration-counter decrement and backward branch back to the top. 8
    instructions.

    `mulOff` is the signed JAL offset to `mul_callable` (shared between the
    two JAL sites inside the iteration body). `skipOff` is the BEQ branch
    offset that skips past the conditional-multiply JAL when the current
    exponent bit is zero. `backOff` is the signed 13-bit BNE byte offset from
    the BNE site back to the top of the iteration body (negative). All three
    are pinned by the surrounding `evm_exp` layout in slice evm-asm-ahaz. -/
def exp_loop (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : Program :=
  exp_iter_body mulOff skipOff ;;
  exp_loop_back backOff

theorem exp_loop_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    (exp_loop mulOff skipOff backOff).length = 8 := by
  show (exp_iter_body mulOff skipOff ;; exp_loop_back backOff).length = 8
  simp only [seq, Program.length_append,
    exp_iter_body_length, exp_loop_back_length]

theorem exp_loop_byte_length (mulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    4 * (exp_loop mulOff skipOff backOff).length = 32 := by
  rw [exp_loop_length]

-- ----------------------------------------------------------------------------
-- Loop prologue: initialize accumulator + counter (#92 slice 3d, beads
-- evm-asm-yvfr)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-survey.md` §2(b) and §4, the EXP body needs two pieces of
-- state initialized before the 256-iteration square-and-multiply loop runs:
--
--   1. The running accumulator `result` (a 256-bit value held as 4 LE 64-bit
--      limbs in the local RISC-V scratch frame at `sp+0 .. sp+24`) must be
--      initialized to 1, i.e. (limb0, limb1, limb2, limb3) = (1, 0, 0, 0).
--   2. The master iteration counter `x9` must be initialized to 256.
--
-- This block does NOT include the LP64 `cc_prologue` (which is emitted by the
-- surrounding non-leaf `evm_exp` wrapper) and does NOT marshal the EVM stack
-- operands `a` / `b` into LP64 a0/a1 slots (handled per-iteration by the
-- scaffold introduced in slice evm-asm-w5mk). It is the EXP-specific tail of
-- the prologue: counter init + accumulator init.
--
-- Convention assumed by this block: the `evm_exp` wrapper has already moved
-- `sp` (x2) down by enough bytes to give us a 32-byte 8-byte-aligned region
-- at offsets `[0, 24]` for the four `result` limbs (low limb at +0, high
-- limb at +24). The wrapper will lay out the rest of its scratch frame —
-- saved ra, alignment, any spilled values — at offsets ≥ 32, so the four
-- SDs here only touch the result slots.
--
-- Register usage:
--   x9  — master iteration counter (output: 256)
--   x5  — t0, used as a temporary to hold the literal `1` before the SD;
--          caller-saved per LP64, not live across calls so safe to clobber
--          before the loop body ever runs.
--   x2  — sp; read-only here.
--   x0  — zero register, used directly in the three high-limb SDs to avoid
--          a second ADDI for an additional zero temp.
--
-- 6 instructions, 24 bytes:
--   ADDI x9, x0, 256   — counter := 256
--   ADDI x5, x0, 1     — t0      := 1
--   SD   sp, t0, 0     — result.limb0 := 1
--   SD   sp, x0, 8     — result.limb1 := 0
--   SD   sp, x0, 16    — result.limb2 := 0
--   SD   sp, x0, 24    — result.limb3 := 0

/-- EXP-specific prologue: initialize the master iteration counter
    `x9 := 256` and the four limbs of the running accumulator `result`
    in the local scratch frame at `sp+0 .. sp+24` to `(1, 0, 0, 0)`.
    Excludes the LP64 `cc_prologue` (which the surrounding `evm_exp`
    wrapper emits separately) and operand marshalling. 6 instructions. -/
def exp_prologue : Program :=
  ADDI .x9 .x0 256 ;;
  ADDI .x5 .x0 1 ;;
  SD .x2 .x5 0 ;;
  SD .x2 .x0 8 ;;
  SD .x2 .x0 16 ;;
  SD .x2 .x0 24

theorem exp_prologue_length : exp_prologue.length = 6 := by decide

theorem exp_prologue_byte_length : 4 * exp_prologue.length = 24 := by
  rw [exp_prologue_length]

-- ----------------------------------------------------------------------------
-- Loop epilogue: result writeback + EVM stack advance (#92 slice 3e, beads
-- evm-asm-tesj)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-survey.md` §"Result write-back" (line 178), once the
-- 256-iteration square-and-multiply loop has finished, the four limbs of the
-- running accumulator `result` (held in the local scratch frame at
-- `sp + 0 .. sp + 24`) must be copied out to the EVM stack at
-- `x12 + 32 .. x12 + 56` (the slot that originally held operand `a` on
-- entry, since both `a` and `b` are popped and a single 256-bit result is
-- pushed). Then `x12` advances by +32 (one EVM-word pop, since EXP pops
-- two 256-bit operands and pushes one result).
--
-- This block does NOT include the LP64 `cc_epilogue` (which the surrounding
-- `evm_exp` non-leaf wrapper emits separately, restoring `ra`/`sp` and
-- returning to the caller). It is the EXP-specific tail of the body:
-- writeback + EVM stack-pointer fixup, mirroring the role of `mul_epilogue`
-- in `Evm64/Multiply/Program.lean` but with an additional 4-limb LD/SD
-- copy because EXP holds its accumulator in the local scratch frame
-- rather than directly on the EVM stack.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); advanced by +32 at the very end.
--   x5  — t0, used as a single-limb load/store temporary; caller-saved per
--          LP64 and not live across the surrounding loop, so safe to clobber.
--
-- 9 instructions, 36 bytes:
--   LD   t0, sp, 0     — t0          := result.limb0
--   SD   x12, t0, 32   — evm_stack[0] := t0
--   LD   t0, sp, 8     — t0          := result.limb1
--   SD   x12, t0, 40   — evm_stack[1] := t0
--   LD   t0, sp, 16    — t0          := result.limb2
--   SD   x12, t0, 48   — evm_stack[2] := t0
--   LD   t0, sp, 24    — t0          := result.limb3
--   SD   x12, t0, 56   — evm_stack[3] := t0
--   ADDI x12, x12, 32  — pop one EVM word

/-- EXP-specific epilogue: copy the four limbs of the running accumulator
    `result` from the local scratch frame at `sp + 0 .. sp + 24` to the
    EVM stack at `x12 + 32 .. x12 + 56`, then advance the EVM stack
    pointer `x12` by +32 (one EVM-word pop). Excludes the LP64
    `cc_epilogue` (which the surrounding `evm_exp` wrapper emits
    separately). 9 instructions. -/
def exp_epilogue : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 56 ;;
  ADDI .x12 .x12 32

theorem exp_epilogue_length : exp_epilogue.length = 9 := by decide

theorem exp_epilogue_byte_length : 4 * exp_epilogue.length = 36 := by
  rw [exp_epilogue_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-factor1, beads
-- evm-asm-6hue)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-frame-design.md` §5 and §8 action item 1, every
-- per-iteration MUL call (both the unconditional squaring and the
-- conditional multiply by base `a`) needs to copy the running accumulator
-- `result` (held in the local scratch frame at `sp + 0 .. sp + 24`) into
-- the LP64 MUL factor-1 slot at `x12 + 0 .. x12 + 24`. This is the same
-- 8-instruction LD/SD chain in both call sites; we factor it out here as a
-- reusable `Program` so the two marshalling Programs (squaring marshal,
-- conditional-multiply marshal) can share it.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue, so writes at offsets +0 .. +24 land in the
--          factor-1 slot disjoint from the operand region (`sp_evm0 + 0
--          .. + 56`).
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of `result` from the local scratch frame at
    `sp + 0 .. sp + 24` into the LP64 MUL factor-1 slot at
    `x12 + 0 .. x12 + 24`. 8 instructions, 32 bytes.

    Used by both the squaring marshal (where factor-1 = factor-2 = result)
    and the conditional-multiply marshal (where factor-1 = result and
    factor-2 = a). Pure Program definition; spec lands in the
    marshalling-spec slice (evm-asm-mtj3 / evm-asm-w5mk follow-up). -/
def exp_loop_marshal_factor1 : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 0 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 8 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 16 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 24

theorem exp_loop_marshal_factor1_length :
    exp_loop_marshal_factor1.length = 8 := by decide

theorem exp_loop_marshal_factor1_byte_length :
    4 * exp_loop_marshal_factor1.length = 32 := by
  rw [exp_loop_marshal_factor1_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-result-to-factor2,
-- beads evm-asm-z5yv)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-frame-design.md` §5 and §8 action item 2, the squaring
-- step copies the running accumulator `result` into BOTH MUL operand slots
-- on the EVM stack: factor-1 at `x12 + 0..+24` (handled by
-- `exp_loop_marshal_factor1` above) and factor-2 at `x12 + 32..+56`
-- (handled here). This block mirrors `exp_loop_marshal_factor1` line for
-- line, only with the SD offsets shifted by +32 to land in the factor-2
-- window.
--
-- Register usage:
--   x2  — sp; read-only (local scratch frame base for `result`).
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue, so writes at offsets +32 .. +56 land in the
--          factor-2 slot disjoint from the operand region.
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of `result` from the local scratch frame at
    `sp + 0 .. sp + 24` into the LP64 MUL factor-2 slot at
    `x12 + 32 .. x12 + 56`. 8 instructions, 32 bytes.

    Used by the squaring marshal where factor-1 = factor-2 = result, so
    this block runs immediately after `exp_loop_marshal_factor1` to
    populate the second operand slot before the JAL into `mul_callable`.
    Pure Program definition; spec lands in the marshalling-spec slice
    (evm-asm-mtj3 / evm-asm-w5mk follow-up). -/
def exp_loop_marshal_result_to_factor2 : Program :=
  LD .x5 .x2 0 ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x2 8 ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x2 16 ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x2 24 ;;
  SD .x12 .x5 56

theorem exp_loop_marshal_result_to_factor2_length :
    exp_loop_marshal_result_to_factor2.length = 8 := by decide

theorem exp_loop_marshal_result_to_factor2_byte_length :
    4 * exp_loop_marshal_result_to_factor2.length = 32 := by
  rw [exp_loop_marshal_result_to_factor2_length]

-- ----------------------------------------------------------------------------
-- Per-iteration marshalling helpers (#92 slice 3-marshal-a-to-factor2,
-- beads evm-asm-18wt)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-frame-design.md` §8 action item 3, the
-- conditional-multiply step copies the EVM-stack base operand `a` (held in
-- the slot `x12 + (-64) .. x12 + (-40)` — i.e. the original `a` window
-- that survives below the loop's working `x12 = x12_loop = sp_evm0 + 64`)
-- into the LP64 MUL factor-2 slot at `x12 + 32 .. x12 + 56`. This block
-- mirrors `exp_loop_marshal_factor1` / `exp_loop_marshal_result_to_factor2`
-- line for line, only with the LD source offsets shifted to negative
-- signed 12-bit immediates addressing the saved `a` window.
--
-- Register usage:
--   x12 — EVM stack pointer (a2); pointed at `x12_loop = sp_evm0 + 64`
--          by the prologue. LDs at offsets -64..-40 read the original
--          `a` operand; SDs at offsets +32..+56 write the factor-2
--          window. Both windows are disjoint from the operand region
--          (`sp_evm0 + 0 .. + 56`) at the time the `cond_mul`
--          marshalling runs.
--   x5  — t0, single-limb temporary; caller-saved per LP64 and not live
--          across the surrounding marshalling.

/-- Copy the four limbs of EVM-stack base operand `a` from
    `x12 + (-64) .. x12 + (-40)` into the LP64 MUL factor-2 slot at
    `x12 + 32 .. x12 + 56`. 8 instructions, 32 bytes.

    Used by the conditional-multiply marshalling sequence (where
    factor-1 = `result` and factor-2 = `a`); runs immediately after
    `exp_loop_marshal_factor1` to populate the second operand slot
    before the JAL into `mul_callable`. Pure Program definition; spec
    lands in the marshalling-spec slice (evm-asm-mtj3 / evm-asm-w5mk
    follow-up). -/
def exp_loop_marshal_a_to_factor2 : Program :=
  LD .x5 .x12 (-64) ;;
  SD .x12 .x5 32 ;;
  LD .x5 .x12 (-56) ;;
  SD .x12 .x5 40 ;;
  LD .x5 .x12 (-48) ;;
  SD .x12 .x5 48 ;;
  LD .x5 .x12 (-40) ;;
  SD .x12 .x5 56

theorem exp_loop_marshal_a_to_factor2_length :
    exp_loop_marshal_a_to_factor2.length = 8 := by decide

theorem exp_loop_marshal_a_to_factor2_byte_length :
    4 * exp_loop_marshal_a_to_factor2.length = 32 := by
  rw [exp_loop_marshal_a_to_factor2_length]


-- ----------------------------------------------------------------------------
-- Per-iteration un-marshalling tail (#92 slice 3-un-marshal, beads
-- evm-asm-shtuc)
-- ----------------------------------------------------------------------------
--
-- Per `docs/92-exp-frame-design.md` §5 (squaring tail), §6 (cond-mul tail),
-- and §8 action item 4: every per-iteration MUL call (both the unconditional
-- squaring and the taken branch of the conditional multiply by base `a`)
-- ends with the same 9-instruction tail. The MUL output sits at
-- `x12_loop + 32 .. x12_loop + 56`, but `mul_callable` advanced `x12` by
-- +32, so from the post-call EVM stack pointer the output is at
-- `x12 + 0 .. x12 + 24`. We copy it back into the local scratch frame at
-- `sp + 0 .. sp + 24` (so the next iteration sees `result` updated in
-- place), then `ADDI .x12 .x12 (-32)` to undo MUL's pop and restore
-- `x12 := x12_loop` for the next iteration's marshalling.
--
-- This helper is the same in both call sites (squaring and cond-mul taken
-- path), so we factor it out as a single `Program` block. Pure Program
-- definition; spec lands in the marshalling-spec slice (`evm-asm-mtj3` /
-- `evm-asm-w5mk` follow-up).
--
-- Register usage:
--   x12 — EVM stack pointer (a2); on entry points at `x12_loop + 32`
--          (MUL advanced it by +32). The four LDs at offsets +0..+24 read
--          the MUL output from that window. Final `ADDI .x12 .x12 (-32)`
--          restores `x12 := x12_loop` for the next iteration.
--   x2  — sp; read-only (local scratch frame base for `result`). The four
--          SDs at offsets +0..+24 write the new `result` limbs into the
--          local frame.
--   x5  — t0, single-limb load/store temporary; caller-saved per LP64 and
--          not live across the surrounding marshalling.

/-- Un-marshal MUL output and restore the loop EVM stack pointer.
    Copies the four limbs of MUL output from the post-call EVM-stack
    window at `x12 + 0 .. x12 + 24` (= `x12_loop + 32 .. x12_loop + 56`,
    since `mul_callable` advanced `x12` by +32) back into the local
    scratch frame at `sp + 0 .. sp + 24`, then advances `x12` by -32 to
    restore `x12 := x12_loop` for the next iteration. 9 instructions,
    36 bytes.

    Used by both the squaring tail (`evm-asm-mtj3`) and the
    conditional-multiply taken-branch tail (`evm-asm-w5mk` follow-up).
    Pure Program definition; spec lands in the marshalling-spec slice. -/
def exp_loop_un_marshal_and_restore : Program :=
  LD .x5 .x12 0 ;;
  SD .x2 .x5 0 ;;
  LD .x5 .x12 8 ;;
  SD .x2 .x5 8 ;;
  LD .x5 .x12 16 ;;
  SD .x2 .x5 16 ;;
  LD .x5 .x12 24 ;;
  SD .x2 .x5 24 ;;
  ADDI .x12 .x12 (-32)

theorem exp_loop_un_marshal_and_restore_length :
    exp_loop_un_marshal_and_restore.length = 9 := by decide

theorem exp_loop_un_marshal_and_restore_byte_length :
    4 * exp_loop_un_marshal_and_restore.length = 36 := by
  rw [exp_loop_un_marshal_and_restore_length]

-- ----------------------------------------------------------------------------
-- Per-iteration squaring call (#92 slice 3-squaring-call, beads evm-asm-ywrjr)
-- ----------------------------------------------------------------------------
--
-- Per docs/92-exp-frame-design.md §5 + §8, the per-iteration squaring step
-- composes four already-merged sub-blocks:
--
--   exp_squaring_call_block mulOff :=
--     exp_loop_marshal_factor1                ;;  -- 8 instr (32 bytes)
--     exp_loop_marshal_result_to_factor2      ;;  -- 8 instr (32 bytes)
--     exp_square_block mulOff                 ;;  -- 1 instr (4 bytes; JAL → mul)
--     exp_loop_un_marshal_and_restore             -- 9 instr (36 bytes)
--
-- Total: 26 instructions = 104 bytes.
-- Pure structural composition: marshalling specs land in the limb-level
-- slice (`evm-asm-mtj3`) and the full-loop composition in `evm-asm-w5mk`.

/-- Per-iteration squaring step: marshal factor1 + result→factor2, JAL into
    `mul_callable`, then un-marshal and restore the scratch frame. 26
    instructions. -/
def exp_squaring_call_block (mulOff : BitVec 21) : Program :=
  exp_loop_marshal_factor1 ;;
  exp_loop_marshal_result_to_factor2 ;;
  exp_square_block mulOff ;;
  exp_loop_un_marshal_and_restore

theorem exp_squaring_call_block_length (mulOff : BitVec 21) :
    (exp_squaring_call_block mulOff).length = 26 := by
  show (((exp_loop_marshal_factor1 ;;
          exp_loop_marshal_result_to_factor2) ;;
         exp_square_block mulOff) ;;
        exp_loop_un_marshal_and_restore).length = 26
  simp only [seq, Program.length_append,
    exp_loop_marshal_factor1_length,
    exp_loop_marshal_result_to_factor2_length,
    exp_square_block_length,
    exp_loop_un_marshal_and_restore_length]

theorem exp_squaring_call_block_byte_length (mulOff : BitVec 21) :
    4 * (exp_squaring_call_block mulOff).length = 104 := by
  rw [exp_squaring_call_block_length]


-- ----------------------------------------------------------------------------
-- Conditional-multiply taken-branch composite: exp_cond_mul_call_block
-- (#92 slice 3-cond-mul-call, beads evm-asm-1uu01)
-- ----------------------------------------------------------------------------
--
-- Sibling of `exp_squaring_call_block` (slice evm-asm-ywrjr). The
-- conditional-multiply taken-branch performs the same 4-block composition
-- as the squaring tail, but loads the base `a` into the `factor2` slot
-- instead of copying `result` into it. The surrounding scaffold
-- (`evm_exp`, slice evm-asm-ahaz) hoists the BEQ that skips this block
-- when the current exponent bit is zero.
--
-- Layout (26 instructions = 104 bytes):
--
--     exp_cond_mul_call_block mulOff :=
--       exp_loop_marshal_factor1 ;;            -- 8 instr (place result at f1 slot)
--       exp_loop_marshal_a_to_factor2 ;;       -- 8 instr (place base `a` at f2 slot)
--       exp_square_block mulOff ;;             -- 1 instr (JAL mul_callable)
--       exp_loop_un_marshal_and_restore        -- 9 instr (copy MUL output back; ADDI x12 -32)
--
-- The block name retains `_call` to mirror `exp_squaring_call_block`; the
-- conditional gating (BEQ skip when `x10 == 0`) is composed in by the
-- top-level `evm_exp` layout, not by this block. Pure structural
-- composition; per-iteration limb specs land in evm-asm-mtj3 and the
-- full-loop spec in evm-asm-w5mk.

/-- Conditional-multiply (taken-branch) composite for one EXP iteration:
    marshal `result` into the LP64 `factor1` slot, marshal base `a` into
    the LP64 `factor2` slot, JAL into `mul_callable`, and copy the MUL
    output back into the local scratch frame while restoring `x12` to
    its pre-call position. 26 instructions, 104 bytes.

    `mulOff` is the signed 21-bit JAL offset to `mul_callable` (shared
    with `exp_squaring_call_block` and the bare `exp_square_block`; the
    concrete numeric value is pinned once the surrounding `evm_exp`
    layout is final in slice evm-asm-ahaz). -/
def exp_cond_mul_call_block (mulOff : BitVec 21) : Program :=
  exp_loop_marshal_factor1 ;;
  exp_loop_marshal_a_to_factor2 ;;
  exp_square_block mulOff ;;
  exp_loop_un_marshal_and_restore

theorem exp_cond_mul_call_block_length (mulOff : BitVec 21) :
    (exp_cond_mul_call_block mulOff).length = 26 := by
  show (((exp_loop_marshal_factor1 ;;
            exp_loop_marshal_a_to_factor2) ;;
            exp_square_block mulOff) ;;
          exp_loop_un_marshal_and_restore).length = 26
  simp only [seq, Program.length_append,
    exp_loop_marshal_factor1_length,
    exp_loop_marshal_a_to_factor2_length,
    exp_square_block_length,
    exp_loop_un_marshal_and_restore_length]

theorem exp_cond_mul_call_block_byte_length (mulOff : BitVec 21) :
    4 * (exp_cond_mul_call_block mulOff).length = 104 := by
  rw [exp_cond_mul_call_block_length]



-- ----------------------------------------------------------------------------
-- Conditional-multiply with BEQ skip gate: exp_cond_mul_call_with_skip_block
-- (#92 slice 3-cond-mul-with-skip, beads evm-asm-qqz3m)
-- ----------------------------------------------------------------------------
--
-- Wraps `exp_cond_mul_call_block` with the leading BEQ instruction that
-- skips past the entire 26-instruction taken-branch composite when the
-- current exponent bit is zero (`x10 == 0`). Per
-- `docs/92-exp-frame-design.md` §6 and §8, the per-iteration conditional
-- multiply step has shape
--
--     BEQ x10, x0, +108                ;; skip taken branch (1 instr)
--     exp_cond_mul_call_block mulOff   ;; taken: marshal+JAL+un-marshal (26 instr)
--
-- Pure structural composition; no specs in this slice. The BEQ branch
-- offset is the byte distance from the BEQ site to the instruction
-- immediately past the taken branch — i.e. exactly the byte length of
-- `exp_cond_mul_call_block` (= 104 bytes / 26 instr). Callers must pin
-- `skipOff` accordingly when they assemble the surrounding `evm_exp`
-- layout in slice evm-asm-ahaz.

/-- Conditional-multiply step with BEQ skip gate: `BEQ x10, x0, skipOff`
    followed by the 26-instruction taken-branch composite
    `exp_cond_mul_call_block mulOff`. 27 instructions, 108 bytes. -/
def exp_cond_mul_call_with_skip_block
    (mulOff : BitVec 21) (skipOff : BitVec 13) : Program :=
  single (.BEQ .x10 .x0 skipOff) ;;
  exp_cond_mul_call_block mulOff

theorem exp_cond_mul_call_with_skip_block_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    (exp_cond_mul_call_with_skip_block mulOff skipOff).length = 27 := by
  show (single (.BEQ .x10 .x0 skipOff) ;;
        exp_cond_mul_call_block mulOff).length = 27
  simp only [seq, Program.length_append, exp_cond_mul_call_block_length]
  rfl

theorem exp_cond_mul_call_with_skip_block_byte_length
    (mulOff : BitVec 21) (skipOff : BitVec 13) :
    4 * (exp_cond_mul_call_with_skip_block mulOff skipOff).length = 108 := by
  rw [exp_cond_mul_call_with_skip_block_length]



-- Placeholder: `evm_exp : Program` lands in slice 3 (evm-asm-ahaz).
-- See `docs/92-exp-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
