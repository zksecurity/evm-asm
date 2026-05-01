/-
  EvmAsm.Evm64.Multiply.Layout

  Pilot for #334 (slice 3, beads evm-asm-1d1o): the
  `MultiplyScratchpadLayout` struct, its `Valid` bundle, the canonical
  instance matching today's hardcoded `sp`-relative offsets, and a
  decide-discharged validity proof.

  Per `docs/scratchpad-layout-design.md` §3.2: Multiply is the layout
  pilot precisely *because* it does not currently rely on
  `signExtend12 N` literals — its scratch is the eight 8-byte cells
  reached as `sp + 0`, `sp + 8`, …, `sp + 56` (operand-stack window
  `a` at `sp..sp+24`, operand `b` at `sp+32..sp+56`). This file
  introduces the abstraction shape without touching any existing
  proof, so the migration cost is zero and the pilot can be reviewed
  independently of the much larger DivMod layout migration in slice 4.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Layout of the EVM `MUL` scratchpad.

    All fields are byte offsets from a layout-supplied base register
    (today always `sp`). Eight 8-byte cells, naming the four limbs of
    operand `a` (`a0..a3`, low-to-high in memory) and the four limbs
    of operand `b` (`b0..b3`). The canonical instance (below) places
    them contiguously at `0, 8, …, 56`, matching today's hardcoded
    `sp + N` literals in `Multiply/LimbSpec.lean`.

    The struct is intentionally `BitVec 12`-typed so that a future
    `signExtend12`-folded form coexists with the natural-number
    layout the Multiply spec uses today; both encode the same
    address arithmetic. -/
structure MultiplyScratchpadLayout where
  /-- `a[0]` cell — operand `a` low limb. Canonical: `0`. -/
  a0Off : BitVec 12
  /-- `a[1]` cell. Canonical: `8`. -/
  a1Off : BitVec 12
  /-- `a[2]` cell. Canonical: `16`. -/
  a2Off : BitVec 12
  /-- `a[3]` cell — operand `a` high limb. Canonical: `24`. -/
  a3Off : BitVec 12
  /-- `b[0]` cell — operand `b` low limb. Canonical: `32`. -/
  b0Off : BitVec 12
  /-- `b[1]` cell. Canonical: `40`. -/
  b1Off : BitVec 12
  /-- `b[2]` cell. Canonical: `48`. -/
  b2Off : BitVec 12
  /-- `b[3]` cell — operand `b` high limb. Canonical: `56`. -/
  b3Off : BitVec 12
  deriving DecidableEq, Repr

namespace MultiplyScratchpadLayout

/-- Layout obligations: each cell is 8-aligned, the four `a`-limbs
    are contiguous, the four `b`-limbs are contiguous, and the `b`
    block sits exactly 32 bytes above the `a` block (so the EVM stack
    pop-and-overwrite convention used by `evm_mul` continues to hold).

    Discharged for the canonical instance by `decide`. -/
structure Valid (L : MultiplyScratchpadLayout) : Prop where
  align_a0 : (L.a0Off &&& 7#12) = 0#12
  align_a1 : (L.a1Off &&& 7#12) = 0#12
  align_a2 : (L.a2Off &&& 7#12) = 0#12
  align_a3 : (L.a3Off &&& 7#12) = 0#12
  align_b0 : (L.b0Off &&& 7#12) = 0#12
  align_b1 : (L.b1Off &&& 7#12) = 0#12
  align_b2 : (L.b2Off &&& 7#12) = 0#12
  align_b3 : (L.b3Off &&& 7#12) = 0#12
  -- Contiguity of the four `a` limbs.
  a1_eq : L.a1Off = L.a0Off + 8#12
  a2_eq : L.a2Off = L.a0Off + 16#12
  a3_eq : L.a3Off = L.a0Off + 24#12
  -- Contiguity of the four `b` limbs.
  b1_eq : L.b1Off = L.b0Off + 8#12
  b2_eq : L.b2Off = L.b0Off + 16#12
  b3_eq : L.b3Off = L.b0Off + 24#12
  -- `b` window starts 32 bytes above `a` window — the operand-stack
  -- gap that `evm_mul` overwrites with the 256-bit product.
  b0_eq : L.b0Off = L.a0Off + 32#12

end MultiplyScratchpadLayout

/-- Canonical Multiply scratchpad: contiguous 8-byte cells at offsets
    `0, 8, …, 56` from `sp`. This matches the hardcoded literals in
    `Multiply/LimbSpec.lean`; if/when a downstream caller wants to
    relocate the scratchpad, they can supply a different
    `MultiplyScratchpadLayout` and prove its `Valid` bundle instead
    of re-proving Multiply itself. -/
def canonicalMultiplyScratchpadLayout : MultiplyScratchpadLayout where
  a0Off := 0#12
  a1Off := 8#12
  a2Off := 16#12
  a3Off := 24#12
  b0Off := 32#12
  b1Off := 40#12
  b2Off := 48#12
  b3Off := 56#12

/-- The canonical layout discharges every obligation in
    `MultiplyScratchpadLayout.Valid` by `decide` — both the alignment
    side-conditions and the contiguity / `b = a + 32` algebraic
    identities are concrete `BitVec 12` equalities. -/
theorem canonicalMultiplyScratchpadLayout_valid :
    canonicalMultiplyScratchpadLayout.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end EvmAsm.Evm64
