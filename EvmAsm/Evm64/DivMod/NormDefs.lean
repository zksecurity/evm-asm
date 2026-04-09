/-
  EvmAsm.Evm64.DivMod.NormDefs

  Standalone definitions for the normalization/denormalization computations
  in Knuth Algorithm D. These replace let-chains in theorem type signatures,
  making specs easier to compose and use downstream.

  Normalization: left-shift a[] and b[] by the CLZ of the leading divisor limb.
  Denormalization: right-shift the remainder back after division.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Normalization: shift b[] and a[] left by `shift` bits
-- ============================================================================

/-- Normalize a non-leading limb by shifting left and OR-ing in bits from the
    lower-adjacent limb. Used for b[1], b[2], b[3] and u[1], u[2], u[3]. -/
def normLimb (prev cur shift anti_shift : Word) : Word :=
  (cur <<< (shift.toNat % 64)) ||| (prev >>> (anti_shift.toNat % 64))

/-- Normalize the lowest limb (no lower neighbor to OR in). -/
def normLimb_lo (lo shift : Word) : Word :=
  lo <<< (shift.toNat % 64)

/-- Compute the carry limb above the top a[] limb after normalization. -/
def normLimb_top (hi anti_shift : Word) : Word :=
  hi >>> (anti_shift.toNat % 64)

/-- Bundle: normalize all 4 b-limbs.
    Returns (b0', b1', b2', b3') where b[] is left-shifted by `shift`. -/
def normBLimbs (b0 b1 b2 b3 shift anti_shift : Word) :
    Word × Word × Word × Word :=
  ( normLimb_lo b0 shift,
    normLimb b0 b1 shift anti_shift,
    normLimb b1 b2 shift anti_shift,
    normLimb b2 b3 shift anti_shift )

/-- Bundle: normalize all 4 a-limbs plus carry.
    Returns (u0, u1, u2, u3, u4) where a[] is left-shifted by `shift`
    and u4 is the overflow carry. -/
def normULimbs (a0 a1 a2 a3 shift anti_shift : Word) :
    Word × Word × Word × Word × Word :=
  ( normLimb_lo a0 shift,
    normLimb a0 a1 shift anti_shift,
    normLimb a1 a2 shift anti_shift,
    normLimb a2 a3 shift anti_shift,
    normLimb_top a3 anti_shift )

-- ============================================================================
-- Denormalization: shift remainder u[] right by `shift` bits
-- ============================================================================

/-- Denormalize a non-top remainder limb by shifting right and OR-ing in
    bits from the higher-adjacent limb. -/
def denormLimb (cur next shift anti_shift : Word) : Word :=
  (cur >>> (shift.toNat % 64)) ||| (next <<< (anti_shift.toNat % 64))

/-- Denormalize the top remainder limb (no higher neighbor). -/
def denormLimb_top (hi shift : Word) : Word :=
  hi >>> (shift.toNat % 64)

/-- Bundle: denormalize 4 remainder limbs.
    Returns (r0', r1', r2', r3') where u[] is right-shifted by `shift`. -/
def denormRLimbs (u0 u1 u2 u3 shift anti_shift : Word) :
    Word × Word × Word × Word :=
  ( denormLimb u0 u1 shift anti_shift,
    denormLimb u1 u2 shift anti_shift,
    denormLimb u2 u3 shift anti_shift,
    denormLimb_top u3 shift )

end EvmAsm.Evm64
