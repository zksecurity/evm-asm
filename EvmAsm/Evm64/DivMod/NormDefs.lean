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
def normLimb (prev cur shift antiShift : Word) : Word :=
  (cur <<< (shift.toNat % 64)) ||| (prev >>> (antiShift.toNat % 64))

/-- Normalize the lowest limb (no lower neighbor to OR in). -/
def normLimb_lo (lo shift : Word) : Word :=
  lo <<< (shift.toNat % 64)

/-- Compute the carry limb above the top a[] limb after normalization. -/
def normLimb_top (hi antiShift : Word) : Word :=
  hi >>> (antiShift.toNat % 64)

-- ============================================================================
-- Denormalization: shift remainder u[] right by `shift` bits
-- ============================================================================

/-- Denormalize a non-top remainder limb by shifting right and OR-ing in
    bits from the higher-adjacent limb. -/
def denormLimb (cur next shift antiShift : Word) : Word :=
  (cur >>> (shift.toNat % 64)) ||| (next <<< (antiShift.toNat % 64))

/-- Denormalize the top remainder limb (no higher neighbor). -/
def denormLimb_top (hi shift : Word) : Word :=
  hi >>> (shift.toNat % 64)

end EvmAsm.Evm64
