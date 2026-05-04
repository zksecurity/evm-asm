/-
  EvmAsm.Evm64.EvmWordArith.MulHigh

  High 256 bits of the 512-bit product `a * b` of two `EvmWord`s.

  Provides:
  * `EvmWord.mulHigh a b` — the upper 256 bits of `a.toNat * b.toNat`
    encoded back as an `EvmWord`.
  * `EvmWord.mulHigh_correct` — algebraic correctness:
    `(mulHigh a b).toNat = (a.toNat * b.toNat) / 2 ^ 256`.

  Slice 4a deliverable for GH issue #91 (ADDMOD/MULMOD), beads
  `evm-asm-8qht`. Together with the existing `EvmWord.mul` (low 256
  bits, see `Multiply/Spec.lean` and `MulCorrect.lean`) this exposes
  the complete 512-bit schoolbook product needed by `MULMOD`'s
  `evm_mulmod_stack_spec` (slice 5, `evm-asm-m4wu`) which divides the
  full product by `N` modulo `2 ^ 256`.

  This file is purely algebraic — no RISC-V state, no separation
  logic — mirroring the structure of `AddMod.lean` and `MulMod.lean`.

  See `docs/91-addmod-mulmod-survey.md` §3 for context.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace EvmWord

-- ============================================================================
-- mulHigh
-- ============================================================================

/-- Upper 256 bits of the 512-bit product `a * b`, encoded as an `EvmWord`.
    Defined directly on `Nat` and then re-encoded; the bridge to limb-level
    schoolbook multiplication lives in the runtime side (slice 5). -/
def mulHigh (a b : EvmWord) : EvmWord :=
  BitVec.ofNat 256 ((a.toNat * b.toNat) / 2 ^ 256)

/-- Algebraic correctness of `EvmWord.mulHigh`:
    the encoded high 256 bits agree with `Nat`-level division by `2 ^ 256`. -/
theorem mulHigh_correct (a b : EvmWord) :
    (EvmWord.mulHigh a b).toNat = (a.toNat * b.toNat) / 2 ^ 256 := by
  unfold mulHigh
  rw [BitVec.toNat_ofNat]
  -- The quotient `(a.toNat * b.toNat) / 2 ^ 256` is bounded by
  -- `(2^256 - 1) * (2^256 - 1) / 2^256 < 2 ^ 256`, so no further
  -- reduction modulo `2 ^ 256` is needed.
  have hA : a.toNat < 2 ^ 256 := a.isLt
  have hB : b.toNat < 2 ^ 256 := b.isLt
  have h2 : (0 : Nat) < 2 ^ 256 := Nat.two_pow_pos 256
  have hProd : a.toNat * b.toNat < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul_of_lt_of_le hA (Nat.le_of_lt hB) h2
  have hLt : (a.toNat * b.toNat) / 2 ^ 256 < 2 ^ 256 :=
    (Nat.div_lt_iff_lt_mul h2).mpr hProd
  exact Nat.mod_eq_of_lt hLt

end EvmWord

end EvmAsm.Evm64
