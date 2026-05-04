/-
  EvmAsm.Evm64.EvmWordArith.MulMod

  EVM MULMOD semantics: word-level definition and correctness theorem.

  Provides:
  * `EvmWord.mulmod a b N` — the EVM `MULMOD` operation: `(a * b) mod N`
    with `N = 0 ⇒ 0`, where the intermediate product `a * b` is taken at
    full 512-bit precision.
  * `EvmWord.mulmod_correct` — algebraic correctness:
    `(mulmod a b N).toNat = if N = 0 then 0 else (a.toNat * b.toNat) % N.toNat`.

  This is the slice-3a deliverable for GH issue #91 (ADDMOD/MULMOD)
  and mirrors `EvmWord.addmod` / `EvmWord.addmod_correct` in
  `EvmAsm/Evm64/EvmWordArith/AddMod.lean`. The future
  `evm_mulmod_stack_spec` (slice 5, beads `evm-asm-m4wu`) will bridge
  to this algebraic shape via the 512-bit schoolbook product handled by
  slice 4 (`evm-asm-lxq4`).

  See `docs/91-addmod-mulmod-survey.md` §1.3, §3, §4 for context.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace EvmWord

-- ============================================================================
-- MULMOD
-- ============================================================================

/-- EVM `MULMOD` semantics: `(a * b) mod N` evaluated at full 512-bit
    precision when `N ≠ 0`; returns `0` when `N = 0`. -/
def mulmod (a b N : EvmWord) : EvmWord :=
  if N = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % N.toNat)

/-- Algebraic correctness of `EvmWord.mulmod`. -/
theorem mulmod_correct (a b N : EvmWord) :
    (EvmWord.mulmod a b N).toNat =
      if N = 0 then 0 else (a.toNat * b.toNat) % N.toNat := by
  unfold mulmod
  by_cases h : N = 0
  · simp [h]
  · simp only [if_neg h]
    rw [BitVec.toNat_ofNat]
    -- The mod result is < N.toNat ≤ 2^256 - 1 < 2^256, so no further
    -- reduction modulo 2^256 is needed.
    have hNpos : 0 < N.toNat := by
      have hne : N.toNat ≠ 0 := by
        intro hz
        apply h
        exact BitVec.eq_of_toNat_eq (by simpa using hz)
      omega
    have hlt : (a.toNat * b.toNat) % N.toNat < 2 ^ 256 := by
      have hN : N.toNat < 2 ^ 256 := N.isLt
      have : (a.toNat * b.toNat) % N.toNat < N.toNat := Nat.mod_lt _ hNpos
      omega
    exact Nat.mod_eq_of_lt hlt

end EvmWord

end EvmAsm.Evm64
