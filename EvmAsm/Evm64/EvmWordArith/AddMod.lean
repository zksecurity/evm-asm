/-
  EvmAsm.Evm64.EvmWordArith.AddMod

  EVM ADDMOD semantics: word-level definition and correctness theorem.

  Provides:
  * `EvmWord.addmod a b N` — the EVM `ADDMOD` operation: `(a + b) mod N`
    with `N = 0 ⇒ 0`, where the intermediate sum `a + b` is taken at
    full 257-bit precision (carry out of bit 255).
  * `EvmWord.addCarry a b` — the 257-bit add helper: returns the
    Boolean carry-out alongside the truncated 256-bit sum, with a
    proof that the pair faithfully represents the natural-number sum
    `a.toNat + b.toNat`.
  * `EvmWord.addmod_correct` — algebraic correctness:
    `(addmod a b N).toNat = if N = 0 then 0 else (a.toNat + b.toNat) % N.toNat`.

  This is the slice-2 deliverable for GH issue #91 (ADDMOD/MULMOD)
  and matches the algebraic shape required by the future
  `evm_addmod_stack_spec` (slice 3, beads `evm-asm-sord`).

  See `docs/91-addmod-mulmod-survey.md` §1.3, §3, §4 for context.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace EvmWord

-- ============================================================================
-- 257-bit add helper
-- ============================================================================

/-- Pair of (carry-out, truncated 256-bit sum) for the addition of two
    `EvmWord`s. The carry bit is `true` exactly when `a.toNat + b.toNat`
    overflows 256 bits, i.e. equals `2^256` or more. -/
def addCarry (a b : EvmWord) : Bool × EvmWord :=
  (decide (a.toNat + b.toNat ≥ 2 ^ 256), a + b)

/-- The 257-bit identity for `addCarry`: the natural-number sum of the
    inputs is exactly `(carry · 2^256) + truncated`. This is the
    algebraic shape downstream proofs use to bridge the limb-level
    RISC-V add-with-carry to the EVM word-level model. -/
theorem addCarry_spec (a b : EvmWord) :
    a.toNat + b.toNat =
      (if (addCarry a b).fst then 2 ^ 256 else 0) + (addCarry a b).snd.toNat := by
  unfold addCarry
  simp only [BitVec.toNat_add]
  have ha : a.toNat < 2 ^ 256 := a.isLt
  have hb : b.toNat < 2 ^ 256 := b.isLt
  by_cases h : a.toNat + b.toNat ≥ 2 ^ 256
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    have hmod : (a.toNat + b.toNat) % 2 ^ 256 = a.toNat + b.toNat - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]; omega
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    have hlt : a.toNat + b.toNat < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

-- ============================================================================
-- ADDMOD
-- ============================================================================

/-- EVM `ADDMOD` semantics: `(a + b) mod N` evaluated at full 257-bit
    precision when `N ≠ 0`; returns `0` when `N = 0`. -/
def addmod (a b N : EvmWord) : EvmWord :=
  if N = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)

/-- Algebraic correctness of `EvmWord.addmod`. -/
theorem addmod_correct (a b N : EvmWord) :
    (EvmWord.addmod a b N).toNat =
      if N = 0 then 0 else (a.toNat + b.toNat) % N.toNat := by
  unfold addmod
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
    have hlt : (a.toNat + b.toNat) % N.toNat < 2 ^ 256 := by
      have hN : N.toNat < 2 ^ 256 := N.isLt
      have : (a.toNat + b.toNat) % N.toNat < N.toNat := Nat.mod_lt _ hNpos
      omega
    exact Nat.mod_eq_of_lt hlt

-- ============================================================================
-- modAdd: pre-reduced ADDMOD helper
-- ============================================================================
--
-- A specialized variant of `addmod` that assumes both operands are already
-- reduced modulo `N`, i.e. `a.toNat < N.toNat` and `b.toNat < N.toNat`. Under
-- this precondition `a.toNat + b.toNat < 2 * N.toNat`, so the modular sum
-- equals either the sum itself or the sum minus `N` (a single conditional
-- subtraction). This shape models what the RISC-V `ADDMOD` program emits at
-- the limb level — a 257-bit add followed by a conditional subtract — without
-- the full division step that `addmod` would otherwise need to model.
--
-- The bridge lemma `modAdd_correct` lets downstream Programs (notably
-- `evm_addmod`, beads `evm-asm-sord`) reason about the post-condition
-- `(a + b) mod N` without re-deriving the bound from `addmod_correct` plus
-- the operand-bound side-conditions. Refs GH #91, beads `evm-asm-539jk`.

/-- Pre-reduced ADDMOD: `(a + b) mod N` assuming `a, b < N`. Distinct from
    `addmod` in that the precondition rules out the `N = 0` branch, so the
    result coincides with `BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)`
    unconditionally. -/
def modAdd (a b N : EvmWord) : EvmWord :=
  BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)

/-- Algebraic correctness of `EvmWord.modAdd` under the pre-reduced
    precondition `a, b < N`: the `BitVec` truncation is a no-op because
    `(a + b) mod N < N ≤ 2^256`. -/
theorem modAdd_correct (a b N : EvmWord)
    (ha : a.toNat < N.toNat) (_hb : b.toNat < N.toNat) :
    (EvmWord.modAdd a b N).toNat = (a.toNat + b.toNat) % N.toNat := by
  unfold modAdd
  rw [BitVec.toNat_ofNat]
  -- The precondition forces `N.toNat > 0` (since `a.toNat < N.toNat` with
  -- `a.toNat ≥ 0` implies `N.toNat ≥ 1`), so the mod result is `< N.toNat`,
  -- hence `< 2^256`, hence already in range.
  have hNpos : 0 < N.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have hN : N.toNat < 2 ^ 256 := N.isLt
  have hlt : (a.toNat + b.toNat) % N.toNat < 2 ^ 256 := by
    have : (a.toNat + b.toNat) % N.toNat < N.toNat := Nat.mod_lt _ hNpos
    omega
  exact Nat.mod_eq_of_lt hlt

/-- `modAdd` agrees with the unconstrained `addmod` whenever `N ≠ 0`: both
    return `BitVec.ofNat 256 ((a.toNat + b.toNat) % N.toNat)`. This makes
    `modAdd` a drop-in replacement at call sites that already discharge the
    pre-reduction bounds, while keeping `addmod` available for the unguarded
    EVM semantics. -/
theorem modAdd_eq_addmod_of_ne_zero (a b N : EvmWord) (h : N ≠ 0) :
    EvmWord.modAdd a b N = EvmWord.addmod a b N := by
  unfold modAdd addmod
  rw [if_neg h]

end EvmWord

end EvmAsm.Evm64
