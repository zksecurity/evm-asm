/-
  EvmAsm.Evm64.DivMod.Spec.N3QuotientWord

  Quotient-word helper for the n=3 DIV path. Mirrors `Spec.N2QuotientWord`
  for n=3: packages the two non-zero per-limb results from
  `fullDivN3R{0,1}` (with `q2 = q3 = 0` because n=3 means `b3 = 0 ∧ b2 ≠ 0`,
  so `a / b < 2^128`) into a single `EvmWord`, and provides the standard
  structural lemmas (per-limb extraction, `BitVec.eq_of_toNat_eq` bridge,
  `toNat`-as-`val256`, and a `val256`-equality bridge to `EvmWord.div`).

  Consumed by `evm_div_n3_stack_spec_within_word` (mirror of
  `evm_div_n2_stack_spec_within_word`).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-pwvj`, parent `evm-asm-pb40` (#61).
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Pack the four per-limb DIV results from the n=3 path into a single
    `EvmWord`. The top two limbs are `0` because n=3 means `b3 = 0` with
    `b2 ≠ 0`, so the quotient cannot exceed 128 bits. -/
@[irreducible]
def fullDivN3QuotientWord (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (0 : Word)
    | 3 => (0 : Word))

/-- If `fullDivN3QuotientWord ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding `fullDivN3R{0,1}` result
    (and limbs 2, 3 are zero). -/
theorem fullDivN3_hdivs_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN3QuotientWord
    exact EvmWord.getLimbN_fromLimbs_3

/-- BitVec extensionality bridge: a `toNat` equality lifts to an `EvmWord`
    equality. -/
theorem fullDivN3QuotientWord_eq_div_of_toNat_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv_toNat :
      (fullDivN3QuotientWord bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.div a b).toNat) :
    fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b :=
  BitVec.eq_of_toNat_eq hdiv_toNat

/-- The `toNat` of the packed quotient word equals the four-limb
    `EvmWord.val256` of the per-limb results (with top two limbs zero). -/
theorem fullDivN3QuotientWord_toNat
    (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
      (0 : Word) (0 : Word) := by
  delta fullDivN3QuotientWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

/-- `val256`-equality bridge: if the `EvmWord.val256` of the four per-limb
    results equals `a.toNat / b.toNat` (computed via `EvmWord.val256` of the
    inputs), then the `toNat` of the quotient word equals
    `(EvmWord.div a b).toNat`. Mirrors
    `fullDivN2QuotientWord_toNat_eq_div_toNat_of_val256_eq`. -/
theorem fullDivN3QuotientWord_toNat_eq_div_toNat_of_val256_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hquot :
      EvmWord.val256
        (fullDivN3R0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word) (0 : Word) =
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3) :
    (fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat = (EvmWord.div a b).toNat := by
  have ha_val : EvmWord.val256 a0 a1 a2 a3 = a.toNat := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : EvmWord.val256 b0 b1 b2 b3 = b.toNat := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    simp only [← EvmWord.getLimb_as_getLimbN_0,
      ← EvmWord.getLimb_as_getLimbN_1,
      ← EvmWord.getLimb_as_getLimbN_2,
      ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rw [← hb_val]
    exact EvmWord.val256_pos_of_or_ne_zero hbnz
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    have hb_toNat_zero : b.toNat = 0 := by simp [hb_zero]
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hb_ne]
    exact BitVec.toNat_udiv
  rw [fullDivN3QuotientWord_toNat, hquot, ha_val, hb_val, hdiv_toNat]

end EvmAsm.Evm64
