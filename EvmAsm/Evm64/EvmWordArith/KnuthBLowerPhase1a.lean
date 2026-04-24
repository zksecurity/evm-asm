/-
  EvmAsm.Evm64.EvmWordArith.KnuthBLowerPhase1a

  First piece of Knuth Theorem B **LOWER direction**: Phase 1a quotient
  lower bound `q1 ≥ q_true_1`.

  This is the first of ~4 pieces needed to prove `n4CallSkipSemanticHolds`
  from first principles (the "deep math" blocker on PR #1154). Each piece
  is a focused lemma; together they give `(div128Quot u4 u3 b3').toNat ≥
  val256(a_norm) / val256(b_norm)`, which with the normalization bridge
  yields `val256(a) / val256(b) ≤ (div128Quot u4 u3 b3').toNat`.

  This file: the abstract Nat-level bound + its Word-level wrapper at
  Phase 1a (after hi1-correction).
-/

import EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Abstract Knuth-B lower (Phase 1a level)**: when the divisor's high limb
    is normalized (dHi ≥ 2^31, dHi < 2^32) and the low parts are small
    (dLo < 2^32, div_un1 < 2^32), the true quotient of the "full" 96/64
    division is at most the "partial" 64/32 quotient:

    ```
    (uHi*2^32 + div_un1) / (dHi*2^32 + dLo) ≤ uHi/dHi
    ```

    Proof idea: let vTop := dHi*2^32 + dLo and q_true := (uHi*2^32 + div_un1)/vTop.
    Then q_true * vTop ≤ uHi*2^32 + div_un1 (floor def). Since q_true * dLo ≥ 0,
    q_true * dHi * 2^32 ≤ uHi*2^32 + div_un1. Dividing by 2^32:
    q_true * dHi ≤ (uHi*2^32 + div_un1) / 2^32 = uHi (since div_un1 < 2^32).
    Hence q_true ≤ uHi/dHi.

    This is the arithmetic core of Phase 1a's lower bound. -/
theorem knuth_b_lower_q_true_1_le_uHi_div_dHi_abstract
    (uHi dHi dLo div_un1 : Nat)
    (hdHi_pos : 0 < dHi) (h_div_un1_lt : div_un1 < 2^32) :
    (uHi * 2^32 + div_un1) / (dHi * 2^32 + dLo) ≤ uHi / dHi := by
  set vTop := dHi * 2^32 + dLo with hvTop_def
  have h_pow_pos : (0 : Nat) < 2^32 := by positivity
  have h_dHi_pow_pos : 0 < dHi * 2^32 := Nat.mul_pos hdHi_pos h_pow_pos
  have hvTop_pos : 0 < vTop := Nat.lt_of_lt_of_le h_dHi_pow_pos (Nat.le_add_right _ _)
  set q_true := (uHi * 2^32 + div_un1) / vTop with hq_true_def
  -- Step 1: q_true * vTop ≤ uHi * 2^32 + div_un1 (floor property).
  have h_floor : q_true * vTop ≤ uHi * 2^32 + div_un1 := Nat.div_mul_le_self _ _
  -- Step 2: q_true * dHi * 2^32 ≤ q_true * vTop ≤ uHi*2^32 + div_un1.
  have h_dHi_le : q_true * dHi * 2^32 ≤ q_true * vTop := by
    rw [hvTop_def]
    nlinarith
  have h_chain : q_true * dHi * 2^32 ≤ uHi * 2^32 + div_un1 := h_dHi_le.trans h_floor
  -- Step 3: q_true * dHi ≤ uHi. Derived directly from h_chain via nlinarith.
  have h_qTrue_dHi : q_true * dHi ≤ uHi := by
    -- h_chain: q_true * dHi * 2^32 ≤ uHi * 2^32 + div_un1 < (uHi + 1) * 2^32.
    -- Hence q_true * dHi < uHi + 1, i.e., q_true * dHi ≤ uHi.
    have h_pow : (2 : Nat) ^ 32 > 0 := by positivity
    nlinarith
  -- Step 5: q_true ≤ uHi / dHi.
  exact (Nat.le_div_iff_mul_le hdHi_pos).mpr h_qTrue_dHi

/-- **Phase 1a Word-level lower bound**: after Phase 1a's hi1-correction,
    `q1c.toNat ≥ q_true_1`.

    Composes `knuth_b_lower_q_true_1_le_uHi_div_dHi_abstract` (giving
    `q_true_1 ≤ uHi/dHi`) with `div128Quot_phase1a_quotient_bound` (giving
    `uHi/dHi ≤ q1c.toNat + 1`) into... hmm wait, that gives us an upper
    bound on q_true_1 in terms of q1c.toNat + 1, which doesn't directly
    give `q1c.toNat ≥ q_true_1`.

    The right composition: KB-1 gives `q1c.toNat ≤ uHi/dHi` (UPPER). Combined
    with `q_true_1 ≤ uHi/dHi`, we have BOTH q1c AND q_true_1 ≤ uHi/dHi, but
    no direct ordering between them.

    Wait, we need q1c ≥ q_true_1 (LOWER on q1c). From KB-1 we have
    `uHi/dHi ≤ q1c.toNat + 1`, i.e., `q1c.toNat ≥ uHi/dHi - 1`. Combined
    with `q_true_1 ≤ uHi/dHi`, we get `q1c.toNat ≥ q_true_1 - 1`. Off by 1!

    Reason: Phase 1a's hi1-correction decrements when q1 ≥ 2^32, reducing
    q1c to q1 - 1. But in the critical case (q1 = 2^32, q_true_1 < 2^32),
    q1c = 2^32 - 1 which is still ≥ q_true_1.

    The full Phase 1a lower bound needs a case analysis on whether the
    hi1-correction fires. Deferred to follow-up piece. -/
theorem div128Quot_phase1a_q1c_ge_q_true_1_minus_one
    (uHi dHi dLo div_un1 : Word)
    (hdHi_ne : dHi ≠ 0) (hdHi_lt : dHi.toNat < 2^32)
    (h_div_un1_lt : div_un1.toNat < 2^32) :
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat + 1 ≥ (uHi.toNat * 2^32 + div_un1.toNat) /
                     (dHi.toNat * 2^32 + dLo.toNat) := by
  intro q1 hi1 q1c
  have hdHi_pos : 0 < dHi.toNat :=
    Nat.pos_of_ne_zero (fun h => hdHi_ne (BitVec.eq_of_toNat_eq h))
  have h_q_true_le_div := knuth_b_lower_q_true_1_le_uHi_div_dHi_abstract
    uHi.toNat dHi.toNat dLo.toNat div_un1.toNat hdHi_pos h_div_un1_lt
  have h_kb1 := div128Quot_phase1a_quotient_bound uHi dHi hdHi_ne hdHi_lt
  have h_div_le_q1c_plus_one : uHi.toNat / dHi.toNat ≤ q1c.toNat + 1 := h_kb1.2
  omega

end EvmAsm.Evm64
