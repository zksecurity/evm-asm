/-
  EvmAsm.Evm64.DivMod.Spec.N1QuotientWord

  Semantic quotient-word bridge for the n=1 DIV path.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.EvmWordArith.DivAccumulate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- Semantic bridge for the n=1 quotient word once the loop proof supplies the
    accumulated mulsub equation and quotient-overestimate bound. -/
theorem fullDivN1QuotientWord_eq_div_of_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q2 := (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q3 := (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n1_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [q0, q1, q2, q3, r0, r1, r2, r3] using hmulsub)
    (by simpa [q0, q1, q2, q3] using hge)
  delta fullDivN1QuotientWord
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1

end EvmAsm.Evm64
