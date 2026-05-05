/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1ConservationV4

  v4 trial-quotient helpers for the n=1 full path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation
import EvmAsm.Evm64.DivMod.Spec.V4
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Saturated local quotient digit for an n=1 step.

If the high word is below the divisor top word, this is the exact 128/64
floor. Otherwise the hardware path uses the max trial digit `2^64 - 1`. -/
@[irreducible]
def n1LocalFloorDigit (v0 u0 uTop : Word) : Nat :=
  if BitVec.ult uTop v0 then
    (uTop.toNat * 2^64 + u0.toNat) / v0.toNat
  else
    2^64 - 1

@[irreducible]
def iterN1Call_v4 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  iterWithDoubleAddback (div128Quot_v4 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

/-- v4 per-iteration computation for n=1. The max path is unchanged; the call
    path uses the fully corrected `div128Quot_v4`. -/
def iterN1_v4 (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Word × Word × Word × Word × Word × Word :=
  if bltu then iterN1Call_v4 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  else iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop

@[simp]
theorem iterN1_v4_true {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1_v4 true v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Call_v4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1_v4]

@[simp]
theorem iterN1_v4_false {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    iterN1_v4 false v0 v1 v2 v3 u0 u1 u2 u3 uTop =
    iterN1Max v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp [iterN1_v4]

theorem iterN1_v4_qout_ge_trial_sub_two
    (bltu : Bool) (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    let qHat : Word := if bltu then div128Quot_v4 u1 u0 v0 else signExtend12 4095
    let out := iterN1_v4 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop
    qHat.toNat - 2 ≤ out.1.toNat := by
  intro qHat out
  subst qHat
  subst out
  cases bltu
  · simp only [iterN1_v4_false]
    unfold iterN1Max
    exact iterWithDoubleAddback_qout_ge_sub_two
      (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3 uTop (by
        rw [signExtend12_4095_toNat]
        norm_num)
  · simp only [ite_true, iterN1_v4_true]
    unfold iterN1Call_v4
    exact iterWithDoubleAddback_qout_ge_tsub_two
      (div128Quot_v4 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop

theorem mulsubN4_c3_eq_zero_of_qv0_le_low
    (q v0 u0 u1 u2 u3 : Word)
    (hle : q.toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat) :
    (mulsubN4 q v0 0 0 0 u0 u1 u2 u3).2.2.2.2 = 0 := by
  by_contra hc3_ne
  have hc3_one := mulsubN4_c3_eq_one_v3_zero q v0 0 0 u0 u1 u2 u3 hc3_ne
  have hmul := mulsubN4_val256_eq q v0 0 0 0 u0 u1 u2 u3
  let ms := mulsubN4 q v0 0 0 0 u0 u1 u2 u3
  have hbound : EvmWord.val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 < 2^256 :=
    EvmWord.val256_bound ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
  have hlow_le : u1.toNat * 2^64 + u0.toNat ≤ EvmWord.val256 u0 u1 u2 u3 := by
    unfold EvmWord.val256
    nlinarith [u2.isLt, u3.isLt]
  have hmul' : EvmWord.val256 u0 u1 u2 u3 + 2^256 =
      EvmWord.val256 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 + q.toNat * v0.toNat := by
    subst ms
    simp only [] at hmul
    rw [hc3_one] at hmul
    unfold EvmWord.val256 at hmul ⊢
    norm_num at hmul ⊢
    exact hmul
  have hval_lt_qv0 : EvmWord.val256 u0 u1 u2 u3 < q.toNat * v0.toNat := by
    nlinarith [hbound, hmul']
  have : q.toNat * v0.toNat ≤ EvmWord.val256 u0 u1 u2 u3 := le_trans hle hlow_le
  omega

theorem iterWithDoubleAddback_qout_eq_q_of_qv0_le_low
    (q v0 u0 u1 u2 u3 uTop : Word)
    (hle : q.toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat) :
    (iterWithDoubleAddback q v0 0 0 0 u0 u1 u2 u3 uTop).1 = q := by
  have hc3 := mulsubN4_c3_eq_zero_of_qv0_le_low q v0 u0 u1 u2 u3 hle
  have hb : ¬ BitVec.ult uTop (mulsubN4 q v0 0 0 0 u0 u1 u2 u3).2.2.2.2 := by
    rw [hc3]
    exact (EvmWord.ult_iff).not.mpr (by simp)
  have hout := iterWithDoubleAddback_no_borrow (qHat := q) (v0 := v0) (v1 := 0)
      (v2 := 0) (v3 := 0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3)
      (uTop := uTop) hb
  simp only [] at hout
  rw [hout]

theorem iterN1_v4_val256_conservation_v3_zero_of_carry2
    (bltu : Bool) (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| (0 : Word) ≠ 0)
    (hcarry2 : Carry2NzAll v0 v1 v2 0) :
    let out := iterN1_v4 bltu v0 v1 v2 0 u0 u1 u2 u3 uTop
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
        EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 := by
  cases bltu
  · simp only [iterN1_v4_false]
    unfold iterN1Max
    exact iterWithDoubleAddback_val256_conservation_v3_zero_of_carry2
      (signExtend12 4095) v0 v1 v2 u0 u1 u2 u3 uTop hbnz
      (hcarry2 (signExtend12 4095) u0 u1 u2 u3 uTop)
  · simp only [iterN1_v4_true]
    unfold iterN1Call_v4
    exact iterWithDoubleAddback_val256_conservation_v3_zero_of_carry2
      (div128Quot_v4 u1 u0 v0) v0 v1 v2 u0 u1 u2 u3 uTop hbnz
      (hcarry2 (div128Quot_v4 u1 u0 v0) u0 u1 u2 u3 uTop)

@[irreducible]
def fullDivN1R3_v4 (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  iterN1_v4 bltu_3 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)

@[irreducible]
def fullDivN1R2_v4 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_2 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1

@[irreducible]
def fullDivN1R1_v4 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_1 v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1

@[irreducible]
def fullDivN1R0_v4 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Word × Word × Word × Word × Word × Word :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  iterN1_v4 bltu_0 v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

def isTrialN1_v4_j3 (bltu_3 : Bool) (a3 b0 : Word) : Prop :=
  isTrialN1_j3 bltu_3 a3 b0

def isTrialN1_v4_j2 (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Prop :=
  bltu_2 = BitVec.ult
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

def isTrialN1_v4_j1 (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_1 = BitVec.ult
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

def isTrialN1_v4_j0 (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 = BitVec.ult
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).1

@[irreducible]
def fullDivN1QuotientVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  r3.1.toNat * B^3 + r2.1.toNat * B^2 + r1.1.toNat * B + r0.1.toNat

@[irreducible]
def fullDivN1CorrectedTrialVal_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Nat :=
  let B := 2^64
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let qHat3 : Word := if bltu_3 then div128Quot_v4 u.2.2.2.2 u.2.2.2.1 v.1
    else signExtend12 4095
  let qHat2 : Word := if bltu_2 then div128Quot_v4 r3.2.1 u.2.2.1 v.1
    else signExtend12 4095
  let qHat1 : Word := if bltu_1 then div128Quot_v4 r2.2.1 u.2.1 v.1
    else signExtend12 4095
  let qHat0 : Word := if bltu_0 then div128Quot_v4 r1.2.1 u.1 v.1
    else signExtend12 4095
  (qHat3.toNat - 2) * B^3 + (qHat2.toNat - 2) * B^2 +
    (qHat1.toNat - 2) * B + (qHat0.toNat - 2)

theorem fullDivN1R3_v4_step_conservation
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0
      (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u
  subst v
  subst u
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_3
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0 hvnz hc
  delta n1StepConservation
  delta fullDivN1R3_v4
  simpa [hv3z] using h

theorem fullDivN1R2_v4_step_conservation
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.1
      r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
      (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r3
  subst v
  subst u
  subst r3
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_2
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R2_v4
  simpa [hv3z] using h

theorem fullDivN1R1_v4_step_conservation
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.2.1
      r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
      (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r2
  subst v
  subst u
  subst r2
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R1_v4
  simpa [hv3z] using h

theorem fullDivN1R0_v4_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    n1StepConservation v.1 v.2.1 v.2.2.1 u.1
      r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) := by
  intro v u r1
  subst v
  subst u
  subst r1
  have hv3z := fullDivN1NormV_v3_eq_zero_of_high_zero b0 b1 b2 b3 hb3z hb2z
  have hvnz :
      (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
    simpa [hv3z] using
      fullDivN1NormV_or_ne_zero_of_high_zero b0 b1 b2 b3 hb1z hb2z hb3z hbnz
  have hc :
      Carry2NzAll (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 0 := by
    simpa [hv3z] using hcarry2
  have h := iterN1_v4_val256_conservation_v3_zero_of_carry2 bltu_0
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hvnz hc
  delta n1StepConservation
  delta fullDivN1R0_v4
  simpa [hv3z] using h

@[irreducible]
def fullDivN1StepsConservation_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsConservation v u r3 r2 r1 r0

theorem fullDivN1StepsConservation_v4_of_runtime
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    fullDivN1StepsConservation_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation_v4
  delta n1StepsConservation
  constructor
  · exact fullDivN1R3_v4_step_conservation
      bltu_3 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R2_v4_step_conservation
      bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz hcarry2
  constructor
  · exact fullDivN1R1_v4_step_conservation
      bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hbnz
      hcarry2
  · exact fullDivN1R0_v4_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z
      hbnz hcarry2

@[irreducible]
def fullDivN1StepsTelescoped_v4
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
  let r2 := fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  n1StepsTelescoped v u r3 r2 r1 r0

theorem fullDivN1StepsTelescoped_v4_of_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hsteps : fullDivN1StepsConservation_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1StepsTelescoped_v4 bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  delta fullDivN1StepsConservation_v4 at hsteps
  delta fullDivN1StepsTelescoped_v4
  exact n1StepsTelescoped_of_conservation
    (fullDivN1NormV b0 b1 b2 b3)
    (fullDivN1NormU a0 a1 a2 a3 b0)
    (fullDivN1R3_v4 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R2_v4 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R1_v4 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R0_v4 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    hsteps

end EvmAsm.Evm64
