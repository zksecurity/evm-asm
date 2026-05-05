/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1Conservation

  Compact per-iteration conservation wrappers for the n=1 full path.
-/


import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases
import EvmAsm.Evm64.EvmWordArith.DivN4DoubleAddback
import EvmAsm.Evm64.EvmWordArith.ModBridgeUtop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

@[irreducible]
def n1StepConservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word) : Prop :=
  EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
    out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256

@[irreducible]
def n1StepRemainderVal (out : Word × Word × Word × Word × Word × Word) : Nat :=
  EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1

@[irreducible]
def n1StepTopVal (out : Word × Word × Word × Word × Word × Word) : Nat :=
  out.2.2.2.2.2.toNat

@[irreducible]
def n1StepsCarryVal
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Nat :=
  let B := 2^64
  n1StepTopVal r0 * B^4 + n1StepTopVal r1 * B^5 +
    n1StepTopVal r2 * B^6 + n1StepTopVal r3 * B^7

theorem n1StepRemainderVal_mul_base
    (out : Word × Word × Word × Word × Word × Word) :
    let B := 2^64
    n1StepRemainderVal out * B =
      out.2.1.toNat * B + out.2.2.1.toNat * B^2 +
        out.2.2.2.1.toNat * B^3 + out.2.2.2.2.1.toNat * B^4 := by
  intro B
  delta n1StepRemainderVal
  unfold EvmWord.val256
  ring


@[irreducible]
def n1StepConservationNat
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word) : Prop :=
  u0.toNat + u1.toNat * 2^64 + u2.toNat * 2^128 + u3.toNat * 2^192 +
      uTop.toNat * 2^256 =
    out.1.toNat * EvmWord.val256 v0 v1 v2 0 +
      n1StepRemainderVal out + n1StepTopVal out * 2^256

theorem n1StepConservationNat_of_conservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (out : Word × Word × Word × Word × Word × Word)
    (h : n1StepConservation v0 v1 v2 u0 u1 u2 u3 uTop out) :
    n1StepConservationNat v0 v1 v2 u0 u1 u2 u3 uTop out := by
  delta n1StepConservation at h
  delta n1StepConservationNat
  unfold EvmWord.val256 at h ⊢
  delta n1StepRemainderVal n1StepTopVal
  exact h

@[irreducible]
def n1StepsTelescoped
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  let B := 2^64
  EvmWord.val256 u.1 u.2.1 u.2.2.1 u.2.2.2.1 +
      u.2.2.2.2.toNat * B^4 =
    (r3.1.toNat * B^3 + r2.1.toNat * B^2 +
        r1.1.toNat * B + r0.1.toNat) *
      EvmWord.val256 v.1 v.2.1 v.2.2.1 0 + n1StepRemainderVal r0 +
      n1StepsCarryVal r3 r2 r1 r0

@[irreducible]
def n1StepsConservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0 r3 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.2.1
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 r2 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 r1 ∧
  n1StepConservation v.1 v.2.1 v.2.2.1 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 r0

@[irreducible]
def n1StepsConservationNat
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.2.2.1 u.2.2.2.2 0 0 0 r3 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.2.1
    r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 r2 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.2.1
    r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 r1 ∧
  n1StepConservationNat v.1 v.2.1 v.2.2.1 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 r0

@[irreducible]
def n1StepsTelescopeInput
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word) : Prop :=
  let B := 2^64
  let V := EvmWord.val256 v.1 v.2.1 v.2.2.1 0
  u.2.2.2.1.toNat + u.2.2.2.2.toNat * B =
    r3.1.toNat * V + n1StepRemainderVal r3 + n1StepTopVal r3 * B^4 ∧
  u.2.2.1.toNat + n1StepRemainderVal r3 * B =
    r2.1.toNat * V + n1StepRemainderVal r2 + n1StepTopVal r2 * B^4 ∧
  u.2.1.toNat + n1StepRemainderVal r2 * B =
    r1.1.toNat * V + n1StepRemainderVal r1 + n1StepTopVal r1 * B^4 ∧
  u.1.toNat + n1StepRemainderVal r1 * B =
    r0.1.toNat * V + n1StepRemainderVal r0 + n1StepTopVal r0 * B^4

theorem n1StepsConservationNat_of_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservation v u r3 r2 r1 r0) :
    n1StepsConservationNat v u r3 r2 r1 r0 := by
  delta n1StepsConservation at hsteps
  delta n1StepsConservationNat
  rcases hsteps with ⟨h3, h2, h1, h0⟩
  exact ⟨
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h3,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h2,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h1,
    n1StepConservationNat_of_conservation _ _ _ _ _ _ _ _ _ h0⟩

theorem n1TelescopeInput3_of_nat
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 : Word × Word × Word × Word × Word × Word)
    (h3 : n1StepConservationNat v.1 v.2.1 v.2.2.1
      u.2.2.2.1 u.2.2.2.2 0 0 0 r3) :
    let B := 2^64
    let V := EvmWord.val256 v.1 v.2.1 v.2.2.1 0
    u.2.2.2.1.toNat + u.2.2.2.2.toNat * B =
      r3.1.toNat * V + n1StepRemainderVal r3 + n1StepTopVal r3 * B^4 := by
  intro B V
  delta n1StepConservationNat at h3
  subst B; subst V
  simp at h3 ⊢
  exact h3

theorem n1TelescopeInput_of_nat_remainder
    (v0 v1 v2 u0 : Word)
    (rin rout : Word × Word × Word × Word × Word × Word)
    (h : n1StepConservationNat v0 v1 v2 u0
      rin.2.1 rin.2.2.1 rin.2.2.2.1 rin.2.2.2.2.1 rout) :
    let B := 2^64
    let V := EvmWord.val256 v0 v1 v2 0
    u0.toNat + n1StepRemainderVal rin * B =
      rout.1.toNat * V + n1StepRemainderVal rout + n1StepTopVal rout * B^4 := by
  intro B V
  delta n1StepConservationNat at h
  rw [n1StepRemainderVal_mul_base]
  subst B; subst V
  norm_num at h ⊢
  omega

theorem n1StepsTelescopeInput_of_nat_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservationNat v u r3 r2 r1 r0) :
    n1StepsTelescopeInput v u r3 r2 r1 r0 := by
  delta n1StepsConservationNat at hsteps
  delta n1StepsTelescopeInput
  rcases hsteps with ⟨h3, h2, h1, h0⟩
  exact ⟨
    n1TelescopeInput3_of_nat v u r3 h3,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.2.2.1 r3 r2 h2,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.2.1 r2 r1 h1,
    n1TelescopeInput_of_nat_remainder v.1 v.2.1 v.2.2.1 u.1 r1 r0 h0⟩

theorem n1NatStepConservation_telescope
    {B V q3 q2 q1 q0 rem3 rem2 rem1 rem0 top3 top2 top1 top0
      u0 u1 u2 u3 u4 : Nat}
    (h3 : u3 + u4 * B = q3 * V + rem3 + top3 * B^4)
    (h2 : u2 + rem3 * B = q2 * V + rem2 + top2 * B^4)
    (h1 : u1 + rem2 * B = q1 * V + rem1 + top1 * B^4)
    (h0 : u0 + rem1 * B = q0 * V + rem0 + top0 * B^4) :
    u0 + u1 * B + u2 * B^2 + u3 * B^3 + u4 * B^4 =
      (q3 * B^3 + q2 * B^2 + q1 * B + q0) * V + rem0 +
        top0 * B^4 + top1 * B^5 + top2 * B^6 + top3 * B^7 := by
  have H3 := congrArg (fun x => x * B^3) h3
  have H2 := congrArg (fun x => x * B^2) h2
  have H1 := congrArg (fun x => x * B) h1
  ring_nf at H3 H2 H1 h0 ⊢
  nlinarith

theorem n1StepsTelescoped_of_telescopeInput
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hinput : n1StepsTelescopeInput v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 := by
  delta n1StepsTelescopeInput at hinput
  delta n1StepsTelescoped n1StepsCarryVal
  rcases hinput with ⟨h3, h2, h1, h0⟩
  have ht := n1NatStepConservation_telescope h3 h2 h1 h0
  unfold EvmWord.val256 at ht ⊢
  ring_nf at ht ⊢
  exact ht

theorem n1StepsTelescoped_of_nat_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservationNat v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 :=
  n1StepsTelescoped_of_telescopeInput v u r3 r2 r1 r0
    (n1StepsTelescopeInput_of_nat_conservation v u r3 r2 r1 r0 hsteps)

theorem n1StepsTelescoped_of_conservation
    (v : Word × Word × Word × Word) (u : Word × Word × Word × Word × Word)
    (r3 r2 r1 r0 : Word × Word × Word × Word × Word × Word)
    (hsteps : n1StepsConservation v u r3 r2 r1 r0) :
    n1StepsTelescoped v u r3 r2 r1 r0 :=
  n1StepsTelescoped_of_nat_conservation v u r3 r2 r1 r0
    (n1StepsConservationNat_of_conservation v u r3 r2 r1 r0 hsteps)

end EvmAsm.Evm64





