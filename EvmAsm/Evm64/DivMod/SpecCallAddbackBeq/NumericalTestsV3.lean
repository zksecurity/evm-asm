/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.NumericalTestsV3

  Numerical validation tests for `div128Quot_v3` (the fixed algorithm).
  All proofs are `by decide`.

  Counterpart to `SpecCallAddbackBeq/NumericalTests.lean` (which validates
  `div128Quot_v2`'s behavior, including its known bug at unreachable
  inputs).
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV3
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **div128Quot_v3 fixes the truncation bug** — at the input where
    `div128Quot_v2` undershoots by `2^32`, `div128Quot_v3` produces
    the correct quotient.

    Concretely: on `(uHi=2^64-2^32+1, uLo=0, vTop=2^64-1)`,
    `div128Quot_v2` returns `2^64-2^33+1` (wrong) but `div128Quot_v3`
    returns `2^64-2^32+1` (correct, matches the true quotient).

    Kernel-checked via `decide`. -/
theorem div128Quot_v3_correct_at_unreachable_uHi :
    let uHi : Word := BitVec.ofNat 64 (2^64 - 2^32 + 1)
    let uLo : Word := 0
    let vTop : Word := BitVec.ofNat 64 (2^64 - 1)
    let qHat := div128Quot_v3 uHi uLo vTop
    qHat.toNat = (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  decide

/-- **div128Quot_v3 matches div128Quot_v2 on the v1 counterexample** —
    the original input that motivated v2's introduction. Both v2 and v3
    produce the same (correct) quotient on this input because rhatc < 2^32
    holds, so v3's new guard is no-op.

    Kernel-checked via `decide`. -/
theorem div128Quot_v3_eq_v2_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    div128Quot_v3 u4 u3 b3' = div128Quot_v2 u4 u3 b3' := by
  decide

/-- **div128Quot_v3 is correct on the v1 counterexample** —
    composition of v2 correctness (Knuth-A v2) with the
    `div128Quot_v3_eq_v2_on_counterexample` agreement.

    Direct decide-check just confirms v3 produces a quotient ≥ q_true
    on this input (Knuth-A property). -/
theorem div128Quot_v3_knuth_A_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    -- Knuth-A: v3's qHat is at least floor(x / vTop).
    (div128Quot_v3 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) * 2^32 := by
  decide

/-- **div128Quot_v3 produces a 4-limb quotient close to a/b** on the
    v1 counterexample: validates the algorithm's overall correctness
    (qHat = q_true + 1, single-addback case). -/
theorem div128Quot_v3_qHat_eq_q_true_plus_one_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (div128Quot_v3 u4 un3 b3').toNat = q_true + 1 := by
  decide

end EvmAsm.Evm64
