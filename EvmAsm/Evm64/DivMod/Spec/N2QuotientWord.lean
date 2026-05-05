/-
  EvmAsm.Evm64.DivMod.Spec.N2QuotientWord

  Quotient-word helper for the n=2 DIV path. Mirrors the n=1 helper bundle
  in `Spec.Dispatcher` (`fullDivN1QuotientWord` and friends): packages the
  four per-limb results from `fullDivN2R{0,1,2}` (with a zero top limb)
  into a single `EvmWord`, and provides the standard structural lemmas
  (per-limb extraction, `BitVec.eq_of_toNat_eq` bridge, `toNat`-as-`val256`,
  and a `val256`-equality bridge to `EvmWord.div`).

  These will be consumed by a follow-up slice that introduces
  `evm_div_n2_stack_spec_within_word`, mirroring `evm_div_n1_stack_spec_within_word`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

  See beads `evm-asm-qqn4`, parent `evm-asm-wp69` (#61 slice 2).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Pack the four per-limb DIV results from the n=2 path into a single
    `EvmWord`. The top limb is `0` because n=2 means `b2 = b3 = 0` and so
    the quotient cannot exceed 192 bits. -/
@[irreducible]
def fullDivN2QuotientWord (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (0 : Word))

/-- If `fullDivN2QuotientWord ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding `fullDivN2R{0,1,2}` result
    (and limb 3 is zero). -/
theorem fullDivN2_hdivs_of_word_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]
    delta fullDivN2QuotientWord
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]
    delta fullDivN2QuotientWord
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]
    delta fullDivN2QuotientWord
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN2QuotientWord
    exact EvmWord.getLimbN_fromLimbs_3

/-- The `toNat` of the packed quotient word equals the four-limb
    `EvmWord.val256` of the per-limb results (with top limb zero). -/
theorem fullDivN2QuotientWord_toNat
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3).toNat =
    EvmWord.val256
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
      (0 : Word) := by
  delta fullDivN2QuotientWord
  rw [EvmWord.fromLimbs_toNat]
  rfl

end EvmAsm.Evm64
