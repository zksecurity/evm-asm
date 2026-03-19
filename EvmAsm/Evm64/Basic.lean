/-
  EvmAsm.Evm64.Basic

  Types and conversions for 256-bit EVM words on 64-bit RISC-V.
  Each EvmWord is stored as 4 little-endian 64-bit limbs.
-/

import EvmAsm.Rv64.Basic
import Std.Tactic.BVDecide

namespace EvmAsm.Rv64

/-- A 256-bit EVM word. -/
abbrev EvmWord := BitVec 256

namespace EvmWord

/-- Extract the i-th 64-bit limb (little-endian, i=0 is LSB). -/
def getLimb (v : EvmWord) (i : Fin 4) : Word :=
  v.extractLsb' (i.val * 64) 64

/-- Reconstruct a 256-bit value from 4 limbs. -/
def fromLimbs (limbs : Fin 4 → Word) : EvmWord :=
  (limbs 0).zeroExtend 256 |||
  ((limbs 1).zeroExtend 256 <<< 64) |||
  ((limbs 2).zeroExtend 256 <<< 128) |||
  ((limbs 3).zeroExtend 256 <<< 192)

/-- Bitwise AND distributes over limbs. -/
theorem getLimb_and (x y : EvmWord) (i : Fin 4) :
    (x &&& y).getLimb i = x.getLimb i &&& y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_and]

/-- Bitwise OR distributes over limbs. -/
theorem getLimb_or (x y : EvmWord) (i : Fin 4) :
    (x ||| y).getLimb i = x.getLimb i ||| y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_or]

/-- Bitwise XOR distributes over limbs. -/
theorem getLimb_xor (x y : EvmWord) (i : Fin 4) :
    (x ^^^ y).getLimb i = x.getLimb i ^^^ y.getLimb i := by
  simp only [getLimb, BitVec.extractLsb'_xor]

/-- Bitwise NOT distributes over limbs. -/
theorem getLimb_not (x : EvmWord) (i : Fin 4) :
    (~~~x).getLimb i = ~~~(x.getLimb i) := by
  simp only [getLimb]
  have hi := i.isLt
  ext j
  simp only [BitVec.getElem_extractLsb', BitVec.getElem_not, BitVec.getLsbD_not]
  have hbound : i.val * 64 + j < 256 := by omega
  simp [hbound]

/-- Round-trip: fromLimbs ∘ getLimb = id. -/
theorem fromLimbs_getLimb (v : EvmWord) :
    EvmWord.fromLimbs (v.getLimb) = v := by
  simp only [fromLimbs, getLimb,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  bv_decide

private theorem getLimb_fromLimbs_0 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 0 = limbs 0 := by
  simp only [fromLimbs, getLimb, show (0 : Fin 4).val = 0 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_1 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 1 = limbs 1 := by
  simp only [fromLimbs, getLimb, show (1 : Fin 4).val = 1 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_2 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 2 = limbs 2 := by
  simp only [fromLimbs, getLimb, show (2 : Fin 4).val = 2 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide
private theorem getLimb_fromLimbs_3 (limbs : Fin 4 → Word) :
    (EvmWord.fromLimbs limbs).getLimb 3 = limbs 3 := by
  simp only [fromLimbs, getLimb, show (3 : Fin 4).val = 3 from rfl]
  generalize limbs 0 = l0; generalize limbs 1 = l1
  generalize limbs 2 = l2; generalize limbs 3 = l3
  bv_decide

/-- Round-trip: getLimb ∘ fromLimbs = id. -/
theorem getLimb_fromLimbs (limbs : Fin 4 → Word) (i : Fin 4) :
    (EvmWord.fromLimbs limbs).getLimb i = limbs i := by
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact getLimb_fromLimbs_0 limbs
  · exact getLimb_fromLimbs_1 limbs
  · exact getLimb_fromLimbs_2 limbs
  · exact getLimb_fromLimbs_3 limbs

/-- The list of 4 limbs for an EvmWord. -/
def toLimbs (v : EvmWord) : List Word :=
  List.ofFn fun i : Fin 4 => v.getLimb i

theorem toLimbs_length (v : EvmWord) : v.toLimbs.length = 4 := by
  simp [toLimbs]

@[simp] theorem getLimb_one (i : Fin 4) :
    (1 : EvmWord).getLimb i = if i = 0 then 1 else 0 := by
  have h : ∀ j : Fin 4, (1 : EvmWord).getLimb j = if j = 0 then 1 else 0 := by native_decide
  exact h i

@[simp] theorem getLimb_ite (c : Prop) [Decidable c] (x y : EvmWord) (i : Fin 4) :
    (if c then x else y).getLimb i = if c then x.getLimb i else y.getLimb i := by
  split <;> rfl

theorem eq_iff_limbs (a b : EvmWord) :
    a = b ↔ (∀ i, a.getLimb i = b.getLimb i) := by
  constructor
  · intro h; subst h; intro; rfl
  · intro h
    calc a = fromLimbs a.getLimb := (fromLimbs_getLimb a).symm
      _ = fromLimbs b.getLimb := by congr 1; funext i; exact h i
      _ = b := fromLimbs_getLimb b

private theorem fromLimbs_zero : fromLimbs (fun _ => (0 : Word)) = (0 : EvmWord) := by
  simp only [fromLimbs]; bv_decide

theorem eq_zero_iff_limbs (a : EvmWord) :
    a = 0 ↔ a.getLimb 0 = 0 ∧ a.getLimb 1 = 0 ∧ a.getLimb 2 = 0 ∧ a.getLimb 3 = 0 := by
  constructor
  · intro h; subst h
    have hz : ∀ j : Fin 4, (0 : EvmWord).getLimb j = 0 := by native_decide
    exact ⟨hz 0, hz 1, hz 2, hz 3⟩
  · intro ⟨h0, h1, h2, h3⟩
    rw [← fromLimbs_getLimb a]
    unfold fromLimbs
    simp only [h0, h1, h2, h3]
    bv_decide

end EvmWord

end EvmAsm.Rv64
