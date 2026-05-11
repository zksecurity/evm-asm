/-
  EvmAsm.Evm64.EvmWordArith.Exp

  Pure EVM EXP semantics over 256-bit words. This is the semantic target for
  the executable EXP opcode proof: exponentiation in Nat, reduced modulo 2^256.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace EvmWord

/-- EVM EXP semantics: `base ^ exponent`, reduced modulo `2^256`. -/
def exp (base exponent : EvmWord) : EvmWord :=
  BitVec.ofNat 256 (base.toNat ^ exponent.toNat)

/-- `EvmWord.exp` is Nat exponentiation modulo the 256-bit word modulus. -/
theorem exp_correct (base exponent : EvmWord) :
    (exp base exponent).toNat = base.toNat ^ exponent.toNat % 2^256 := by
  simp [exp, BitVec.toNat_ofNat]

/-- EVM's `0^0` case follows Nat exponentiation and returns one. -/
theorem exp_zero_zero : exp 0 0 = 1 := by
  native_decide

/-- Any base raised to the zero EVM word is one. -/
theorem exp_zero_right (base : EvmWord) : exp base 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- The maximum EVM word raised to zero is one. -/
theorem exp_max_zero_right : exp (-1 : EvmWord) 0 = 1 := by
  exact exp_zero_right (-1 : EvmWord)

/-- One raised to any exponent remains one. -/
theorem exp_one_left (exponent : EvmWord) : exp 1 exponent = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp

/-- Zero raised to any nonzero EVM exponent remains zero. -/
theorem exp_zero_left_of_ne_zero (exponent : EvmWord) (h : exponent ≠ 0) :
    exp 0 exponent = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hpos : 0 < exponent.toNat := by
    rcases Nat.eq_zero_or_pos exponent.toNat with hz | hp
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [hz])) h
    · exact hp
  simp [Nat.zero_pow hpos]

/-- Zero raised to an exponent with positive Nat value remains zero. -/
theorem exp_zero_left_of_toNat_pos (exponent : EvmWord)
    (h_pos : 0 < exponent.toNat) :
    exp 0 exponent = 0 := by
  exact exp_zero_left_of_ne_zero exponent (by
    intro h_zero
    rw [h_zero] at h_pos
    simp at h_pos)

/-- Zero raised to one remains zero. -/
theorem exp_zero_one : exp (0 : EvmWord) 1 = 0 := by
  exact exp_zero_left_of_ne_zero 1 (by decide)

/-- Zero raised to the maximum EVM word exponent remains zero. -/
theorem exp_zero_left_max : exp 0 (-1 : EvmWord) = 0 := by
  exact exp_zero_left_of_ne_zero (-1 : EvmWord) (by decide)

/-- Any base raised to the EVM word one is itself. -/
theorem exp_one_right (base : EvmWord) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  simp [Nat.mod_eq_of_lt base.isLt]

/-- The maximum EVM word raised to one remains the maximum EVM word. -/
theorem exp_max_one_right : exp (-1 : EvmWord) 1 = (-1 : EvmWord) := by
  exact exp_one_right (-1 : EvmWord)

/-- Two raised to one remains two. -/
theorem exp_two_one : exp (2 : EvmWord) 1 = 2 := by
  exact exp_one_right (2 : EvmWord)

/-- Successor recurrence for EXP when the exponent increment does not wrap. -/
theorem exp_succ_right_of_toNat_lt (base exponent : EvmWord)
    (h : exponent.toNat + 1 < 2^256) :
    exp base (exponent + 1) = base * exp base exponent := by
  apply BitVec.eq_of_toNat_eq
  rw [exp_correct]
  have hSucc : (exponent + 1).toNat = exponent.toNat + 1 := by
    rw [BitVec.toNat_add]
    have h1 : (1 : EvmWord).toNat = 1 := by decide
    rw [h1]
    exact Nat.mod_eq_of_lt h
  rw [hSucc]
  rw [BitVec.toNat_mul]
  rw [exp_correct]
  rw [Nat.pow_succ]
  rw [Nat.mul_comm (base.toNat ^ exponent.toNat) base.toNat]
  rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt base.isLt]

/-- The GH #92 cross-limb boundary case `EXP(2, 64)`. -/
theorem exp_two_64 : exp (2 : EvmWord) (64 : EvmWord) =
    BitVec.ofNat 256 (2^64) := by
  native_decide

/-- The GH #92 mid-word boundary case `EXP(2, 128)`. -/
theorem exp_two_128 : exp (2 : EvmWord) (128 : EvmWord) =
    BitVec.ofNat 256 (2^128) := by
  native_decide

/-- The GH #92 pre-wrap boundary case `EXP(2, 255)` is the high bit. -/
theorem exp_two_255 : exp (2 : EvmWord) (255 : EvmWord) =
    BitVec.ofNat 256 (2^255) := by
  native_decide

/-- The GH #92 boundary case `EXP(2, 256)` wraps to zero modulo `2^256`. -/
theorem exp_two_256 : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  native_decide

-- Edge checks required by GH #92's EXP acceptance notes.
example : exp (0 : EvmWord) (0 : EvmWord) = 1 := by
  native_decide

example : exp (2 : EvmWord) (256 : EvmWord) = 0 := by
  exact exp_two_256

end EvmWord

end EvmAsm.Evm64
