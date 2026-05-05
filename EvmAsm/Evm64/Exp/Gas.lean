/-
  EvmAsm.Evm64.Exp.Gas

  Dynamic gas helpers for the EXP opcode (GH #92). The static/base EXP cost
  remains the table entry in `EvmAsm.Evm64.Gas`; this file adds the
  exponent-byte add-on used by Shanghai-era executable semantics.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Evm64.Gas

namespace EvmAsm.Evm64.ExpGas

/-- Dynamic EXP byte cost charged for each byte of a nonzero exponent. -/
def expGasPerByte : Nat := 50

/-- Number of big-endian bytes needed to encode a natural exponent, with zero
    encoded as length zero for EXP gas accounting. -/
def exponentByteLengthNat : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + exponentByteLengthNat ((n + 1) / 256)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

theorem exponentByteLengthNat_zero : exponentByteLengthNat 0 = 0 := by
  simp [exponentByteLengthNat]

theorem exponentByteLengthNat_succ (n : Nat) :
    exponentByteLengthNat (n + 1) = 1 + exponentByteLengthNat ((n + 1) / 256) := by
  rw [exponentByteLengthNat]

theorem exponentByteLengthNat_of_pos_lt_256 {n : Nat} (h_pos : 0 < n) (h_lt : n < 256) :
    exponentByteLengthNat n = 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [exponentByteLengthNat_succ]
      have h_div : (k + 1) / 256 = 0 := Nat.div_eq_of_lt h_lt
      simp [h_div, exponentByteLengthNat_zero]

theorem exponentByteLengthNat_256 : exponentByteLengthNat 256 = 2 := by
  native_decide

/-- Number of exponent bytes seen by EXP dynamic gas accounting. -/
def exponentByteLength (exponent : EvmWord) : Nat :=
  exponentByteLengthNat exponent.toNat

/-- Dynamic EXP gas add-on from the exponent operand alone. -/
def expDynamicCostFromExponent (exponent : EvmWord) : Nat :=
  expGasPerByte * exponentByteLength exponent

/-- Full EXP gas before memory-independent execution effects: static EXP base
    cost plus the exponent-byte dynamic add-on. -/
def expTotalGasFromExponent (exponent : EvmWord) : Nat :=
  EvmOpcode.staticGasCost .EXP + expDynamicCostFromExponent exponent

theorem exponentByteLength_zero : exponentByteLength (0 : EvmWord) = 0 := by
  unfold exponentByteLength
  simp [exponentByteLengthNat_zero]

theorem exponentByteLength_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    exponentByteLength exponent = 1 := by
  unfold exponentByteLength
  exact exponentByteLengthNat_of_pos_lt_256 h_pos h_lt

theorem exponentByteLength_one : exponentByteLength (1 : EvmWord) = 1 := by
  exact exponentByteLength_of_pos_lt_256 (by decide) (by decide)

theorem exponentByteLength_256 : exponentByteLength (256 : EvmWord) = 2 := by
  unfold exponentByteLength
  native_decide

theorem expDynamicCostFromExponent_zero :
    expDynamicCostFromExponent (0 : EvmWord) = 0 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_zero]

theorem expDynamicCostFromExponent_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    expDynamicCostFromExponent exponent = 50 := by
  unfold expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_of_pos_lt_256 h_pos h_lt]

theorem expTotalGasFromExponent_zero :
    expTotalGasFromExponent (0 : EvmWord) = 10 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_zero]
  rfl

theorem expTotalGasFromExponent_of_pos_lt_256 {exponent : EvmWord}
    (h_pos : 0 < exponent.toNat) (h_lt : exponent.toNat < 256) :
    expTotalGasFromExponent exponent = 60 := by
  unfold expTotalGasFromExponent
  rw [expDynamicCostFromExponent_of_pos_lt_256 h_pos h_lt]
  rfl

theorem expTotalGasFromExponent_256 :
    expTotalGasFromExponent (256 : EvmWord) = 110 := by
  unfold expTotalGasFromExponent expDynamicCostFromExponent expGasPerByte
  rw [exponentByteLength_256]
  rfl

end EvmAsm.Evm64.ExpGas
