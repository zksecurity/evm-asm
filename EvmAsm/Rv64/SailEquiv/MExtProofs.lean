/-
  EvmAsm.Rv64.SailEquiv.MExtProofs

  Per-instruction equivalence theorems for M-extension instructions:
  MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU.

  MUL (low 64 bits) is already proved in ALUProofs.lean.

  Helper lemmas for unsigned division/remainder (to_bits_truncate_neg1,
  to_bits_truncate_natCast, unsigned_div_equiv, unsigned_rem_equiv)
  are proved below. The instruction-level proofs for DIVU/REMU need
  these helpers applied within the monadic expression before wX_bits
  captures the value — this integration is still in progress.
-/

import EvmAsm.Rv64.Execution
import EvmAsm.Rv64.SailEquiv.StateRel
import EvmAsm.Rv64.SailEquiv.MonadLemmas
import EvmAsm.Rv64.SailEquiv.ALUProofs
import LeanRV64D

open LeanRV64D.Functions
open Sail

namespace EvmAsm.Rv64.SailEquiv

set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

-- ============================================================================
-- Proved helper lemmas for unsigned division/remainder
-- ============================================================================

/-- to_bits_truncate on a non-negative integer = BitVec.ofNat. -/
theorem to_bits_truncate_natCast (n : Nat) :
    to_bits_truncate (l := 64) (↑n : Int) = BitVec.ofNat 64 n := by
  simp [to_bits_truncate, get_slice_int]; apply BitVec.eq_of_toNat_eq; simp

/-- to_bits_truncate (-1) = allOnes 64. -/
theorem to_bits_truncate_neg1 :
    to_bits_truncate (l := 64) (-1 : Int) = BitVec.allOnes 64 := by
  simp [to_bits_truncate, get_slice_int, BitVec.allOnes]

/-- BEq bridge: Int.ofNat b.toNat == 0 ↔ b == 0#64. -/
theorem int_ofNat_beq_zero (b : BitVec 64) :
    (Int.ofNat b.toNat == (0 : Int)) = (b == 0#64) := by
  simp [BEq.beq, decide_eq_decide]
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
  · intro h; subst h; simp

/-- Unsigned division: SAIL's Int.tdiv on non-negative = BitVec udiv. -/
theorem unsigned_div_equiv (a b : BitVec 64) (hb : b ≠ 0#64) :
    to_bits_truncate (l := 64) ((↑a.toNat : Int).tdiv (↑b.toNat : Int)) = a / b := by
  rw [show (↑a.toNat : Int).tdiv (↑b.toNat : Int) = ↑(a.toNat / b.toNat) from
    (Int.ofNat_tdiv a.toNat b.toNat).symm]
  rw [to_bits_truncate_natCast]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

/-- Unsigned remainder: SAIL's Int.tmod on non-negative = BitVec umod. -/
theorem unsigned_rem_equiv (a b : BitVec 64) (hb : b ≠ 0#64) :
    to_bits_truncate (l := 64) ((↑a.toNat : Int).tmod (↑b.toNat : Int)) = a % b := by
  have hbn : b.toNat ≠ 0 := by intro h; exact hb (BitVec.eq_of_toNat_eq (by simp [h]))
  rw [show (↑a.toNat : Int).tmod (↑b.toNat : Int) = ↑(a.toNat % b.toNat) from
    (Int.ofNat_tmod a.toNat b.toNat).symm]
  rw [to_bits_truncate_natCast]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod]
  have : a.toNat % b.toNat < b.toNat := Nat.mod_lt _ (by omega)
  omega

-- ============================================================================
-- Instruction proofs — all sorry pending helper integration
-- ============================================================================

theorem mulh_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULH rd rs1 rs2)) s_sail' := by sorry

theorem mulhsu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULHSU rd rs1 rs2)) s_sail' := by sorry

theorem mulhu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_MUL (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd)
        { result_part := VectorHalf.High, signed_rs1 := Signedness.Unsigned,
          signed_rs2 := Signedness.Unsigned }) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.MULHU rd rs1 rs2)) s_sail' := by sorry

theorem div_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.DIV rd rs1 rs2)) s_sail' := by sorry

theorem divu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_DIV (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.DIVU rd rs1 rs2)) s_sail' := by sorry

theorem rem_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) false) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.REM rd rs1 rs2)) s_sail' := by sorry

theorem remu_sail_equiv (s_rv : MachineState) (s_sail : SailState)
    (hrel : StateRel s_rv s_sail) (rd rs1 rs2 : Reg) :
    ∃ s_sail',
      runSail (execute_REM (regToRegidx rs2) (regToRegidx rs1) (regToRegidx rd) true) s_sail
        = some (RETIRE_SUCCESS, s_sail') ∧
      StateRel (execInstrBr s_rv (.REMU rd rs1 rs2)) s_sail' := by sorry

end EvmAsm.Rv64.SailEquiv
