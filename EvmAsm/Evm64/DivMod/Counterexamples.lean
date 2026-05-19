/-
  EvmAsm.Evm64.DivMod.Counterexamples

  Kernel-checked regression pins for the two n4 call-addback counterexamples
  that motivated the div128 v4 migration.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace DivModCounterexamples

-- The executable DIV/MOD programs must keep the v4 div128 subroutine wired in.
theorem evm_div_uses_div128_v4 :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

theorem evm_mod_uses_div128_v4 :
    evm_mod =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_mod_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) := rfl

-- Counterexample A:
--   a3 = 2^63 + 2^33, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^33 - 1, b1 = b0 = 0
--   q_true = 2^63 + 2^32 - 2
abbrev ceA_a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
abbrev ceA_b2 : Word := BitVec.ofNat 64 (2^33 - 1)
abbrev ceA_b3 : Word := BitVec.ofNat 64 1
abbrev ceA_b3Norm : Word := (ceA_b3 <<< 63) ||| (ceA_b2 >>> 1)
abbrev ceA_u4 : Word := ceA_a3 >>> 1
abbrev ceA_u3 : Word := ceA_a3 <<< 63
abbrev ceA_qTrue : Nat := 2^63 + 2^32 - 2
abbrev ceA_qHatV4 : Word := BitVec.ofNat 64 (ceA_qTrue + 1)

theorem div128Quot_v4_counterexampleA_exact :
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleA_within_two_addbacks :
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  decide

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample A has the v4
    bounded-overshoot shape. -/
theorem evm_div_counterexampleA_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm = ceA_qHatV4 ∧
    (div128Quot_v4 ceA_u4 ceA_u3 ceA_b3Norm).toNat ≤ ceA_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

-- Counterexample B:
--   a3 = 2^64 - 2, a2 = a1 = a0 = 0
--   b3 = 1, b2 = 2^64 - 2, b1 = b0 = 0
--   q_true = floor(val256(a) / val256(b)) = 2^63 - 1
abbrev ceB_a3 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b2 : Word := BitVec.ofNat 64 (2^64 - 2)
abbrev ceB_b3 : Word := BitVec.ofNat 64 1
abbrev ceB_b3Norm : Word := (ceB_b3 <<< 63) ||| (ceB_b2 >>> 1)
abbrev ceB_u4 : Word := ceB_a3 >>> 1
abbrev ceB_u3 : Word := ceB_a3 <<< 63
abbrev ceB_qTrue : Nat := 2^63 - 1
abbrev ceB_qHatV4 : Word := BitVec.ofNat 64 ceB_qTrue

theorem div128Quot_v4_counterexampleB_exact :
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 := by
  decide

theorem div128Quot_v4_counterexampleB_within_two_addbacks :
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  decide

/-- Per-counterexample regression pin: the executable DIV body is on the v4
    path, and the normalized trial quotient for counterexample B has the v4
    exact quotient shape. -/
theorem evm_div_counterexampleB_v4_regression_pin :
    evm_div =
      (divK_phaseA 1020 ;;
      divK_phaseB ;;
      divK_clz ;;
      divK_phaseC2 172 ;;
      divK_normB ;;
      divK_normA 40 ;;
      divK_copyAU ;;
      divK_loopSetup 464 ;;
      divK_loopBody 560 7736 ;;
      divK_denorm ;;
      divK_div_epilogue 24 ;;
      divK_zeroPath ;;
      single (.ADDI .x0 .x0 0) ;;
      divK_div128_v4) ∧
    div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm = ceB_qHatV4 ∧
    (div128Quot_v4 ceB_u4 ceB_u3 ceB_b3Norm).toNat ≤ ceB_qTrue + 2 := by
  constructor
  · exact evm_div_uses_div128_v4
  constructor <;> decide

end DivModCounterexamples

end EvmAsm.Evm64
