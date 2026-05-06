/-
  EvmAsm.Evm64.Accelerators.Status

  Lean bridge for the `zkvm_status` enum from
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.

  The C header (current upstream version) defines exactly two return codes:

      typedef enum {
          ZKVM_EOK   =  0,   /* Success */
          ZKVM_EFAIL = -1    /* Failure */
      } zkvm_status;

  This module mirrors that enum, provides the matching `Int32` numeric encoding,
  and exposes the `a0` return-register `Word` constants used to bridge accelerator
  ECALL postconditions to RISC-V state.

  Refs: parent beads task `evm-asm-nr2sk`, slice `evm-asm-hzmi6`.
-/

import EvmAsm.Rv64.Basic

namespace EvmAsm
namespace Accelerators

/-- Status codes returned by zkVM accelerator functions, mirroring the
`zkvm_status` C enum. The C enum is signed (`ZKVM_EFAIL = -1`); we model it
as a Lean inductive and provide a 32-bit signed encoding. -/
inductive ZkvmStatus where
  | eok    -- ZKVM_EOK   =  0  (Success)
  | efail  -- ZKVM_EFAIL = -1  (Failure)
  deriving DecidableEq, Repr, Inhabited

namespace ZkvmStatus

/-- 32-bit signed encoding matching the C enum's numeric values exactly.
`ZKVM_EOK` is `0`; `ZKVM_EFAIL` is `-1`, encoded as the all-ones `Int32`
bit-pattern `0xFFFFFFFF`. -/
def toInt32 : ZkvmStatus → Int32
  | .eok   => 0
  | .efail => -1

/-- Predicate identifying the success status. -/
def isOk : ZkvmStatus → Bool
  | .eok   => true
  | .efail => false

@[simp] theorem isOk_eok   : isOk .eok   = true  := rfl
@[simp] theorem isOk_efail : isOk .efail = false := rfl

/-- `isOk` agrees with structural equality against `eok`. -/
theorem isOk_iff_eq_eok (s : ZkvmStatus) : s.isOk = true ↔ s = .eok := by
  cases s <;> simp [isOk]

/-- The two encodings are distinct. -/
theorem toInt32_eok_ne_efail : (ZkvmStatus.eok).toInt32 ≠ (ZkvmStatus.efail).toInt32 := by
  decide

/-- The encoding is injective. -/
theorem toInt32_injective : Function.Injective ZkvmStatus.toInt32 := by
  intro a b h
  cases a <;> cases b <;> simp [toInt32] at h ⊢
  all_goals (first | rfl | exact (h rfl).elim | exact absurd h (by decide))

end ZkvmStatus

end Accelerators
end EvmAsm

namespace EvmAsm
namespace Rv64

/-- RISC-V `a0` return-register `Word` value corresponding to `ZKVM_EOK`.
Accelerator ECALL handlers that succeed leave `0` in `a0`; this constant
names that value for postcondition reasoning. -/
def zkvmStatusEokWord : Word := 0

/-- RISC-V `a0` return-register `Word` value corresponding to `ZKVM_EFAIL`.
The C enum value is `-1` (signed `Int32`). On the RV64 ABI, accelerator
return codes occupy `a0` (a 64-bit register) sign-extended from `Int32`,
so `ZKVM_EFAIL` is the all-ones 64-bit word `0xFFFFFFFFFFFFFFFF`. -/
def zkvmStatusEfailWord : Word := BitVec.allOnes 64

/-- The two status words are distinct. -/
theorem zkvmStatusEokWord_ne_efailWord :
    zkvmStatusEokWord ≠ zkvmStatusEfailWord := by
  decide

end Rv64
end EvmAsm
