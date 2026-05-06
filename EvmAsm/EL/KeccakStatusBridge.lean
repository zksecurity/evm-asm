/-
  EvmAsm.EL.KeccakStatusBridge

  Extends `EvmAsm/EL/KeccakEcallBridge.lean` with the `zkvm_status` return
  value defined by the C ABI in
  `EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`.

  The C signature for KECCAK is

      zkvm_status zkvm_keccak256(const uint8_t* data, size_t len,
                                 zkvm_keccak256_hash* output);

  i.e. the accelerator returns a `zkvm_status` (`ZKVM_EOK = 0`,
  `ZKVM_EFAIL = -1`) and, on success, populates the 32-byte hash output
  buffer. The existing `KeccakEcallBridge` only models the success-path
  payload shape (input → 32-byte hash) and assumes the call always
  succeeds. This file adds a status-aware layer on top:

  * `KeccakAccelerator` is the new accelerator interface that returns
    `ZkvmStatus × AcceleratorOutput` for every input.
  * `KeccakStatusResult` carries both fields.
  * `executeKeccakEcallStatus` runs the status-aware accelerator.
  * `statusWord` extracts the RV64 `a0` return-register `Word` via the
    `zkvmStatusToWord` bridge from `EvmAsm/Evm64/Accelerators/Status.lean`.
  * Conversions tie the success path back to `executeKeccakEcall` from
    `KeccakEcallBridge.lean`, so existing payload-only proofs continue to
    apply on `.eok` results.

  Refs: parent beads task `evm-asm-nr2sk`, slice `evm-asm-acve1`.
  Distinctive token: KeccakStatusBridge.executeKeccakEcallStatus #114.
-/

import EvmAsm.EL.KeccakEcallBridge
import EvmAsm.Evm64.Accelerators.Status

namespace EvmAsm.EL

namespace KeccakStatusBridge

open EvmAsm.Accelerators (ZkvmStatus)

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Status-aware accelerator interface for KECCAK256: returns both the
`zkvm_status` and the (deterministic) output buffer for every input. The
output buffer's content is meaningful only when the status is
`ZkvmStatus.eok`; on `.efail` the output is unspecified and consumers
must not push a stack word from it. -/
abbrev KeccakAccelerator :=
  KeccakInputBridge.AcceleratorInput → ZkvmStatus × KeccakResultBridge.AcceleratorOutput

/-- Status-aware result of an accelerator ECALL. -/
structure KeccakStatusResult where
  status : ZkvmStatus
  output : KeccakResultBridge.AcceleratorOutput

/-- Run the status-aware KECCAK accelerator. -/
def executeKeccakEcallStatus
    (accelerator : KeccakAccelerator)
    (request : KeccakEcallBridge.KeccakRequest) : KeccakStatusResult :=
  let pair := accelerator request.input
  { status := pair.1, output := pair.2 }

@[simp] theorem executeKeccakEcallStatus_status
    (accelerator : KeccakAccelerator)
    (request : KeccakEcallBridge.KeccakRequest) :
    (executeKeccakEcallStatus accelerator request).status =
      (accelerator request.input).1 := rfl

@[simp] theorem executeKeccakEcallStatus_output
    (accelerator : KeccakAccelerator)
    (request : KeccakEcallBridge.KeccakRequest) :
    (executeKeccakEcallStatus accelerator request).output =
      (accelerator request.input).2 := rfl

/-- Project the success-path `KeccakResult` from a status-aware result. The
projection drops the `status` field; clients must guard with
`statusIsOk` before pushing a stack word. -/
def toKeccakResult (result : KeccakStatusResult) : KeccakEcallBridge.KeccakResult :=
  { output := result.output }

@[simp] theorem toKeccakResult_output (result : KeccakStatusResult) :
    (toKeccakResult result).output = result.output := rfl

/-- Reduce the success-path side of `executeKeccakEcallStatus` to the
existing `executeKeccakEcall` shape: drop the status, keep the output. -/
theorem toKeccakResult_executeKeccakEcallStatus
    (accelerator : KeccakAccelerator)
    (request : KeccakEcallBridge.KeccakRequest) :
    toKeccakResult (executeKeccakEcallStatus accelerator request) =
      KeccakEcallBridge.executeKeccakEcall
        (fun input => (accelerator input).2) request := rfl

/-- Boolean view of `result.status = .eok`. -/
def statusIsOk (result : KeccakStatusResult) : Bool := result.status.isOk

@[simp] theorem statusIsOk_eq (result : KeccakStatusResult) :
    statusIsOk result = result.status.isOk := rfl

/-- Stack word pushed on the success path. Mirrors
`KeccakEcallBridge.stackWordFromResult` but routes through the status
projection so callers don't need to unfold `toKeccakResult`. -/
def stackWordFromStatusResult (result : KeccakStatusResult) : EvmWord :=
  KeccakEcallBridge.stackWordFromResult (toKeccakResult result)

theorem stackWordFromStatusResult_eq (result : KeccakStatusResult) :
    stackWordFromStatusResult result =
      KeccakResultBridge.stackWordFromAcceleratorOutput result.output := rfl

/-- RV64 `a0` return-register `Word` for the accelerator status. -/
def statusWord (result : KeccakStatusResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : KeccakStatusResult} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : KeccakStatusResult} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : KeccakStatusResult) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : KeccakStatusResult) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Always-success accelerator: lift a payload-only accelerator (the shape
modelled by `KeccakEcallBridge.executeKeccakEcall`) into the status-aware
interface by tagging every result with `ZkvmStatus.eok`. -/
def liftAlwaysOk
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput) : KeccakAccelerator :=
  fun input => (.eok, accelerator input)

@[simp] theorem liftAlwaysOk_status
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (input : KeccakInputBridge.AcceleratorInput) :
    (liftAlwaysOk accelerator input).1 = .eok := rfl

@[simp] theorem liftAlwaysOk_output
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (input : KeccakInputBridge.AcceleratorInput) :
    (liftAlwaysOk accelerator input).2 = accelerator input := rfl

/-- The lifted accelerator preserves the success-path output shape: the
status-aware execution returns the same hash bytes as the existing
payload-only `executeKeccakEcall`. -/
theorem executeKeccakEcallStatus_liftAlwaysOk
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakEcallBridge.KeccakRequest) :
    executeKeccakEcallStatus (liftAlwaysOk accelerator) request =
      { status := .eok
        output := (KeccakEcallBridge.executeKeccakEcall accelerator request).output } := rfl

/-- The lifted-accelerator status word is always `ZKVM_EOK`. -/
theorem statusWord_executeKeccakEcallStatus_liftAlwaysOk
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakEcallBridge.KeccakRequest) :
    statusWord (executeKeccakEcallStatus (liftAlwaysOk accelerator) request) =
      EvmAsm.Rv64.zkvmStatusEokWord := rfl

/-- The lifted-accelerator stack word matches the existing payload-only
bridge. -/
theorem stackWordFromStatusResult_liftAlwaysOk
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakEcallBridge.KeccakRequest) :
    stackWordFromStatusResult
        (executeKeccakEcallStatus (liftAlwaysOk accelerator) request) =
      KeccakEcallBridge.stackWordFromResult
        (KeccakEcallBridge.executeKeccakEcall accelerator request) := rfl

end KeccakStatusBridge

end EvmAsm.EL
