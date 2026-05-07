/-
  EvmAsm.EL.Sha256EcallBridge

  Pure zkVM SHA256 accelerator ECALL surface for the Ethereum SHA256
  precompile.
-/

import EvmAsm.EL.Sha256InputBridge
import EvmAsm.EL.Sha256ResultBridge
import EvmAsm.Evm64.Accelerators.Status
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Sha256EcallBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Selector reserved for the `zkvm_sha256` accelerator ECALL surface. -/
def sha256Selector : BitVec 64 := EvmAsm.Rv64.SyscallIdWord.sha256

/-- ECALL request passed to the zkVM SHA256 accelerator. -/
structure Sha256Request where
  selector : BitVec 64
  input : Sha256InputBridge.AcceleratorInput
  deriving Repr

/-- ECALL result returned by the zkVM SHA256 accelerator. -/
structure Sha256Result where
  status : EvmAsm.Accelerators.ZkvmStatus
  output : Sha256ResultBridge.AcceleratorOutput

/-- Build the SHA256 accelerator request from already-loaded input bytes. -/
def requestFromInput (input : Sha256InputBridge.AcceleratorInput) : Sha256Request :=
  { selector := sha256Selector, input := input }

/-- Stack word exposed by a successful SHA256 accelerator result. -/
def stackWordFromResult (result : Sha256Result) : EvmWord :=
  Sha256ResultBridge.stackWordFromAcceleratorOutput result.output

/--
Pure execution boundary for the SHA256 ECALL. The digest computation itself is
supplied by the accelerator model; this bridge fixes the request/result shape,
the status return, and the stack word extracted from the returned output buffer.

Distinctive token: Sha256EcallBridge.executeSha256Ecall.
-/
def executeSha256Ecall
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (request : Sha256Request) : Sha256Result :=
  let result := accelerator request.input
  { status := result.1, output := result.2 }

theorem requestFromInput_selector (input : Sha256InputBridge.AcceleratorInput) :
    (requestFromInput input).selector = sha256Selector := rfl

theorem requestFromInput_input (input : Sha256InputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeSha256Ecall_status
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (request : Sha256Request) :
    (executeSha256Ecall accelerator request).status = (accelerator request.input).1 := by
  rfl

theorem executeSha256Ecall_output
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (request : Sha256Request) :
    (executeSha256Ecall accelerator request).output = (accelerator request.input).2 := by
  rfl

theorem executeSha256Ecall_stackWord
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (request : Sha256Request) :
    stackWordFromResult (executeSha256Ecall accelerator request) =
      Sha256ResultBridge.stackWordFromAcceleratorOutput
        (accelerator request.input).2 := by
  rfl

theorem executeSha256Ecall_fromMemory_stackWord
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (memory : Sha256InputBridge.MemoryReader) (start size : Nat) :
    stackWordFromResult
        (executeSha256Ecall accelerator
          (requestFromInput
            (Sha256InputBridge.acceleratorInputFromMemory memory start size))) =
      Sha256ResultBridge.stackWordFromAcceleratorOutput
        (accelerator
          (Sha256InputBridge.acceleratorInputFromMemory memory start size)).2 := by
  rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`KeccakStatusBridge.statusWord`. The accelerator places the `zkvm_status`
return code in `a0` after the ECALL; this projection extracts that word from
a `Sha256Result` for postcondition reasoning. -/
def statusWord (result : Sha256Result) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Sha256Result} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Sha256Result} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Sha256Result) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Sha256Result) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeSha256Ecall`: the returned `a0` word is
the accelerator-supplied status encoded via `zkvmStatusToWord`. -/
theorem executeSha256Ecall_statusWord
    (accelerator : Sha256InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Sha256ResultBridge.AcceleratorOutput)
    (request : Sha256Request) :
    statusWord (executeSha256Ecall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).1 := by
  rfl

end Sha256EcallBridge

end EvmAsm.EL
