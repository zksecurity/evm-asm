/-
  EvmAsm.EL.Blake2fEcallBridge

  Pure zkVM `zkvm_blake2f` accelerator ECALL surface. Mirrors the
  SHA256/RIPEMD160/Bn254G1Add ECALL bridge skeletons: fixes the request and
  result shapes, the selector binding (via `SyscallIdWord.blake2f`), and
  exposes a pure execution boundary `executeBlake2fEcall` parameterised by
  an accelerator model.
-/

import EvmAsm.EL.Blake2fInputBridge
import EvmAsm.EL.Blake2fResultBridge
import EvmAsm.Evm64.Accelerators.Status
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Blake2fEcallBridge

/-- Selector reserved for the `zkvm_blake2f` accelerator ECALL. -/
def blake2fSelector : BitVec 64 :=
  EvmAsm.Rv64.SyscallIdWord.blake2f

/-- ECALL request passed to the zkVM BLAKE2F accelerator. -/
structure Blake2fRequest where
  selector : BitVec 64
  input    : Blake2fInputBridge.AcceleratorInput

/-- ECALL result returned by the zkVM BLAKE2F accelerator. -/
structure Blake2fResult where
  status : EvmAsm.Accelerators.ZkvmStatus
  output : Blake2fResultBridge.AcceleratorOutput

/-- Build the BLAKE2F accelerator request from already-loaded input. -/
def requestFromInput
    (input : Blake2fInputBridge.AcceleratorInput) : Blake2fRequest :=
  { selector := blake2fSelector, input := input }

/-- Output byte list (length 64) exposed by a BLAKE2F accelerator result. -/
def outputBytesList (result : Blake2fResult) : List Byte :=
  Blake2fResultBridge.outputBytesList result.output

/--
Pure execution boundary for the BLAKE2F ECALL. The compression itself is
supplied by the accelerator model; this bridge fixes the request/result
shape, the status return, and the output bytes extracted from the returned
state buffer.

Distinctive token: Blake2fEcallBridge.executeBlake2fEcall.
-/
def executeBlake2fEcall
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (request : Blake2fRequest) : Blake2fResult :=
  let result := accelerator request.input
  { status := result.1, output := result.2 }

theorem requestFromInput_selector
    (input : Blake2fInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = blake2fSelector := rfl

theorem requestFromInput_input
    (input : Blake2fInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeBlake2fEcall_status
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (request : Blake2fRequest) :
    (executeBlake2fEcall accelerator request).status =
      (accelerator request.input).1 := by
  rfl

theorem executeBlake2fEcall_output
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (request : Blake2fRequest) :
    (executeBlake2fEcall accelerator request).output =
      (accelerator request.input).2 := by
  rfl

theorem executeBlake2fEcall_outputBytes
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (request : Blake2fRequest) :
    outputBytesList (executeBlake2fEcall accelerator request) =
      Blake2fResultBridge.outputBytesList (accelerator request.input).2 := by
  rfl

theorem executeBlake2fEcall_fromMemory_outputBytes
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (memory : Blake2fInputBridge.MemoryReader)
    (rounds : UInt32) (hStart mStart tStart : Nat) (f : Byte) :
    outputBytesList
        (executeBlake2fEcall accelerator
          (requestFromInput
            (Blake2fInputBridge.blake2fInputFromMemory
              memory rounds hStart mStart tStart f))) =
      Blake2fResultBridge.outputBytesList
        (accelerator
          (Blake2fInputBridge.blake2fInputFromMemory
            memory rounds hStart mStart tStart f)).2 := by
  rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`KeccakStatusBridge.statusWord` and `Sha256EcallBridge.statusWord`. The
accelerator places the `zkvm_status` return code in `a0` after the ECALL;
this projection extracts that word from a `Blake2fResult` for postcondition
reasoning. -/
def statusWord (result : Blake2fResult) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Blake2fResult} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Blake2fResult} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Blake2fResult) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Blake2fResult) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeBlake2fEcall`: the returned `a0` word is
the accelerator-supplied status encoded via `zkvmStatusToWord`. -/
theorem executeBlake2fEcall_statusWord
    (accelerator : Blake2fInputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Blake2fResultBridge.AcceleratorOutput)
    (request : Blake2fRequest) :
    statusWord (executeBlake2fEcall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).1 := by
  rfl

end Blake2fEcallBridge

end EvmAsm.EL
