/-
  EvmAsm.EL.Ripemd160EcallBridge

  Pure zkVM RIPEMD160 accelerator ECALL surface for the Ethereum RIPEMD160
  precompile (address 0x03).
-/

import EvmAsm.EL.Ripemd160InputBridge
import EvmAsm.EL.Ripemd160ResultBridge
import EvmAsm.Evm64.Accelerators.Status
import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm.EL

namespace Ripemd160EcallBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Selector reserved for the `zkvm_ripemd160` accelerator ECALL surface. -/
def ripemd160Selector : BitVec 64 := EvmAsm.Rv64.SyscallIdWord.ripemd160

/-- ECALL request passed to the zkVM RIPEMD160 accelerator. -/
structure Ripemd160Request where
  selector : BitVec 64
  input : Ripemd160InputBridge.AcceleratorInput
  deriving Repr

/-- ECALL result returned by the zkVM RIPEMD160 accelerator. -/
structure Ripemd160Result where
  status : EvmAsm.Accelerators.ZkvmStatus
  output : Ripemd160ResultBridge.AcceleratorOutput

/-- Build the RIPEMD160 accelerator request from already-loaded input bytes. -/
def requestFromInput (input : Ripemd160InputBridge.AcceleratorInput) : Ripemd160Request :=
  { selector := ripemd160Selector, input := input }

/-- Stack word exposed by a successful RIPEMD160 accelerator result. -/
def stackWordFromResult (result : Ripemd160Result) : EvmWord :=
  Ripemd160ResultBridge.stackWordFromAcceleratorOutput result.output

/--
Pure execution boundary for the RIPEMD160 ECALL. The digest computation itself
is supplied by the accelerator model; this bridge fixes the request/result
shape, the status return, and the stack word extracted from the returned
output buffer.

Distinctive token: Ripemd160EcallBridge.executeRipemd160Ecall.
-/
def executeRipemd160Ecall
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (request : Ripemd160Request) : Ripemd160Result :=
  let result := accelerator request.input
  { status := result.1, output := result.2 }

theorem requestFromInput_selector (input : Ripemd160InputBridge.AcceleratorInput) :
    (requestFromInput input).selector = ripemd160Selector := rfl

theorem requestFromInput_input (input : Ripemd160InputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeRipemd160Ecall_status
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (request : Ripemd160Request) :
    (executeRipemd160Ecall accelerator request).status = (accelerator request.input).1 := by
  rfl

theorem executeRipemd160Ecall_output
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (request : Ripemd160Request) :
    (executeRipemd160Ecall accelerator request).output = (accelerator request.input).2 := by
  rfl

theorem executeRipemd160Ecall_stackWord
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (request : Ripemd160Request) :
    stackWordFromResult (executeRipemd160Ecall accelerator request) =
      Ripemd160ResultBridge.stackWordFromAcceleratorOutput
        (accelerator request.input).2 := by
  rfl

theorem executeRipemd160Ecall_fromMemory_stackWord
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (memory : Ripemd160InputBridge.MemoryReader) (start size : Nat) :
    stackWordFromResult
        (executeRipemd160Ecall accelerator
          (requestFromInput
            (Ripemd160InputBridge.acceleratorInputFromMemory memory start size))) =
      Ripemd160ResultBridge.stackWordFromAcceleratorOutput
        (accelerator
          (Ripemd160InputBridge.acceleratorInputFromMemory memory start size)).2 := by
  rfl

/-- RV64 `a0` return-register `Word` for the accelerator status, mirroring
`KeccakStatusBridge.statusWord` and `Sha256EcallBridge.statusWord`. The
accelerator places the `zkvm_status` return code in `a0` after the ECALL;
this projection extracts that word from a `Ripemd160Result` for postcondition
reasoning. -/
def statusWord (result : Ripemd160Result) : BitVec 64 :=
  EvmAsm.Rv64.zkvmStatusToWord result.status

theorem statusWord_eok
    {result : Ripemd160Result} (h_status : result.status = .eok) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

theorem statusWord_efail
    {result : Ripemd160Result} (h_status : result.status = .efail) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEfailWord := by
  show EvmAsm.Rv64.zkvmStatusToWord result.status = _
  rw [h_status]; rfl

/-- The `a0` word is `ZKVM_EOK` iff the accelerator reported success. -/
theorem statusWord_eq_eokWord_iff (result : Ripemd160Result) :
    statusWord result = EvmAsm.Rv64.zkvmStatusEokWord ↔ result.status = .eok := by
  cases h_st : result.status with
  | eok => simp [statusWord_eok h_st]
  | efail =>
    rw [statusWord_efail h_st]
    constructor
    · intro h; exact absurd h.symm EvmAsm.Rv64.zkvmStatusEokWord_ne_efailWord
    · intro h; simp at h

/-- The `a0` word decodes back to the original status. -/
theorem zkvmStatusFromWord?_statusWord (result : Ripemd160Result) :
    EvmAsm.Rv64.zkvmStatusFromWord? (statusWord result) = some result.status :=
  EvmAsm.Rv64.zkvmStatusFromWord?_toWord result.status

/-- Push `statusWord` through `executeRipemd160Ecall`: the returned `a0` word
is the accelerator-supplied status encoded via `zkvmStatusToWord`. -/
theorem executeRipemd160Ecall_statusWord
    (accelerator : Ripemd160InputBridge.AcceleratorInput →
      EvmAsm.Accelerators.ZkvmStatus × Ripemd160ResultBridge.AcceleratorOutput)
    (request : Ripemd160Request) :
    statusWord (executeRipemd160Ecall accelerator request) =
      EvmAsm.Rv64.zkvmStatusToWord (accelerator request.input).1 := by
  rfl

end Ripemd160EcallBridge

end EvmAsm.EL
