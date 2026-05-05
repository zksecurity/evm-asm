/-
  EvmAsm.EL.KeccakEcallBridge

  Pure zkVM KECCAK accelerator ECALL surface (GH #111).
-/

import EvmAsm.EL.KeccakInputBridge
import EvmAsm.EL.KeccakResultBridge

namespace EvmAsm.EL

namespace KeccakEcallBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Selector reserved for the KECCAK256 accelerator ECALL surface. -/
def keccakSelector : BitVec 64 := 0x20

/-- ECALL request passed to the zkVM KECCAK accelerator. -/
structure KeccakRequest where
  selector : BitVec 64
  input : KeccakInputBridge.AcceleratorInput
  deriving Repr

/-- ECALL result returned by the zkVM KECCAK accelerator. -/
structure KeccakResult where
  output : KeccakResultBridge.AcceleratorOutput

/-- Build the KECCAK accelerator request from already-loaded input bytes. -/
def requestFromInput (input : KeccakInputBridge.AcceleratorInput) : KeccakRequest :=
  { selector := keccakSelector, input := input }

/-- Stack word exposed by a successful KECCAK accelerator result. -/
def stackWordFromResult (result : KeccakResult) : EvmWord :=
  KeccakResultBridge.stackWordFromAcceleratorOutput result.output

/--
Pure execution boundary for the KECCAK ECALL. The hash computation itself is
supplied by the accelerator model; this bridge fixes the request/result shape
and the stack word extracted from the returned output buffer.

Distinctive token: KeccakEcallBridge.executeKeccakEcall #111.
-/
def executeKeccakEcall
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) : KeccakResult :=
  { output := accelerator request.input }

theorem requestFromInput_selector (input : KeccakInputBridge.AcceleratorInput) :
    (requestFromInput input).selector = keccakSelector := rfl

theorem requestFromInput_input (input : KeccakInputBridge.AcceleratorInput) :
    (requestFromInput input).input = input := rfl

theorem executeKeccakEcall_output
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    (executeKeccakEcall accelerator request).output = accelerator request.input := rfl

theorem executeKeccakEcall_stackWord
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (request : KeccakRequest) :
    stackWordFromResult (executeKeccakEcall accelerator request) =
      KeccakResultBridge.stackWordFromAcceleratorOutput
        (accelerator request.input) := rfl

theorem executeKeccakEcall_fromArgs_stackWord
    (accelerator : KeccakInputBridge.AcceleratorInput →
      KeccakResultBridge.AcceleratorOutput)
    (memory : KeccakInputBridge.MemoryReader)
    (args : EvmAsm.Evm64.KeccakArgs.Args) :
    stackWordFromResult
        (executeKeccakEcall accelerator
          (requestFromInput (KeccakInputBridge.acceleratorInputFromArgs memory args))) =
      KeccakResultBridge.stackWordFromAcceleratorOutput
        (accelerator (KeccakInputBridge.acceleratorInputFromArgs memory args)) := rfl

end KeccakEcallBridge

end EvmAsm.EL
