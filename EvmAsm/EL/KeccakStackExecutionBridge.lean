/-
  EvmAsm.EL.KeccakStackExecutionBridge

  Pure stack-to-accelerator execution bridge for KECCAK256 (GH #111).
-/

import EvmAsm.Evm64.KeccakArgsStackDecode
import EvmAsm.EL.KeccakEcallBridge

namespace EvmAsm.EL

namespace KeccakStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev MemoryReader := KeccakInputBridge.MemoryReader
abbrev AcceleratorInput := KeccakInputBridge.AcceleratorInput
abbrev AcceleratorOutput := KeccakResultBridge.AcceleratorOutput
abbrev KeccakRequest := KeccakEcallBridge.KeccakRequest
abbrev KeccakResult := KeccakEcallBridge.KeccakResult

/-- KECCAK accelerator model used by the pure execution bridge. -/
abbrev Accelerator := AcceleratorInput -> AcceleratorOutput

/-- Build the KECCAK ECALL request from decoded stack words and memory.
    Distinctive token: KeccakStackExecutionBridge.runKeccakStack? #111. -/
def requestFromStack? (memory : MemoryReader) (stack : List EvmWord) :
    Option KeccakRequest :=
  match EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack? stack with
  | some args =>
      some (KeccakEcallBridge.requestFromInput
        (KeccakInputBridge.acceleratorInputFromArgs memory args))
  | none => none

/-- Execute the KECCAK accelerator from stack-decoded operands. -/
def resultFromStack? (accelerator : Accelerator)
    (memory : MemoryReader) (stack : List EvmWord) : Option KeccakResult :=
  (requestFromStack? memory stack).map
    (fun request => KeccakEcallBridge.executeKeccakEcall accelerator request)

/--
Run the pure KECCAK stack effect: pop `offset, size`, hash the requested memory
slice with the accelerator, then push the returned 256-bit hash.
-/
def runKeccakStack? (accelerator : Accelerator)
    (memory : MemoryReader) : List EvmWord -> Option (List EvmWord)
  | offset :: size :: rest =>
      let args := EvmAsm.Evm64.KeccakArgs.keccakArgs offset size
      let input := KeccakInputBridge.acceleratorInputFromArgs memory args
      let result := KeccakEcallBridge.executeKeccakEcall accelerator
        (KeccakEcallBridge.requestFromInput input)
      some (KeccakEcallBridge.stackWordFromResult result :: rest)
  | _ => none

theorem requestFromStack?_some
    (memory : MemoryReader) (offset size : EvmWord) (rest : List EvmWord) :
    requestFromStack? memory (offset :: size :: rest) =
      some (KeccakEcallBridge.requestFromInput
        (KeccakInputBridge.acceleratorInputFromArgs memory
          (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size))) := rfl

/--
The stack-to-request bridge succeeds exactly when the stack contains the
`offset, size` pair required by KECCAK256.

Distinctive token: KeccakStackExecutionBridge.requestFromStack?_eq_some_iff #111.
-/
theorem requestFromStack?_eq_some_iff
    (memory : MemoryReader) (stack : List EvmWord) (request : KeccakRequest) :
    requestFromStack? memory stack = some request ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          request =
            KeccakEcallBridge.requestFromInput
              (KeccakInputBridge.acceleratorInputFromArgs memory
                (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size)) := by
  constructor
  · intro h_request
    cases stack with
    | nil =>
        simp [requestFromStack?,
          EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_request
    | cons offset tail =>
        cases tail with
        | nil =>
            simp [requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_request
        | cons size rest =>
            simp [requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_request
            cases h_request
            exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

@[simp] theorem requestFromStack?_nil (memory : MemoryReader) :
    requestFromStack? memory [] = none := rfl

@[simp] theorem requestFromStack?_singleton
    (memory : MemoryReader) (offset : EvmWord) :
    requestFromStack? memory [offset] = none := rfl

/--
The stack-to-request bridge fails exactly on stacks missing the KECCAK256
`offset, size` pair.

Distinctive token: KeccakStackExecutionBridge.requestFromStack?_eq_none_iff #111.
-/
theorem requestFromStack?_eq_none_iff
    (memory : MemoryReader) (stack : List EvmWord) :
    requestFromStack? memory stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_request
    cases stack with
    | nil => simp
    | cons offset tail =>
        cases tail with
        | nil => simp
        | cons size rest =>
            simp [requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_request
  · intro h_len
    cases stack with
    | nil => rfl
    | cons offset tail =>
        cases tail with
        | nil => rfl
        | cons size rest =>
            simp at h_len
            omega

theorem resultFromStack?_some
    (accelerator : Accelerator) (memory : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    resultFromStack? accelerator memory (offset :: size :: rest) =
      some (KeccakEcallBridge.executeKeccakEcall accelerator
        (KeccakEcallBridge.requestFromInput
          (KeccakInputBridge.acceleratorInputFromArgs memory
            (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size)))) := rfl

theorem resultFromStack?_eq_some_iff
    (accelerator : Accelerator) (memory : MemoryReader)
    (stack : List EvmWord) (result : KeccakResult) :
    resultFromStack? accelerator memory stack = some result ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          result =
            KeccakEcallBridge.executeKeccakEcall accelerator
              (KeccakEcallBridge.requestFromInput
                (KeccakInputBridge.acceleratorInputFromArgs memory
                  (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size))) := by
  constructor
  · intro h_result
    cases stack with
    | nil =>
        simp [resultFromStack?, requestFromStack?,
          EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_result
    | cons offset tail =>
        cases tail with
        | nil =>
            simp [resultFromStack?, requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_result
        | cons size rest =>
            simp [resultFromStack?, requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_result
            cases h_result
            exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem resultFromStack?_eq_none_iff
    (accelerator : Accelerator) (memory : MemoryReader)
    (stack : List EvmWord) :
    resultFromStack? accelerator memory stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_result
    cases stack with
    | nil => simp
    | cons offset tail =>
        cases tail with
        | nil => simp
        | cons size rest =>
            simp [resultFromStack?, requestFromStack?,
              EvmAsm.Evm64.KeccakArgsStackDecode.decodeKeccakStack?] at h_result
  · intro h_len
    cases stack with
    | nil => rfl
    | cons offset tail =>
        cases tail with
        | nil => rfl
        | cons size rest =>
            simp at h_len
            omega

theorem runKeccakStack?_some
    (accelerator : Accelerator) (memory : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    runKeccakStack? accelerator memory (offset :: size :: rest) =
      some
        (KeccakResultBridge.stackWordFromAcceleratorOutput
            (accelerator
              (KeccakInputBridge.acceleratorInputFromArgs memory
                (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size))) :: rest) := rfl

theorem runKeccakStack?_eq_some_iff
    (accelerator : Accelerator) (memory : MemoryReader)
    (stack out : List EvmWord) :
    runKeccakStack? accelerator memory stack = some out ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧
          out =
            KeccakResultBridge.stackWordFromAcceleratorOutput
              (accelerator
                (KeccakInputBridge.acceleratorInputFromArgs memory
                  (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size))) :: rest := by
  constructor
  · intro h_run
    cases stack with
    | nil => simp [runKeccakStack?] at h_run
    | cons offset tail =>
        cases tail with
        | nil => simp [runKeccakStack?] at h_run
        | cons size rest =>
            simp [runKeccakStack?] at h_run
            cases h_run
            exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

@[simp] theorem runKeccakStack?_nil
    (accelerator : Accelerator) (memory : MemoryReader) :
    runKeccakStack? accelerator memory [] = none := rfl

@[simp] theorem runKeccakStack?_singleton
    (accelerator : Accelerator) (memory : MemoryReader) (offset : EvmWord) :
    runKeccakStack? accelerator memory [offset] = none := rfl

theorem runKeccakStack?_eq_none_iff
    (accelerator : Accelerator) (memory : MemoryReader)
    (stack : List EvmWord) :
    runKeccakStack? accelerator memory stack = none ↔ stack.length < 2 := by
  constructor
  · intro h_run
    cases stack with
    | nil => simp
    | cons offset tail =>
        cases tail with
        | nil => simp
        | cons size rest =>
            simp [runKeccakStack?] at h_run
  · intro h_len
    cases stack with
    | nil => rfl
    | cons offset tail =>
        cases tail with
        | nil => rfl
        | cons size rest =>
            simp at h_len
            omega

theorem runKeccakStack?_length
    {accelerator : Accelerator} {memory : MemoryReader}
    {stack out : List EvmWord}
    (h_run : runKeccakStack? accelerator memory stack = some out) :
    out.length + EvmAsm.Evm64.KeccakArgs.stackArgumentCount =
      stack.length + EvmAsm.Evm64.KeccakArgs.resultCount := by
  cases stack with
  | nil => simp at h_run
  | cons offset tail =>
      cases tail with
      | nil => simp at h_run
      | cons size rest =>
          simp [runKeccakStack?] at h_run
          cases h_run
          simp [EvmAsm.Evm64.KeccakArgs.stackArgumentCount,
            EvmAsm.Evm64.KeccakArgs.resultCount]

theorem runKeccakStack?_head?
    (accelerator : Accelerator) (memory : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    (runKeccakStack? accelerator memory (offset :: size :: rest)).map List.head? =
      some
        (some
          (KeccakResultBridge.stackWordFromAcceleratorOutput
            (accelerator
              (KeccakInputBridge.acceleratorInputFromArgs memory
                (EvmAsm.Evm64.KeccakArgs.keccakArgs offset size))))) := rfl

theorem runKeccakStack?_tail?
    (accelerator : Accelerator) (memory : MemoryReader)
    (offset size : EvmWord) (rest : List EvmWord) :
    (runKeccakStack? accelerator memory (offset :: size :: rest)).map List.tail? =
      some (some rest) := rfl

end KeccakStackExecutionBridge

end EvmAsm.EL
