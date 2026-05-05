/-
  EvmAsm.EL.Conformance.Call

  Compact Lean-side conformance vectors for CALL output bridge helpers
  (GH #125 / GH #114).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.CallOutputBridge

namespace EvmAsm.EL
namespace Conformance
namespace Call

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange

/-- Input shape for CALL output-copy executable-helper conformance vectors. -/
structure CallOutputInput where
  result : CallResult
  range : MemoryRange

def mkRange (offset size : EvmWord) : MemoryRange :=
  { offset := offset, size := size }

def runCallOutput (input : CallOutputInput) : List Byte :=
  EvmAsm.EL.CallOutputBridge.copiedOutputForRange input.result input.range

/-- Successful CALL output is clipped to the caller-provided output size.
    Distinctive token: Call.callOutputClipVector #125 #114. -/
def callOutputClipVector : TestVector CallOutputInput (List Byte) :=
  { id := "call-output-clip"
    input :=
      { result :=
          { status := .success, state := WorldState.empty,
            output := [(0xaa : Byte), 0xbb, 0xcc], gasRemaining := 7 }
        range := mkRange 0 2 }
    expected := .value [(0xaa : Byte), 0xbb] }

/-- Failed CALL exposes no copied output, regardless of result bytes. -/
def callOutputFailureVector : TestVector CallOutputInput (List Byte) :=
  { id := "call-output-failure-empty"
    input :=
      { result :=
          { status := .failure, state := WorldState.empty,
            output := [(0xaa : Byte), 0xbb], gasRemaining := 0 }
        range := mkRange 0 2 }
    expected := .value [] }

theorem runCallOutput_clip :
    runCallOutput
      { result :=
          { status := .success, state := WorldState.empty,
            output := [(0xaa : Byte), 0xbb, 0xcc], gasRemaining := 7 }
        range := mkRange 0 2 } =
      [(0xaa : Byte), 0xbb] := rfl

theorem runCallOutput_failure :
    runCallOutput
      { result :=
          { status := .failure, state := WorldState.empty,
            output := [(0xaa : Byte), 0xbb], gasRemaining := 0 }
        range := mkRange 0 2 } = [] := by
  simp [runCallOutput, EvmAsm.EL.CallOutputBridge.copiedOutputForRange,
    EvmAsm.EL.MessageCallExecution.propagatedOutput]

theorem callOutputClipVector_passed :
    checkVector runCallOutput callOutputClipVector = .passed :=
  checkVector_value_passed runCallOutput
    "call-output-clip"
    { result :=
        { status := .success, state := WorldState.empty,
          output := [(0xaa : Byte), 0xbb, 0xcc], gasRemaining := 7 }
      range := mkRange 0 2 }
    [(0xaa : Byte), 0xbb]
    runCallOutput_clip

theorem callOutputFailureVector_passed :
    checkVector runCallOutput callOutputFailureVector = .passed :=
  checkVector_value_passed runCallOutput
    "call-output-failure-empty"
    { result :=
        { status := .failure, state := WorldState.empty,
          output := [(0xaa : Byte), 0xbb], gasRemaining := 0 }
      range := mkRange 0 2 }
    []
    runCallOutput_failure

/-- Compact checked-vector batch for CALL output bridge helpers.
    Distinctive token: Call.callOutputConformanceVectors #125 #114. -/
def callOutputConformanceVectors : List CheckResult :=
  [ checkVector runCallOutput callOutputClipVector
  , checkVector runCallOutput callOutputFailureVector
  ]

theorem callOutputConformanceVectors_passed :
    callOutputConformanceVectors = [.passed, .passed] := by
  simp [callOutputConformanceVectors, callOutputClipVector_passed,
    callOutputFailureVector_passed]

end Call
end Conformance
end EvmAsm.EL
