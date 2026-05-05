/-
  EvmAsm.EL.Conformance.KeccakStackExecution

  Lean-side conformance vector for the KECCAK256 stack execution bridge
  (GH #111 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.KeccakStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace KeccakStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev AcceleratorInput := EvmAsm.EL.KeccakInputBridge.AcceleratorInput
abbrev AcceleratorOutput := EvmAsm.EL.KeccakResultBridge.AcceleratorOutput

structure KeccakStackInput where
  memory : List Byte
  stack : List EvmWord
  deriving Repr

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def zeroHash : EvmAsm.EL.KeccakResultBridge.HashBytes :=
  fun _ => 0

def vectorAccelerator (input : AcceleratorInput) : AcceleratorOutput :=
  if input.bytes = [(0xbb : Byte), 0xcc] then
    { hash := zeroHash }
  else
    { hash := fun _ => 0xff }

def runKeccakStack? (input : KeccakStackInput) : Option (List EvmWord) :=
  EvmAsm.EL.KeccakStackExecutionBridge.runKeccakStack?
    vectorAccelerator (readByteAt input.memory) input.stack

def keccakStackVector : TestVector KeccakStackInput (List EvmWord) :=
  { id := "keccak-stack-vector"
    input :=
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] }
    expected := .value [(0 : EvmWord), 99] }

theorem runKeccakStack?_vector :
    runKeccakStack?
      { memory := [(0xaa : Byte), 0xbb, 0xcc]
        stack := [(1 : EvmWord), 2, 99] } =
      some [(0 : EvmWord), 99] := by
  native_decide

theorem keccakStackVector_passed :
    checkVector? runKeccakStack? keccakStackVector = .passed :=
  checkVector?_some_passed runKeccakStack?
    "keccak-stack-vector"
    { memory := [(0xaa : Byte), 0xbb, 0xcc]
      stack := [(1 : EvmWord), 2, 99] }
    [(0 : EvmWord), 99]
    runKeccakStack?_vector

/-- Compact checked-vector batch for KECCAK stack execution.
    Distinctive token:
    KeccakStackExecutionConformance.keccakStackConformanceVectors #111 #125. -/
def keccakStackConformanceVectors : List CheckResult :=
  [checkVector? runKeccakStack? keccakStackVector]

theorem keccakStackConformanceVectors_passed :
    keccakStackConformanceVectors = [.passed] := by
  simp [keccakStackConformanceVectors, keccakStackVector_passed]

end KeccakStackExecution
end Conformance
end EvmAsm.EL
