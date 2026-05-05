/-
  EvmAsm.EL.Conformance.Code

  Initial Lean-side conformance vector for executable code helpers
  (GH #125 / GH #107 / GH #118).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.Code.CopyExec

namespace EvmAsm.EL
namespace Conformance
namespace Code

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a CODECOPY executable-helper conformance vector. -/
structure CodeCopyInput where
  code : List (BitVec 8)
  destOffset : EvmWord
  codeOffset : EvmWord
  size : EvmWord
  deriving Repr

def runCodeCopy (input : CodeCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.CodeCopyExec.copiedBytesFromArgs
    input.code
    (EvmAsm.Evm64.CodeCopyArgs.copyArgs
      input.destOffset input.codeOffset input.size)

/-- CODECOPY zero-pads bytes copied past the end of code.
    Distinctive token: codeCopyZeroPadVector #125 #107 #118. -/
def codeCopyZeroPadVector :
    TestVector CodeCopyInput (List (BitVec 8)) :=
  { id := "codecopy-zero-pad"
    input :=
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 }
    expected := .value [(0xaa : BitVec 8), 0, 0, 0] }

theorem runCodeCopy_zeroPad :
    runCodeCopy
      { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
        destOffset := 64
        codeOffset := 1
        size := 4 } =
      [(0xaa : BitVec 8), 0, 0, 0] := rfl

theorem codeCopyZeroPadVector_passed :
    checkVector runCodeCopy codeCopyZeroPadVector = .passed :=
  checkVector_value_passed runCodeCopy
    "codecopy-zero-pad"
    { code := [(0x60 : BitVec 8), (0xaa : BitVec 8)]
      destOffset := (64 : EvmWord)
      codeOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xaa : BitVec 8), 0, 0, 0]
    runCodeCopy_zeroPad

/-- Compact checked-vector batch for code executable helpers.
    Distinctive token: codeConformanceVectors #125 #107 #118. -/
def codeConformanceVectors : List CheckResult :=
  [checkVector runCodeCopy codeCopyZeroPadVector]

theorem codeConformanceVectors_passed :
    codeConformanceVectors = [.passed] := by
  simp [codeConformanceVectors, codeCopyZeroPadVector_passed]

end Code
end Conformance
end EvmAsm.EL
