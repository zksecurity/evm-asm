/-
  EvmAsm.EL.Conformance.ReturnData

  Initial Lean-side conformance vector for executable returndata helpers
  (GH #125 / GH #114).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.ReturnData.CopyExec

namespace EvmAsm.EL
namespace Conformance
namespace ReturnData

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a RETURNDATACOPY executable-helper conformance vector. -/
structure ReturnDataCopyInput where
  data : List (BitVec 8)
  destOffset : EvmWord
  dataOffset : EvmWord
  size : EvmWord
  deriving Repr

def runReturnDataCopy (input : ReturnDataCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.ReturnDataCopyExec.copiedBytesFromArgs
    input.data
    (EvmAsm.Evm64.ReturnDataCopyArgs.copyArgs
      input.destOffset input.dataOffset input.size)

/-- RETURNDATACOPY zero-pads bytes copied past the end of returndata.
    Distinctive token: returnDataCopyZeroPadVector #125 #114. -/
def returnDataCopyZeroPadVector :
    TestVector ReturnDataCopyInput (List (BitVec 8)) :=
  { id := "returndatacopy-zero-pad"
    input :=
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 }
    expected := .value [(0xbb : BitVec 8), 0, 0, 0] }

theorem runReturnDataCopy_zeroPad :
    runReturnDataCopy
      { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
        destOffset := 32
        dataOffset := 1
        size := 4 } =
      [(0xbb : BitVec 8), 0, 0, 0] := rfl

theorem returnDataCopyZeroPadVector_passed :
    checkVector runReturnDataCopy returnDataCopyZeroPadVector = .passed :=
  checkVector_value_passed runReturnDataCopy
    "returndatacopy-zero-pad"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)]
      destOffset := (32 : EvmWord)
      dataOffset := (1 : EvmWord)
      size := (4 : EvmWord) }
    [(0xbb : BitVec 8), 0, 0, 0]
    runReturnDataCopy_zeroPad

/-- Compact checked-vector batch for returndata executable helpers.
    Distinctive token: returnDataConformanceVectors #125 #114. -/
def returnDataConformanceVectors : List CheckResult :=
  [checkVector runReturnDataCopy returnDataCopyZeroPadVector]

theorem returnDataConformanceVectors_passed :
    returnDataConformanceVectors = [.passed] := by
  simp [returnDataConformanceVectors, returnDataCopyZeroPadVector_passed]

end ReturnData
end Conformance
end EvmAsm.EL
