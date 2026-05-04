/-
  EvmAsm.EL.Conformance.Calldata

  Initial Lean-side conformance vectors for executable calldata helpers
  (GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.Calldata.Basic
import EvmAsm.Evm64.Calldata.Size

namespace EvmAsm.EL
namespace Conformance
namespace Calldata

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for a CALLDATALOAD executable-helper conformance vector. -/
structure CallDataLoadInput where
  data : List (BitVec 8)
  offset : Nat
  deriving Repr

/-- Input shape for a CALLDATASIZE executable-helper conformance vector. -/
structure CallDataSizeInput where
  data : List (BitVec 8)
  deriving Repr

/-- Input shape for a CALLDATACOPY executable-helper conformance vector. -/
structure CallDataCopyInput where
  data : List (BitVec 8)
  dataOffset : Nat
  size : Nat
  deriving Repr

def runCallDataLoad (input : CallDataLoadInput) : EvmWord :=
  EvmAsm.Evm64.Calldata.callDataLoadWord input.data input.offset

def runCallDataSize (input : CallDataSizeInput) : EvmWord :=
  EvmAsm.Evm64.Calldata.callDataSizeOf input.data

def runCallDataCopy (input : CallDataCopyInput) : List (BitVec 8) :=
  EvmAsm.Evm64.Calldata.callDataCopyBytes
    input.data input.dataOffset input.size

/-- CALLDATALOAD reads zero when the requested 32-byte window starts at the
    end of calldata. Distinctive token: callDataLoadOutOfBoundsVector. -/
def callDataLoadOutOfBoundsVector : TestVector CallDataLoadInput EvmWord :=
  { id := "calldataload-oob-zero"
    input := { data := [(0x12 : BitVec 8)], offset := 1 }
    expected := .value 0 }

/-- CALLDATASIZE pushes the byte length of calldata as an EVM word. -/
def callDataSizeTwoBytesVector : TestVector CallDataSizeInput EvmWord :=
  { id := "calldatasize-two-bytes"
    input := { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] }
    expected := .value 2 }

/-- CALLDATACOPY zero-pads bytes copied past the end of calldata.
    Distinctive token: callDataCopyZeroPadVector. -/
def callDataCopyZeroPadVector :
    TestVector CallDataCopyInput (List (BitVec 8)) :=
  { id := "calldatacopy-zero-pad"
    input := { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 }
    expected := .value [(0xaa : BitVec 8), 0, 0] }

theorem runCallDataLoad_outOfBounds :
    runCallDataLoad { data := [(0x12 : BitVec 8)], offset := 1 } = 0 := by
  exact EvmAsm.Evm64.Calldata.callDataLoadWord_of_ge_length (by decide)

theorem runCallDataSize_twoBytes :
    runCallDataSize { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] } =
      (2 : EvmWord) := rfl

theorem runCallDataCopy_zeroPad :
    runCallDataCopy
      { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 } =
      [(0xaa : BitVec 8), 0, 0] := rfl

theorem callDataLoadOutOfBoundsVector_passed :
    checkVector runCallDataLoad callDataLoadOutOfBoundsVector = .passed :=
  checkVector_value_passed runCallDataLoad
    "calldataload-oob-zero"
    { data := [(0x12 : BitVec 8)], offset := 1 }
    (0 : EvmWord)
    runCallDataLoad_outOfBounds

theorem callDataSizeTwoBytesVector_passed :
    checkVector runCallDataSize callDataSizeTwoBytesVector = .passed :=
  checkVector_value_passed runCallDataSize
    "calldatasize-two-bytes"
    { data := [(0xaa : BitVec 8), (0xbb : BitVec 8)] }
    (2 : EvmWord)
    runCallDataSize_twoBytes

theorem callDataCopyZeroPadVector_passed :
    checkVector runCallDataCopy callDataCopyZeroPadVector = .passed :=
  checkVector_value_passed runCallDataCopy
    "calldatacopy-zero-pad"
    { data := [(0xaa : BitVec 8)], dataOffset := 0, size := 3 }
    [(0xaa : BitVec 8), 0, 0]
    runCallDataCopy_zeroPad

/-- Compact initial checked-vector batch for calldata executable helpers.
    Distinctive token: calldataConformanceVectors. -/
def calldataConformanceVectors : List CheckResult :=
  [ checkVector runCallDataLoad callDataLoadOutOfBoundsVector
  , checkVector runCallDataSize callDataSizeTwoBytesVector
  , checkVector runCallDataCopy callDataCopyZeroPadVector
  ]

theorem calldataConformanceVectors_passed :
    calldataConformanceVectors = [.passed, .passed, .passed] := by
  simp [calldataConformanceVectors, callDataLoadOutOfBoundsVector_passed,
    callDataSizeTwoBytesVector_passed, callDataCopyZeroPadVector_passed]

end Calldata
end Conformance
end EvmAsm.EL
