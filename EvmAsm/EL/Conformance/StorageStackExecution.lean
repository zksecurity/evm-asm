/-
  EvmAsm.EL.Conformance.StorageStackExecution

  Lean-side conformance vectors for the SLOAD/SSTORE stack execution bridge
  (GH #110 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.StorageStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace StorageStackExecution

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev StorageKind := EvmAsm.Evm64.StorageArgs.Kind
abbrev StorageStackState :=
  EvmAsm.EL.StorageStackExecutionBridge.StorageStackState
abbrev StorageAccessList :=
  EvmAsm.EL.StorageStackExecutionBridge.StorageAccessList

deriving instance DecidableEq for
  EvmAsm.EL.StorageStackExecutionBridge.StorageStackState

structure StorageStackInput where
  kind : StorageKind
  world : WorldState
  accesses : StorageAccessList
  address : Address
  stackState : StorageStackState

def runStorageStack? (input : StorageStackInput) : Option StorageStackState :=
  EvmAsm.EL.StorageStackExecutionBridge.runStorageStack?
    input.kind input.world input.accesses input.address input.stackState

def storageStackSloadVector : TestVector StorageStackInput StorageStackState :=
  { id := "storage-stack-sload"
    input :=
      { kind := .sload
        world := WorldState.empty
        accesses := []
        address := 0x1234
        stackState := { stack := [7, 99] } }
    expected := .value { stack := [0, 99] } }

def storageStackSstoreVector : TestVector StorageStackInput StorageStackState :=
  { id := "storage-stack-sstore"
    input :=
      { kind := .sstore
        world := WorldState.empty
        accesses := []
        address := 0x1234
        stackState := { stack := [7, 42, 99] } }
    expected := .value { stack := [99] } }

theorem runStorageStack?_sload_empty :
    runStorageStack?
      { kind := .sload
        world := WorldState.empty
        accesses := []
        address := (0x1234 : Address)
        stackState := { stack := [(7 : EvmWord), (99 : EvmWord)] } } =
      some { stack := [(0 : EvmWord), (99 : EvmWord)] } := rfl

theorem runStorageStack?_sstore_empty :
    runStorageStack?
      { kind := .sstore
        world := WorldState.empty
        accesses := []
        address := (0x1234 : Address)
        stackState := { stack := [(7 : EvmWord), (42 : EvmWord), (99 : EvmWord)] } } =
      some { stack := [(99 : EvmWord)] } := rfl

theorem storageStackSloadVector_passed :
    checkVector? runStorageStack? storageStackSloadVector = .passed :=
  checkVector?_some_passed runStorageStack?
    "storage-stack-sload"
    { kind := .sload
      world := WorldState.empty
      accesses := []
      address := (0x1234 : Address)
      stackState := { stack := [(7 : EvmWord), (99 : EvmWord)] } }
    { stack := [(0 : EvmWord), (99 : EvmWord)] }
    runStorageStack?_sload_empty

theorem storageStackSstoreVector_passed :
    checkVector? runStorageStack? storageStackSstoreVector = .passed :=
  checkVector?_some_passed runStorageStack?
    "storage-stack-sstore"
    { kind := .sstore
      world := WorldState.empty
      accesses := []
      address := (0x1234 : Address)
      stackState :=
        { stack := [(7 : EvmWord), (42 : EvmWord), (99 : EvmWord)] } }
    { stack := [(99 : EvmWord)] }
    runStorageStack?_sstore_empty

/-- Compact checked-vector batch for storage stack execution.
    Distinctive token:
    StorageStackExecutionConformance.storageStackConformanceVectors #110 #125. -/
def storageStackConformanceVectors : List CheckResult :=
  [ checkVector? runStorageStack? storageStackSloadVector
  , checkVector? runStorageStack? storageStackSstoreVector
  ]

theorem storageStackConformanceVectors_passed :
    storageStackConformanceVectors = [.passed, .passed] := by
  simp [storageStackConformanceVectors, storageStackSloadVector_passed,
    storageStackSstoreVector_passed]

end StorageStackExecution
end Conformance
end EvmAsm.EL
