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

/-- SSTORE requires both slot and value stack operands.
    Distinctive token: storageSstoreUnderflowConformanceVector #110 #125. -/
def storageSstoreUnderflowConformanceVector :
    TestVector StorageStackInput StorageStackState :=
  { id := "storage-stack-sstore-underflow"
    input :=
      { kind := .sstore
        world := WorldState.empty
        accesses := []
        address := 0x1234
        stackState := { stack := [7] } }
    expected := .error "stack-underflow" }

/-- SLOAD requires a slot stack operand.
    Distinctive token: storageSloadUnderflowConformanceVector #110 #125. -/
def storageSloadUnderflowConformanceVector :
    TestVector StorageStackInput StorageStackState :=
  { id := "storage-stack-sload-underflow"
    input :=
      { kind := .sload
        world := WorldState.empty
        accesses := []
        address := 0x1234
        stackState := { stack := [] } }
    expected := .error "stack-underflow" }

/-- Storage stack conformance inputs as reusable test vectors.
    Distinctive token:
    StorageStackExecutionConformance.storageStackConformanceTestVectors #110 #125. -/
def storageStackConformanceTestVectors :
    List (TestVector StorageStackInput StorageStackState) :=
  [ storageStackSloadVector
  , storageStackSstoreVector
  , storageSstoreUnderflowConformanceVector
  , storageSloadUnderflowConformanceVector
  ]

def storageStackConformanceVectorIds : List String :=
  storageStackConformanceTestVectors.map TestVector.id

theorem storageStackConformanceTestVectors_length :
    storageStackConformanceTestVectors.length = 4 := rfl

theorem storageStackConformanceVectorIds_eq :
    storageStackConformanceVectorIds =
      [ "storage-stack-sload"
      , "storage-stack-sstore"
      , "storage-stack-sstore-underflow"
      , "storage-stack-sload-underflow"
      ] := rfl

theorem storageStackConformanceVectorIds_length :
    storageStackConformanceVectorIds.length = 4 := rfl

theorem storageStackConformanceVectorIds_nodup :
    storageStackConformanceVectorIds.Nodup := by
  decide

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

theorem runStorageStack?_sstore_underflow :
    runStorageStack?
      { kind := .sstore
        world := WorldState.empty
        accesses := []
        address := (0x1234 : Address)
        stackState := { stack := [(7 : EvmWord)] } } =
      none := rfl

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

theorem storageSstoreUnderflowConformanceVector_errored :
    checkVector? runStorageStack? storageSstoreUnderflowConformanceVector =
      .errored "storage-stack-sstore-underflow" "stack-underflow" :=
  checkVector?_none_error runStorageStack?
    "storage-stack-sstore-underflow"
    "stack-underflow"
    { kind := .sstore
      world := WorldState.empty
      accesses := []
      address := (0x1234 : Address)
      stackState := { stack := [(7 : EvmWord)] } }
    runStorageStack?_sstore_underflow

theorem runStorageStack?_sload_underflow :
    runStorageStack?
      { kind := .sload
        world := WorldState.empty
        accesses := []
        address := (0x1234 : Address)
        stackState := { stack := [] } } =
      none := rfl

theorem storageSloadUnderflowConformanceVector_errored :
    checkVector? runStorageStack? storageSloadUnderflowConformanceVector =
      .errored "storage-stack-sload-underflow" "stack-underflow" :=
  checkVector?_none_error runStorageStack?
    "storage-stack-sload-underflow"
    "stack-underflow"
    { kind := .sload
      world := WorldState.empty
      accesses := []
      address := (0x1234 : Address)
      stackState := { stack := [] } }
    runStorageStack?_sload_underflow

/-- Compact checked-vector batch for storage stack execution.
    Distinctive token:
    StorageStackExecutionConformance.storageStackConformanceVectors #110 #125. -/
def storageStackConformanceVectors : List CheckResult :=
  checkBatch? runStorageStack? storageStackConformanceTestVectors

theorem storageStackConformanceVectors_passed :
    storageStackConformanceVectors =
      [ .passed
      , .passed
      , .errored "storage-stack-sstore-underflow" "stack-underflow"
      , .errored "storage-stack-sload-underflow" "stack-underflow"
      ] := by
  simp [storageStackConformanceVectors, storageStackConformanceTestVectors,
    storageStackSloadVector_passed, storageStackSstoreVector_passed,
    storageSstoreUnderflowConformanceVector_errored,
    storageSloadUnderflowConformanceVector_errored]

end StorageStackExecution
end Conformance
end EvmAsm.EL
