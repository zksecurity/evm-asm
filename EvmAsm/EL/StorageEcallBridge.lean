/-
  EvmAsm.EL.StorageEcallBridge

  Pure storage ECALL request/result surface for SLOAD and SSTORE (GH #110).
-/

import EvmAsm.EL.StorageAccessBridge

namespace EvmAsm.EL
namespace StorageEcallBridge

abbrev RvWord := BitVec 64
abbrev StorageAccessList := EvmAsm.Evm64.StorageAccess.StorageAccessList
abbrev Outcome := EvmAsm.Evm64.StorageAccessOutcome.Outcome

/-- Storage syscall selectors reserved for the EVM storage host interface. -/
inductive StorageSyscall where
  | sload
  | sstore
  deriving DecidableEq, Repr

/-- Selector value to put in the ECALL selector register for a storage syscall.
    These constants reserve a compact host-interface surface; later RV64 ECALL
    specs can connect them to concrete machine execution. -/
def selector : StorageSyscall → RvWord
  | .sload => 0xE0
  | .sstore => 0xE1

theorem selector_sload : selector .sload = (0xE0 : RvWord) := rfl

theorem selector_sstore : selector .sstore = (0xE1 : RvWord) := rfl

theorem selector_ne : selector .sload ≠ selector .sstore := by
  decide

/-- SLOAD ECALL payload after decoding machine registers into EL words. -/
structure SloadRequest where
  state : WorldState
  accesses : StorageAccessList
  address : Address
  slot : StorageKey

/-- SSTORE ECALL payload after decoding machine registers into EL words. -/
structure SstoreRequest where
  state : WorldState
  accesses : StorageAccessList
  address : Address
  slot : StorageKey
  newValue : Word256

/-- SLOAD ECALL result: loaded value plus updated access-list/gas outcome. -/
structure SloadResult where
  value : Word256
  outcome : Outcome

/-- SSTORE ECALL result: updated world state plus access-list/gas outcome. -/
structure SstoreResult where
  state : WorldState
  outcome : Outcome

/-- Execute the pure SLOAD ECALL request through the storage executable spec.
    Distinctive token: StorageEcallBridge.executeSloadEcall #110. -/
def executeSloadEcall (request : SloadRequest) : SloadResult :=
  let execution :=
    StorageAccessBridge.sloadExecution
      request.state request.accesses request.address request.slot
  { value := execution.value
    outcome := execution.outcome }

/-- Execute the pure SSTORE ECALL request through the storage executable spec. -/
def executeSstoreEcall (request : SstoreRequest) : SstoreResult :=
  let execution :=
    StorageAccessBridge.sstoreExecution
      request.state request.accesses request.address request.slot request.newValue
  { state := execution.state
    outcome := execution.outcome }

theorem executeSloadEcall_value (request : SloadRequest) :
    (executeSloadEcall request).value =
      Storage.sload request.state request.address request.slot := rfl

theorem executeSloadEcall_outcome (request : SloadRequest) :
    (executeSloadEcall request).outcome =
      EvmAsm.Evm64.StorageAccessOutcome.sloadOutcome request.accesses
        (StorageAccessBridge.accessKey request.address request.slot) := rfl

theorem executeSloadEcall_cost (request : SloadRequest) :
    (executeSloadEcall request).outcome.cost =
      EvmAsm.Evm64.StorageAccess.sloadDynamicCostForKey request.accesses
        (StorageAccessBridge.accessKey request.address request.slot) := rfl

theorem executeSloadEcall_warms (request : SloadRequest) :
    EvmAsm.Evm64.StorageAccess.isWarm
      (executeSloadEcall request).outcome.accesses
      (StorageAccessBridge.accessKey request.address request.slot) = true := by
  exact StorageAccessBridge.sloadExecution_warms
    request.state request.accesses request.address request.slot

theorem executeSstoreEcall_state (request : SstoreRequest) :
    (executeSstoreEcall request).state =
      Storage.sstore request.state request.address request.slot request.newValue := rfl

theorem executeSstoreEcall_outcome (request : SstoreRequest) :
    (executeSstoreEcall request).outcome =
      EvmAsm.Evm64.StorageAccessOutcome.sstoreOutcome request.accesses
        (StorageAccessBridge.accessKey request.address request.slot)
        (Storage.sload request.state request.address request.slot) request.newValue := rfl

theorem executeSstoreEcall_cost (request : SstoreRequest) :
    (executeSstoreEcall request).outcome.cost =
      EvmAsm.Evm64.StorageAccess.sstoreDynamicCostForKey request.accesses
        (StorageAccessBridge.accessKey request.address request.slot)
        (Storage.sload request.state request.address request.slot) request.newValue := rfl

theorem executeSstoreEcall_warms (request : SstoreRequest) :
    EvmAsm.Evm64.StorageAccess.isWarm
      (executeSstoreEcall request).outcome.accesses
      (StorageAccessBridge.accessKey request.address request.slot) = true := by
  exact StorageAccessBridge.sstoreExecution_warms
    request.state request.accesses request.address request.slot request.newValue

end StorageEcallBridge
end EvmAsm.EL
