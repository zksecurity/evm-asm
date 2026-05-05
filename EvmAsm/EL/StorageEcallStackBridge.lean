/-
  EvmAsm.EL.StorageEcallStackBridge

  Bridge from storage ECALL results to stack-facing SLOAD/SSTORE effects
  (GH #110).
-/

import EvmAsm.EL.StorageEcallBridge
import EvmAsm.EL.StorageStackBridge

namespace EvmAsm.EL
namespace StorageEcallStackBridge

abbrev SloadRequest := StorageEcallBridge.SloadRequest
abbrev SstoreRequest := StorageEcallBridge.SstoreRequest

/-- Convert an executed SLOAD ECALL result to the stack-facing execution record.
    Distinctive token: StorageEcallStackBridge.sloadEcallStackWord #110. -/
def sloadExecutionFromEcall (request : SloadRequest) :
    StorageStackBridge.SloadExecution :=
  let result := StorageEcallBridge.executeSloadEcall request
  { value := result.value
    outcome := result.outcome }

/-- Convert an executed SSTORE ECALL result to the stack-facing execution record. -/
def sstoreExecutionFromEcall (request : SstoreRequest) :
    StorageStackBridge.SstoreExecution :=
  let result := StorageEcallBridge.executeSstoreEcall request
  { state := result.state
    outcome := result.outcome }

/-- Stack word pushed by an SLOAD ECALL. -/
def sloadEcallStackWord (request : SloadRequest) : Word256 :=
  StorageStackBridge.sloadStackWord (sloadExecutionFromEcall request)

/-- Stack words pushed by an SSTORE ECALL. This is always empty. -/
def sstoreEcallStackWords (request : SstoreRequest) : List Word256 :=
  StorageStackBridge.sstoreStackWords (sstoreExecutionFromEcall request)

theorem sloadExecutionFromEcall_value (request : SloadRequest) :
    (sloadExecutionFromEcall request).value =
      (StorageEcallBridge.executeSloadEcall request).value := rfl

theorem sloadExecutionFromEcall_outcome (request : SloadRequest) :
    (sloadExecutionFromEcall request).outcome =
      (StorageEcallBridge.executeSloadEcall request).outcome := rfl

theorem sloadEcallStackWord_value (request : SloadRequest) :
    sloadEcallStackWord request =
      (StorageEcallBridge.executeSloadEcall request).value := rfl

theorem sloadEcallStackWord_storage (request : SloadRequest) :
    sloadEcallStackWord request =
      Storage.sload request.state request.address request.slot := rfl

theorem sstoreExecutionFromEcall_state (request : SstoreRequest) :
    (sstoreExecutionFromEcall request).state =
      (StorageEcallBridge.executeSstoreEcall request).state := rfl

theorem sstoreExecutionFromEcall_outcome (request : SstoreRequest) :
    (sstoreExecutionFromEcall request).outcome =
      (StorageEcallBridge.executeSstoreEcall request).outcome := rfl

@[simp] theorem sstoreEcallStackWords_nil (request : SstoreRequest) :
    sstoreEcallStackWords request = [] := rfl

theorem sstoreEcallStackWords_length (request : SstoreRequest) :
    (sstoreEcallStackWords request).length =
      StorageStackBridge.sstoreResultCount := rfl

end StorageEcallStackBridge
end EvmAsm.EL
