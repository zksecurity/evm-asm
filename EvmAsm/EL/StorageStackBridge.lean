/-
  EvmAsm.EL.StorageStackBridge

  Stack-facing bridge for SLOAD/SSTORE storage executions (GH #110).
-/

import EvmAsm.EL.StorageAccessBridge

namespace EvmAsm.EL

namespace StorageStackBridge

abbrev SloadExecution := StorageAccessBridge.SloadExecution
abbrev SstoreExecution := StorageAccessBridge.SstoreExecution

/-- SLOAD pushes one stack word. -/
def sloadResultCount : Nat := 1

/-- SSTORE pushes no stack words. -/
def sstoreResultCount : Nat := 0

/-- Stack word pushed by an SLOAD execution.
    Distinctive token: StorageStackBridge.sloadStackWord #110. -/
def sloadStackWord (execution : SloadExecution) : Word256 :=
  execution.value

/-- SSTORE's stack result payload is empty; state and access outcome are kept in
    `SstoreExecution`. -/
def sstoreStackWords (_execution : SstoreExecution) : List Word256 :=
  []

theorem sloadResultCount_eq_one :
    sloadResultCount = 1 := rfl

theorem sstoreResultCount_eq_zero :
    sstoreResultCount = 0 := rfl

theorem sloadStackWord_value (execution : SloadExecution) :
    sloadStackWord execution = execution.value := rfl

theorem sloadStackWord_execution
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    sloadStackWord (StorageAccessBridge.sloadExecution state accesses addr slot) =
      Storage.sload state addr slot := rfl

theorem sloadStackWord_empty
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    sloadStackWord (StorageAccessBridge.sloadExecution WorldState.empty accesses addr slot) =
      0 := rfl

@[simp] theorem sstoreStackWords_nil (execution : SstoreExecution) :
    sstoreStackWords execution = [] := rfl

theorem sstoreStackWords_length (execution : SstoreExecution) :
    (sstoreStackWords execution).length = sstoreResultCount := rfl

theorem sstoreStackWords_execution
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) :
    sstoreStackWords (StorageAccessBridge.sstoreExecution state accesses addr slot new) =
      [] := rfl

end StorageStackBridge

end EvmAsm.EL
