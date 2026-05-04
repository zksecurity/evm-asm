/-
  EvmAsm.EL.StorageAccessBridge

  Bridge from the pure EL SLOAD/SSTORE semantics to the Evm64 cold/warm
  storage-access outcome surface (GH #110).  This is still pure data:
  later ECALL and stack-level opcode specs can consume these records to
  connect handler execution to the executable storage model.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.Storage
import EvmAsm.Evm64.StorageAccessOutcome

namespace EvmAsm.EL
namespace StorageAccessBridge

/-- Convert an EL storage address/slot pair into the Evm64 access-list key
    used by EIP-2929 cold/warm accounting. -/
def accessKey (addr : Address) (slot : StorageKey) :
    EvmAsm.Evm64.StorageAccess.StorageAccessKey :=
  { address := addr, slot := slot }

/-- Pure SLOAD result paired with the cold/warm access-list outcome. -/
structure SloadExecution where
  value : Word256
  outcome : EvmAsm.Evm64.StorageAccessOutcome.Outcome

/-- Pure SSTORE result paired with the cold/warm access-list outcome. -/
structure SstoreExecution where
  state : WorldState
  outcome : EvmAsm.Evm64.StorageAccessOutcome.Outcome

/-- Execute pure SLOAD and account for the storage-key access outcome. -/
def sloadExecution
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) : SloadExecution :=
  let key := accessKey addr slot
  { value := Storage.sload state addr slot
    outcome := EvmAsm.Evm64.StorageAccessOutcome.sloadOutcome accesses key }

/-- Execute pure SSTORE and account for the storage-key access outcome.

    The dynamic cost depends on the current slot value and the new value;
    the resulting world state is the pure EL `Storage.sstore` update. -/
def sstoreExecution
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) : SstoreExecution :=
  let current := Storage.sload state addr slot
  let key := accessKey addr slot
  { state := Storage.sstore state addr slot new
    outcome := EvmAsm.Evm64.StorageAccessOutcome.sstoreOutcome accesses key current new }

theorem accessKey_address (addr : Address) (slot : StorageKey) :
    (accessKey addr slot).address = addr := rfl

theorem accessKey_slot (addr : Address) (slot : StorageKey) :
    (accessKey addr slot).slot = slot := rfl

theorem sloadExecution_value
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    (sloadExecution state accesses addr slot).value =
      Storage.sload state addr slot := rfl

theorem sloadExecution_outcome
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    (sloadExecution state accesses addr slot).outcome =
      EvmAsm.Evm64.StorageAccessOutcome.sloadOutcome accesses (accessKey addr slot) := rfl

theorem sloadExecution_cost
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    (sloadExecution state accesses addr slot).outcome.cost =
      EvmAsm.Evm64.StorageAccess.sloadDynamicCostForKey accesses (accessKey addr slot) := rfl

theorem sloadExecution_warms
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) :
    EvmAsm.Evm64.StorageAccess.isWarm
      (sloadExecution state accesses addr slot).outcome.accesses
      (accessKey addr slot) = true := by
  exact EvmAsm.Evm64.StorageAccessOutcome.sloadOutcome_warms accesses (accessKey addr slot)

/-- Distinctive token: `StorageAccessBridge.sstoreExecution_state`. -/
theorem sstoreExecution_state
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) :
    (sstoreExecution state accesses addr slot new).state =
      Storage.sstore state addr slot new := rfl

theorem sstoreExecution_outcome
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) :
    (sstoreExecution state accesses addr slot new).outcome =
      EvmAsm.Evm64.StorageAccessOutcome.sstoreOutcome accesses (accessKey addr slot)
        (Storage.sload state addr slot) new := rfl

theorem sstoreExecution_cost
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) :
    (sstoreExecution state accesses addr slot new).outcome.cost =
      EvmAsm.Evm64.StorageAccess.sstoreDynamicCostForKey accesses (accessKey addr slot)
        (Storage.sload state addr slot) new := rfl

theorem sstoreExecution_warms
    (state : WorldState)
    (accesses : EvmAsm.Evm64.StorageAccess.StorageAccessList)
    (addr : Address) (slot : StorageKey) (new : Word256) :
    EvmAsm.Evm64.StorageAccess.isWarm
      (sstoreExecution state accesses addr slot new).outcome.accesses
      (accessKey addr slot) = true := by
  exact EvmAsm.Evm64.StorageAccessOutcome.sstoreOutcome_warms accesses
    (accessKey addr slot) (Storage.sload state addr slot) new

theorem sloadExecution_nil_cost
    (state : WorldState) (addr : Address) (slot : StorageKey) :
    (sloadExecution state [] addr slot).outcome.cost =
      EvmAsm.Evm64.StorageGas.coldSloadCost := by
  exact EvmAsm.Evm64.StorageAccessOutcome.sloadOutcome_nil_cost (accessKey addr slot)

theorem sstoreExecution_nil_cost
    (state : WorldState) (addr : Address) (slot : StorageKey) (new : Word256) :
    (sstoreExecution state [] addr slot new).outcome.cost =
      EvmAsm.Evm64.StorageGas.coldSloadCost +
        EvmAsm.Evm64.StorageGas.sstoreWriteCost (Storage.sload state addr slot) new := by
  exact EvmAsm.Evm64.StorageAccessOutcome.sstoreOutcome_nil_cost
    (accessKey addr slot) (Storage.sload state addr slot) new

end StorageAccessBridge
end EvmAsm.EL
