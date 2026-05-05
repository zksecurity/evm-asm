/-
  EvmAsm.EL.StorageArgsEcallBridge

  Bridge from decoded SLOAD/SSTORE stack arguments to the storage ECALL
  request/result surface (GH #110).
-/

import EvmAsm.Evm64.StorageArgs
import EvmAsm.EL.StorageEcallStackBridge

namespace EvmAsm.EL

namespace StorageArgsEcallBridge

abbrev StorageAccessList := EvmAsm.Evm64.StorageAccess.StorageAccessList
abbrev SLoadArgs := EvmAsm.Evm64.StorageArgs.SLoad
abbrev SStoreArgs := EvmAsm.Evm64.StorageArgs.SStore
abbrev SloadRequest := StorageEcallBridge.SloadRequest
abbrev SstoreRequest := StorageEcallBridge.SstoreRequest

/--
Build a pure SLOAD ECALL request from decoded stack arguments and the current
contract storage address.

Distinctive token: StorageArgsEcallBridge.sloadRequestFromArgs #110.
-/
def sloadRequestFromArgs
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) : SloadRequest :=
  { state := state
    accesses := accesses
    address := address
    slot := args.slot }

def sstoreRequestFromArgs
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) : SstoreRequest :=
  { state := state
    accesses := accesses
    address := address
    slot := args.slot
    newValue := args.value }

theorem sloadRequestFromArgs_state
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) :
    (sloadRequestFromArgs state accesses address args).state = state := rfl

theorem sloadRequestFromArgs_accesses
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) :
    (sloadRequestFromArgs state accesses address args).accesses = accesses := rfl

theorem sloadRequestFromArgs_address
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) :
    (sloadRequestFromArgs state accesses address args).address = address := rfl

theorem sloadRequestFromArgs_slot
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) :
    (sloadRequestFromArgs state accesses address args).slot = args.slot := rfl

theorem sstoreRequestFromArgs_state
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreRequestFromArgs state accesses address args).state = state := rfl

theorem sstoreRequestFromArgs_accesses
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreRequestFromArgs state accesses address args).accesses = accesses := rfl

theorem sstoreRequestFromArgs_address
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreRequestFromArgs state accesses address args).address = address := rfl

theorem sstoreRequestFromArgs_slot
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreRequestFromArgs state accesses address args).slot = args.slot := rfl

theorem sstoreRequestFromArgs_newValue
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreRequestFromArgs state accesses address args).newValue = args.value := rfl

def sloadStackWordFromArgs
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) : Word256 :=
  StorageEcallStackBridge.sloadEcallStackWord
    (sloadRequestFromArgs state accesses address args)

def sstoreStackWordsFromArgs
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) : List Word256 :=
  StorageEcallStackBridge.sstoreEcallStackWords
    (sstoreRequestFromArgs state accesses address args)

theorem sloadStackWordFromArgs_storage
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SLoadArgs) :
    sloadStackWordFromArgs state accesses address args =
      Storage.sload state address args.slot := rfl

@[simp] theorem sstoreStackWordsFromArgs_nil
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    sstoreStackWordsFromArgs state accesses address args = [] := rfl

theorem sstoreStackWordsFromArgs_length
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (args : SStoreArgs) :
    (sstoreStackWordsFromArgs state accesses address args).length =
      EvmAsm.Evm64.StorageArgs.resultCount .sstore := rfl

end StorageArgsEcallBridge

end EvmAsm.EL
