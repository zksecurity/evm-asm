/-
  EvmAsm.EL.StorageStackExecutionBridge

  Pure stack-to-ECALL execution bridge for SLOAD/SSTORE (GH #110).
-/

import EvmAsm.EL.StorageArgsEcallBridge

namespace EvmAsm.EL

namespace StorageStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev StorageKind := EvmAsm.Evm64.StorageArgs.Kind
abbrev StorageAccessList := StorageArgsEcallBridge.StorageAccessList

/-- Runtime state visible to the pure storage stack bridge. -/
structure StorageStackState where
  stack : List EvmWord

def stackRestAfterStorage? (kind : StorageKind) :
    List EvmWord -> Option (List EvmWord)
  | _slot :: rest =>
      match kind with
      | .sload => some rest
      | .sstore =>
          match rest with
          | _value :: rest => some rest
          | _ => none
  | _ => none

def stackWordsFromDecoded (state : WorldState) (accesses : StorageAccessList)
    (address : Address) : EvmAsm.Evm64.StorageArgs.Decoded -> List EvmWord
  | .sload args =>
      [StorageArgsEcallBridge.sloadStackWordFromArgs
        state accesses address args]
  | .sstore args =>
      StorageArgsEcallBridge.sstoreStackWordsFromArgs
        state accesses address args

/--
Run the pure storage stack effect: decode SLOAD/SSTORE operands, build the
existing storage ECALL request surface, and expose the resulting stack after
opcode-specific consumption.

Distinctive token: StorageStackExecutionBridge.runStorageStack? #110.
-/
def runStorageStack? (kind : StorageKind) (state : WorldState)
    (accesses : StorageAccessList) (address : Address) :
    StorageStackState -> Option StorageStackState
  | stackState =>
      match EvmAsm.Evm64.StorageArgs.decodeStorageStack? kind stackState.stack,
          stackRestAfterStorage? kind stackState.stack with
      | some decoded, some rest =>
          some { stack := stackWordsFromDecoded state accesses address decoded ++ rest }
      | _, _ => none

theorem stackRestAfterStorage?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sload (slot :: rest) = some rest := rfl

theorem stackRestAfterStorage?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    stackRestAfterStorage? .sstore (slot :: value :: rest) = some rest := rfl

@[simp] theorem stackRestAfterStorage?_nil (kind : StorageKind) :
    stackRestAfterStorage? kind [] = none := rfl

theorem runStorageStack?_eq_none_iff
    (kind : StorageKind) (state : WorldState) (accesses : StorageAccessList)
    (address : Address) (stackState : StorageStackState) :
    runStorageStack? kind state accesses address stackState = none ↔
      EvmAsm.Evm64.StorageArgs.decodeStorageStack? kind stackState.stack = none ∨
        stackRestAfterStorage? kind stackState.stack = none := by
  cases stackState with
  | mk stack =>
      simp [runStorageStack?]
      cases h_decode :
          EvmAsm.Evm64.StorageArgs.decodeStorageStack? kind stack with
      | none => simp
      | some decoded =>
          cases h_rest : stackRestAfterStorage? kind stack with
          | none => simp
          | some rest => simp

theorem stackWordsFromDecoded_sload
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (slot : EvmWord) :
    stackWordsFromDecoded state accesses address
        (.sload (EvmAsm.Evm64.StorageArgs.mkSLoad slot)) =
      [Storage.sload state address slot] := rfl

theorem stackWordsFromDecoded_sstore
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (slot value : EvmWord) :
    stackWordsFromDecoded state accesses address
        (.sstore (EvmAsm.Evm64.StorageArgs.mkSStore slot value)) =
      [] := rfl

theorem runStorageStack?_sload
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (slot : EvmWord) (rest : List EvmWord) :
    runStorageStack? .sload state accesses address { stack := slot :: rest } =
      some { stack := Storage.sload state address slot :: rest } := rfl

theorem runStorageStack?_sstore
    (state : WorldState) (accesses : StorageAccessList) (address : Address)
    (slot value : EvmWord) (rest : List EvmWord) :
    runStorageStack? .sstore state accesses address
        { stack := slot :: value :: rest } =
      some { stack := rest } := rfl

theorem runStorageStack?_eq_some_iff
    (kind : StorageKind) (state : WorldState) (accesses : StorageAccessList)
    (address : Address) (stackState out : StorageStackState) :
    runStorageStack? kind state accesses address stackState = some out ↔
      ∃ decoded rest,
        EvmAsm.Evm64.StorageArgs.decodeStorageStack? kind stackState.stack =
          some decoded ∧
        stackRestAfterStorage? kind stackState.stack = some rest ∧
        out = { stack := stackWordsFromDecoded state accesses address decoded ++ rest } := by
  cases stackState with
  | mk stack =>
      constructor
      · intro h_run
        simp [runStorageStack?] at h_run
        cases h_decode :
            EvmAsm.Evm64.StorageArgs.decodeStorageStack? kind stack with
        | none => simp [h_decode] at h_run
        | some decoded =>
            cases h_rest : stackRestAfterStorage? kind stack with
            | none => simp [h_decode, h_rest] at h_run
            | some rest =>
                simp [h_decode, h_rest] at h_run
                exact ⟨decoded, rest, rfl, rfl, h_run.symm⟩
      · rintro ⟨decoded, rest, h_decode, h_rest, rfl⟩
        simp [runStorageStack?, h_decode, h_rest]

theorem runStorageStack?_stack_length
    {kind : StorageKind} {state : WorldState} {accesses : StorageAccessList}
    {address : Address} {stackState out : StorageStackState}
    (h_run : runStorageStack? kind state accesses address stackState = some out) :
    out.stack.length + EvmAsm.Evm64.StorageArgs.argumentCount kind =
      stackState.stack.length + EvmAsm.Evm64.StorageArgs.resultCount kind := by
  cases stackState with
  | mk stack =>
      cases kind
      · cases stack with
        | nil => simp [runStorageStack?, stackRestAfterStorage?] at h_run
        | cons slot rest =>
            simp [runStorageStack?, stackRestAfterStorage?,
              stackWordsFromDecoded] at h_run
            cases h_run
            simp [EvmAsm.Evm64.StorageArgs.argumentCount,
              EvmAsm.Evm64.StorageArgs.resultCount]
      · cases stack with
        | nil => simp [runStorageStack?, stackRestAfterStorage?] at h_run
        | cons slot tail =>
            cases tail with
            | nil => simp [runStorageStack?, stackRestAfterStorage?] at h_run
            | cons value rest =>
                simp [runStorageStack?, stackRestAfterStorage?,
                  stackWordsFromDecoded] at h_run
                cases h_run
                simp [EvmAsm.Evm64.StorageArgs.argumentCount,
                  EvmAsm.Evm64.StorageArgs.resultCount]

end StorageStackExecutionBridge

end EvmAsm.EL
