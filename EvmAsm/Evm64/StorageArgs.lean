/-
  EvmAsm.Evm64.StorageArgs

  Pure stack-argument records and decoder for SLOAD and SSTORE (GH #110).
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64

namespace StorageArgs

/-- SLOAD stack arguments: one storage slot key. -/
structure SLoad where
  slot : EvmWord
  deriving Repr

/-- SSTORE stack arguments: storage slot key and new value. -/
structure SStore where
  slot : EvmWord
  value : EvmWord
  deriving Repr

inductive Kind where
  | sload
  | sstore
  deriving DecidableEq, Repr

inductive Decoded where
  | sload (args : SLoad)
  | sstore (args : SStore)
  deriving Repr

def argumentCount : Kind → Nat
  | .sload => 1
  | .sstore => 2

def resultCount : Kind → Nat
  | .sload => 1
  | .sstore => 0

def writesStorage : Kind → Bool
  | .sload => false
  | .sstore => true

def mkSLoad (slot : EvmWord) : SLoad :=
  { slot := slot }

def mkSStore (slot value : EvmWord) : SStore :=
  { slot := slot, value := value }

def decodedKind : Decoded → Kind
  | .sload _ => .sload
  | .sstore _ => .sstore

/--
Decode SLOAD/SSTORE stack arguments from top-of-stack order:
`slot` for SLOAD and `slot, value` for SSTORE.

Distinctive token: StorageArgs.decodeStorageStack? #110.
-/
def decodeStorageStack? : Kind → List EvmWord → Option Decoded
  | .sload, slot :: _ => some (.sload (mkSLoad slot))
  | .sstore, slot :: value :: _ => some (.sstore (mkSStore slot value))
  | _, _ => none

theorem decodeStorageStack?_sload
    (slot : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sload (slot :: rest) =
      some (.sload (mkSLoad slot)) := rfl

theorem decodeStorageStack?_sstore
    (slot value : EvmWord) (rest : List EvmWord) :
    decodeStorageStack? .sstore (slot :: value :: rest) =
      some (.sstore (mkSStore slot value)) := rfl

theorem decodedKind_sload (slot : EvmWord) :
    decodedKind (.sload (mkSLoad slot)) = .sload := rfl

theorem decodedKind_sstore (slot value : EvmWord) :
    decodedKind (.sstore (mkSStore slot value)) = .sstore := rfl

theorem argumentCount_sload : argumentCount .sload = 1 := rfl

theorem argumentCount_sstore : argumentCount .sstore = 2 := rfl

theorem resultCount_sload : resultCount .sload = 1 := rfl

theorem resultCount_sstore : resultCount .sstore = 0 := rfl

theorem writesStorage_sload : writesStorage .sload = false := rfl

theorem writesStorage_sstore : writesStorage .sstore = true := rfl

theorem decoded_sload_slot (slot : EvmWord) :
    (mkSLoad slot).slot = slot := rfl

theorem decoded_sstore_slot (slot value : EvmWord) :
    (mkSStore slot value).slot = slot := rfl

theorem decoded_sstore_value (slot value : EvmWord) :
    (mkSStore slot value).value = value := rfl

end StorageArgs

end EvmAsm.Evm64
