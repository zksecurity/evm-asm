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

/--
SLOAD stack decoding succeeds exactly when the stack has a top slot word.

Distinctive token: StorageArgs.decodeStorageStack?_sload_eq_some_iff #110.
-/
theorem decodeStorageStack?_sload_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sload stack = some decoded ↔
      ∃ slot rest, stack = slot :: rest ∧ decoded = .sload (mkSLoad slot) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot rest =>
        simp [decodeStorageStack?] at h_decode
        cases h_decode
        exact ⟨slot, rest, rfl, rfl⟩
  · rintro ⟨slot, rest, rfl, rfl⟩
    rfl

theorem decodeStorageStack?_sstore_eq_some_iff
    (stack : List EvmWord) (decoded : Decoded) :
    decodeStorageStack? .sstore stack = some decoded ↔
      ∃ slot value rest,
        stack = slot :: value :: rest ∧ decoded = .sstore (mkSStore slot value) := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [decodeStorageStack?] at h_decode
    | cons slot tail =>
        cases tail with
        | nil => simp [decodeStorageStack?] at h_decode
        | cons value rest =>
            simp [decodeStorageStack?] at h_decode
            cases h_decode
            exact ⟨slot, value, rest, rfl, rfl⟩
  · rintro ⟨slot, value, rest, rfl, rfl⟩
    rfl

theorem decodeStorageStack?_sload_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sload stack = none ↔ stack.length < argumentCount .sload := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot rest =>
        simp [argumentCount] at h_len

theorem decodeStorageStack?_sstore_eq_none_iff
    (stack : List EvmWord) :
    decodeStorageStack? .sstore stack = none ↔ stack.length < argumentCount .sstore := by
  constructor
  · intro h_decode
    cases stack with
    | nil => simp [argumentCount]
    | cons slot tail =>
        cases tail with
        | nil => simp [argumentCount]
        | cons value rest => simp [decodeStorageStack?] at h_decode
  · intro h_len
    cases stack with
    | nil => rfl
    | cons slot tail =>
        cases tail with
        | nil => rfl
        | cons value rest =>
            simp [argumentCount] at h_len
            omega

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
