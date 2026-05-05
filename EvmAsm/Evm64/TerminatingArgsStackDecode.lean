/-
  EvmAsm.Evm64.TerminatingArgsStackDecode

  Pure top-of-stack decoders for frame-terminating opcode arguments
  (GH #113).
-/

import EvmAsm.Evm64.TerminatingArgs

namespace EvmAsm.Evm64

namespace TerminatingArgsStackDecode

open TerminatingArgs

/--
Decode RETURN stack arguments from the top-of-stack list order:
`offset, size`.

Distinctive token: TerminatingArgsStackDecode.decodeReturnStack? #113.
-/
def decodeReturnStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (returnArgs offset size)
  | _ => none

/--
Decode REVERT stack arguments from the top-of-stack list order:
`offset, size`.
-/
def decodeRevertStack? : List EvmWord → Option Args
  | offset :: size :: _ => some (revertArgs offset size)
  | _ => none

/--
Decode SELFDESTRUCT stack arguments from the top-of-stack list order:
`beneficiary`.
-/
def decodeSelfdestructStack? : List EvmWord → Option EvmWord
  | beneficiary :: _ => some beneficiary
  | _ => none

theorem decodeReturnStack?_cons
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeReturnStack? (offset :: size :: rest) =
      some (returnArgs offset size) := rfl

theorem decodeRevertStack?_cons
    (offset size : EvmWord) (rest : List EvmWord) :
    decodeRevertStack? (offset :: size :: rest) =
      some (revertArgs offset size) := rfl

theorem decodeSelfdestructStack?_cons
    (beneficiary : EvmWord) (rest : List EvmWord) :
    decodeSelfdestructStack? (beneficiary :: rest) =
      some beneficiary := rfl

theorem decodeReturnStack?_eq_some_iff
    {stack : List EvmWord} {args : Args} :
    decodeReturnStack? stack = some args ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧ args = returnArgs offset size := by
  constructor
  · cases stack with
    | nil => simp [decodeReturnStack?]
    | cons offset s1 =>
      cases s1 with
      | nil => simp [decodeReturnStack?]
      | cons size rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeRevertStack?_eq_some_iff
    {stack : List EvmWord} {args : Args} :
    decodeRevertStack? stack = some args ↔
      ∃ offset size rest,
        stack = offset :: size :: rest ∧ args = revertArgs offset size := by
  constructor
  · cases stack with
    | nil => simp [decodeRevertStack?]
    | cons offset s1 =>
      cases s1 with
      | nil => simp [decodeRevertStack?]
      | cons size rest =>
        intro h
        injection h with h_args
        subst h_args
        exact ⟨offset, size, rest, rfl, rfl⟩
  · rintro ⟨offset, size, rest, rfl, rfl⟩
    rfl

theorem decodeSelfdestructStack?_eq_some_iff
    {stack : List EvmWord} {beneficiary : EvmWord} :
    decodeSelfdestructStack? stack = some beneficiary ↔
      ∃ rest, stack = beneficiary :: rest := by
  constructor
  · cases stack with
    | nil => simp [decodeSelfdestructStack?]
    | cons head rest =>
      intro h
      injection h with h_eq
      subst h_eq
      exact ⟨rest, rfl⟩
  · rintro ⟨rest, rfl⟩
    rfl

theorem decodeReturnStack?_dataRange
    (offset size : EvmWord) (rest : List EvmWord) :
    dataRange (Option.getD
      (decodeReturnStack? (offset :: size :: rest))
      (returnArgs 0 0)) =
      { offset := offset, size := size } := rfl

theorem decodeRevertStack?_dataRange
    (offset size : EvmWord) (rest : List EvmWord) :
    dataRange (Option.getD
      (decodeRevertStack? (offset :: size :: rest))
      (revertArgs 0 0)) =
      { offset := offset, size := size } := rfl

end TerminatingArgsStackDecode

end EvmAsm.Evm64
