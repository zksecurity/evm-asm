/-
  EvmAsm.EL.RLP.ListDecodeBridge

  Semantic bridge for Phase 5 list-payload decoding (GH #120).
-/

import EvmAsm.EL.RLP.PrefixDecode

namespace EvmAsm.EL.RLP

namespace ListDecodeBridge

/-- Decode an RLP list payload and require that the payload decoder consumes
    the payload exactly. Distinctive token: ListDecodeBridge.decodeListPayload
    #120. -/
def decodeListPayload (nDepth : Nat) (payload : List Byte) : Option (List RLPItem) := do
  let (items, leftover) ← decodeItems nDepth payload
  if List.isEmpty leftover then some items else none

theorem decodeListPayload_eq_some_of_decodeItems_empty
    {nDepth : Nat} {payload : List Byte} {items : List RLPItem}
    (h_decode : decodeItems nDepth payload = some (items, [])) :
    decodeListPayload nDepth payload = some items := by
  simp [decodeListPayload, h_decode]

theorem decodeListPayload_eq_none_of_decodeItems_none
    {nDepth : Nat} {payload : List Byte}
    (h_decode : decodeItems nDepth payload = none) :
    decodeListPayload nDepth payload = none := by
  simp [decodeListPayload, h_decode]

theorem decodeListPayload_eq_none_of_leftover
    {nDepth : Nat} {payload : List Byte} {items : List RLPItem} {leftover : List Byte}
    (h_decode : decodeItems nDepth payload = some (items, leftover))
    (h_leftover : leftover ≠ []) :
    decodeListPayload nDepth payload = none := by
  cases leftover with
  | nil =>
      contradiction
  | cons b bs =>
      simp [decodeListPayload, h_decode]

/--
List-payload decode failure is exactly either recursive decoder failure or
successful payload-prefix decode with trailing bytes left over.

Distinctive token: ListDecodeBridge.decodeListPayload_eq_none_iff #120.
-/
theorem decodeListPayload_eq_none_iff (nDepth : Nat) (payload : List Byte) :
    decodeListPayload nDepth payload = none ↔
      decodeItems nDepth payload = none ∨
        ∃ items leftover,
          decodeItems nDepth payload = some (items, leftover) ∧ leftover ≠ [] := by
  unfold decodeListPayload
  cases h_decode : decodeItems nDepth payload with
  | none => simp
  | some decoded =>
      cases decoded with
      | mk items leftover =>
          cases leftover with
          | nil => simp
          | cons b rest =>
              constructor
              · intro _
                exact Or.inr ⟨items, b :: rest, rfl, by simp⟩
              · intro _
                rfl

theorem decodeAux_cons_shortList_eq_decodeListPayload
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let items ← decodeListPayload nDepth payload
        some (.list items, rest')) := by
  rw [decodeAux_cons_shortList_of_classifyPrefix nDepth pfx rest h_class]
  cases h_take : takeBytes rest (rlpPrefixShortListPayloadLen pfx) with
  | none =>
      simp [decodeListPayload]
  | some pair =>
      rcases pair with ⟨payload, rest'⟩
      cases h_decode : decodeItems nDepth payload with
      | none =>
          simp [decodeListPayload, h_decode]
      | some pair' =>
          rcases pair' with ⟨items, leftover⟩
          cases leftover <;> simp [decodeListPayload, h_decode]

theorem decodeAux_cons_longList_eq_decodeListPayload
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList) :
    decodeAux (nDepth + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let items ← decodeListPayload nDepth payload
          some (.list items, rest'')) := by
  rw [decodeAux_cons_longList_of_classifyPrefix nDepth pfx rest h_class]
  cases h_read : readLength rest (rlpPrefixLongListLenOfLen pfx) with
  | none =>
      simp [decodeListPayload]
  | some pair =>
      rcases pair with ⟨lenVal, rest'⟩
      by_cases h_short : lenVal ≤ 55
      · simp [decodeListPayload, h_short]
      · cases h_take : takeBytes rest' lenVal with
        | none =>
            simp [decodeListPayload, h_short, h_take]
        | some pair' =>
            rcases pair' with ⟨payload, rest''⟩
            cases h_decode : decodeItems nDepth payload with
            | none =>
                simp [decodeListPayload, h_short, h_take, h_decode]
            | some pair'' =>
                rcases pair'' with ⟨items, leftover⟩
                cases leftover <;> simp [decodeListPayload, h_short, h_take, h_decode]

end ListDecodeBridge

end EvmAsm.EL.RLP
