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
def decodeListPayload (fuel : Nat) (payload : List Byte) : Option (List RLPItem) := do
  let (items, leftover) ← decodeItems fuel payload
  if List.isEmpty leftover then some items else none

theorem decodeListPayload_eq_some_of_decodeItems_empty
    {fuel : Nat} {payload : List Byte} {items : List RLPItem}
    (h_decode : decodeItems fuel payload = some (items, [])) :
    decodeListPayload fuel payload = some items := by
  simp [decodeListPayload, h_decode]

theorem decodeListPayload_eq_none_of_decodeItems_none
    {fuel : Nat} {payload : List Byte}
    (h_decode : decodeItems fuel payload = none) :
    decodeListPayload fuel payload = none := by
  simp [decodeListPayload, h_decode]

theorem decodeListPayload_eq_none_of_leftover
    {fuel : Nat} {payload : List Byte} {items : List RLPItem} {leftover : List Byte}
    (h_decode : decodeItems fuel payload = some (items, leftover))
    (h_leftover : leftover ≠ []) :
    decodeListPayload fuel payload = none := by
  cases leftover with
  | nil =>
      contradiction
  | cons b bs =>
      simp [decodeListPayload, h_decode]

theorem decodeAux_cons_shortList_eq_decodeListPayload
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortList) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (payload, rest') ← takeBytes rest (rlpPrefixShortListPayloadLen pfx)
        let items ← decodeListPayload fuel payload
        some (.list items, rest')) := by
  rw [decodeAux_cons_shortList_of_classifyPrefix fuel pfx rest h_class]
  cases h_take : takeBytes rest (rlpPrefixShortListPayloadLen pfx) with
  | none =>
      simp [decodeListPayload]
  | some pair =>
      rcases pair with ⟨payload, rest'⟩
      cases h_decode : decodeItems fuel payload with
      | none =>
          simp [decodeListPayload, h_decode]
      | some pair' =>
          rcases pair' with ⟨items, leftover⟩
          cases leftover <;> simp [decodeListPayload, h_decode]

theorem decodeAux_cons_longList_eq_decodeListPayload
    (fuel : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longList) :
    decodeAux (fuel + 1) (pfx :: rest) =
      (do
        let (lenVal, rest') ← readLength rest (rlpPrefixLongListLenOfLen pfx)
        if lenVal ≤ 55 then none
        else do
          let (payload, rest'') ← takeBytes rest' lenVal
          let items ← decodeListPayload fuel payload
          some (.list items, rest'')) := by
  rw [decodeAux_cons_longList_of_classifyPrefix fuel pfx rest h_class]
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
            cases h_decode : decodeItems fuel payload with
            | none =>
                simp [decodeListPayload, h_short, h_take, h_decode]
            | some pair'' =>
                rcases pair'' with ⟨items, leftover⟩
                cases leftover <;> simp [decodeListPayload, h_short, h_take, h_decode]

end ListDecodeBridge

end EvmAsm.EL.RLP
