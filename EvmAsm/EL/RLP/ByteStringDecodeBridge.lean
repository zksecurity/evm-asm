/-
  EvmAsm.EL.RLP.ByteStringDecodeBridge

  Semantic success bridges for byte-string RLP prefix branches (GH #120).
-/

import EvmAsm.EL.RLP.PrefixDecode

namespace EvmAsm.EL.RLP

namespace ByteStringDecodeBridge

/--
Classified single-byte decode succeeds exactly as the one-byte RLP item.

Distinctive token:
ByteStringDecodeBridge.decodeAux_cons_singleByte_eq_some_iff #120.
-/
theorem decodeAux_cons_singleByte_eq_some_iff
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .singleByte)
    (data : List Byte) (rest' : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes data, rest') ↔
      [pfx] = data ∧ rest = rest' := by
  rw [decodeAux_cons_singleByte_of_classifyPrefix nDepth pfx rest h_class]
  simp

/--
Classified short-byte-string decode succeeds exactly when the payload slice is
available and, in the singleton case, is not redundantly encoded.

Distinctive token:
ByteStringDecodeBridge.decodeAux_cons_shortBytes_eq_some_iff #120.
-/
theorem decodeAux_cons_shortBytes_eq_some_iff
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .shortBytes)
    (data : List Byte) (rest' : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes data, rest') ↔
      ∃ payload,
        takeBytes rest (rlpPrefixShortBytesPayloadLen pfx) = some (payload, rest') ∧
          payload = data ∧
          match payload with
          | [b] => ¬ b.toNat < 0x80
          | _ => True := by
  rw [decodeAux_cons_shortBytes_of_classifyPrefix nDepth pfx rest h_class]
  cases h_take : takeBytes rest (rlpPrefixShortBytesPayloadLen pfx) with
  | none =>
      simp
  | some pair =>
      rcases pair with ⟨payload, slicedRest⟩
      cases payload with
      | nil =>
          constructor
          · intro h_some
            simp at h_some
            rcases h_some with ⟨h_data, h_rest⟩
            exact ⟨[], by simp [h_rest], h_data.symm, trivial⟩
          · rintro ⟨payload', h_slice, h_data, _⟩
            simp at h_slice
            rcases h_slice with ⟨h_payload, h_rest⟩
            rw [← h_data, h_payload, h_rest]
            rfl
      | cons b tail =>
          cases tail with
          | nil =>
              by_cases h_canon : b.toNat < 0x80
              · simp [h_canon]
              · constructor
                · intro h_some
                  simp [h_canon] at h_some
                  rcases h_some with ⟨h_data, h_rest⟩
                  exact ⟨[b], by simp [h_rest], h_data, h_canon⟩
                · rintro ⟨payload', h_slice, h_data, _⟩
                  simp at h_slice
                  rcases h_slice with ⟨h_payload, h_rest⟩
                  have h_data_eq : data = [b] := h_data.symm.trans h_payload.symm
                  rw [h_data_eq, h_rest]
                  simp [h_canon]
          | cons c tail' =>
              constructor
              · intro h_some
                simp at h_some
                rcases h_some with ⟨h_data, h_rest⟩
                exact ⟨b :: c :: tail', by simp [h_rest], h_data, trivial⟩
              · rintro ⟨payload', h_slice, h_data, _⟩
                simp at h_slice
                rcases h_slice with ⟨h_payload, h_rest⟩
                have h_data_eq : data = b :: c :: tail' := h_data.symm.trans h_payload.symm
                rw [h_data_eq, h_rest]
                rfl

/--
Classified long-byte-string decode succeeds exactly when the encoded length is
canonical long-form, the payload slice is available, and that slice is returned.

Distinctive token:
ByteStringDecodeBridge.decodeAux_cons_longBytes_eq_some_iff #120.
-/
theorem decodeAux_cons_longBytes_eq_some_iff
    (nDepth : Nat) (pfx : Byte) (rest : List Byte)
    (h_class : classifyPrefix pfx = .longBytes)
    (data : List Byte) (rest'' : List Byte) :
    decodeAux (nDepth + 1) (pfx :: rest) = some (.bytes data, rest'') ↔
      ∃ lenVal rest',
        readLength rest (rlpPrefixLongBytesLenOfLen pfx) = some (lenVal, rest') ∧
          55 < lenVal ∧
          takeBytes rest' lenVal = some (data, rest'') := by
  rw [decodeAux_cons_longBytes_of_classifyPrefix nDepth pfx rest h_class]
  cases h_read : readLength rest (rlpPrefixLongBytesLenOfLen pfx) with
  | none =>
      simp
  | some pair =>
      rcases pair with ⟨lenVal, lenRest⟩
      by_cases h_short : lenVal ≤ 55
      · constructor
        · simp [h_short]
        · rintro ⟨lenVal', rest', h_read', h_long, _⟩
          have h_pair : (lenVal, lenRest) = (lenVal', rest') := by
            simpa [h_read] using h_read'
          have h_len : lenVal = lenVal' := congrArg Prod.fst h_pair
          omega
      · cases h_take : takeBytes lenRest lenVal with
        | none =>
            simp [h_short, h_take, Option.bind]
        | some pair' =>
            rcases pair' with ⟨payload, outRest⟩
            constructor
            · intro h_some
              have h_data : payload = data ∧ outRest = rest'' := by
                simp [h_short, h_take, Option.bind] at h_some
                exact h_some
              have h_long : 55 < lenVal := by omega
              have h_take_out :
                  takeBytes lenRest lenVal = some (data, rest'') := by
                rw [← h_data.1, ← h_data.2]
                exact h_take
              refine Exists.intro lenVal ?_
              refine Exists.intro lenRest ?_
              constructor
              · rfl
              constructor
              · exact h_long
              · exact h_take_out
            · rintro ⟨lenVal', rest', h_read', h_long, h_take'⟩
              have h_len_pair : (lenVal, lenRest) = (lenVal', rest') := by
                simpa [h_read] using h_read'
              have h_len : lenVal = lenVal' := congrArg Prod.fst h_len_pair
              have h_rest : lenRest = rest' := congrArg Prod.snd h_len_pair
              have h_take_norm :
                  takeBytes lenRest lenVal = some (data, rest'') := by
                simpa [h_len, h_rest] using h_take'
              have h_payload_pair : (payload, outRest) = (data, rest'') := by
                simpa [h_take] using h_take_norm
              have h_payload : payload = data := congrArg Prod.fst h_payload_pair
              have h_out : outRest = rest'' := congrArg Prod.snd h_payload_pair
              simp [h_short, h_take, h_payload, h_out, Option.bind]

end ByteStringDecodeBridge

end EvmAsm.EL.RLP
