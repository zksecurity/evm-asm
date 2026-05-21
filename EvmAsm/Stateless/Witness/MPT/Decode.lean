/-
  EvmAsm.Stateless.Witness.MPT.Decode

  RLP-decode a single MPT node. The wire format (Ethereum MPT) is
  one of three RLP shapes selected by item count + first nibble:

  - **Branch node**: 17-item RLP list. Items 0..16 are child
    references (32-byte hash or inlined RLP < 32 bytes). Item 16
    is the value at this prefix (often empty bytes).
  - **Extension node**: 2-item RLP list `[encoded_path,
    child_ref]`. The encoded_path is HP-encoded nibbles with
    flag bits in the first byte indicating "extension".
  - **Leaf node**: 2-item RLP list `[encoded_path, value]`. Same
    HP encoding as extension but with the "leaf" flag set.

  The decoder returns the node variant + decoded fields without
  copying — the input RLP buffer is in the node_db, and the
  decoder just records `(item_start, item_len)` offsets into a
  small node-shape struct in scratch RAM.

  ## PR-K20 / PR-K21 status

  Two primitives are now in place:

    - PR-K20 (#5388) : `rlp_list_nth_item` walks an RLP-encoded
                       list to extract the N-th item's content
                       bounds.
    - PR-K21 (this)  : `mpt_node_kind` classifies an MPT node
                       as leaf / extension / branch from item
                       count + path-prefix nibble.

  Higher-level node decoding composes the two:

    - PR-K22+        : `mpt_branch_child` wraps PR-K20 with
                       index in 0..15.
    - PR-K23+        : `mpt_leaf_extract_value` / `mpt_extension_next`.

  Calling convention for `mpt_node_kind`:

      Input:
        a0 (input)  : RLP-encoded node bytes ptr
        a1 (input)  : node byte length
        ra (input)  : return

      Output:
        a0 = 0   branch node (17-item RLP list)
        a0 = 1   extension node (2-item list, item 0 high-nibble ∈ {0,1})
        a0 = 2   leaf node (2-item list, item 0 high-nibble ∈ {2,3})
        a0 = 3   parse failure (not a list, empty list, malformed item 0,
                 or item 0 high-nibble outside [0..3])

  HP encoding cheat-sheet for the first path byte:

      high nibble = 0  →  extension, even path length
      high nibble = 1  →  extension, odd path length
      high nibble = 2  →  leaf, even path length
      high nibble = 3  →  leaf, odd path length

  Calling convention for `rlp_list_nth_item`:

      Input:
        a0 (input)  : list bytes ptr (start of the outer RLP
                      list prefix)
        a1 (input)  : total list byte length
        a2 (input)  : index N (0-based)
        a3 (input)  : u64 out ptr (item N's *content* offset
                      within `list_bytes`, NOT including the
                      RLP type prefix)
        a4 (input)  : u64 out ptr (item N's content byte length)
        ra (input)  : return

      Output:
        a0 = 0  iff item N exists within the list
        a0 = 1  on parse error or N >= number_of_items.

  The "content" interpretation means:
    * Single byte (0x00..0x7f)           → offset points AT the byte; length = 1
    * Short string (0x80..0xb7)          → offset = item_start+1; length = b - 0x80
    * Long string (0xb8..0xbf)           → offset = item_start+1+lol; length = decoded
    * List items (0xc0..0xff)            → offset = item_start; length = full encoded length

  i.e. for byte-string items, the prefix is stripped; for sub-
  lists the full encoded form is returned so callers can recurse.

  ## Implementation shape

  `rlpListNthItemFunction` emits `rlp_list_nth_item:`. Pure
  register arithmetic; no scratch memory; leaf-callable.

  `mptNodeKindFunction` emits `mpt_node_kind:`. Calls
  `rlp_list_nth_item` twice (once to probe item 2 for the
  branch case, once to read item 0's path byte for the leaf
  vs extension distinction). Uses four 8-byte `.data` scratches
  for the temporary `(offset, length)` returns. Not
  leaf-callable (calls into `rlp_list_nth_item`).
-/

namespace EvmAsm.Stateless.Witness.MPT.Decode

-- TODO(stateless-witness): expose a `cpsTripleWithin` spec for
-- `rlp_list_nth_item` once the RLP semantics are formalised.

end EvmAsm.Stateless.Witness.MPT.Decode
