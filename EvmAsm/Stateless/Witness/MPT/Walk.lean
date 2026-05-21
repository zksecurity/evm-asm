/-
  EvmAsm.Stateless.Witness.MPT.Walk

  Drive an MPT walk along a nibble path starting from a given
  root hash.

  ## Algorithm (Python `IncrementalMPT.get` analogue)

      def walk(root_hash, path_nibbles):
          node = node_db[root_hash]
          decoded = decode(node)
          nibble_consumed = 0
          while nibble_consumed < len(path_nibbles):
              match decoded.variant:
                  case Branch:
                      next_ref = decoded.children[path[nibble_consumed]]
                      nibble_consumed += 1
                  case Extension:
                      assert path matches decoded.prefix
                      next_ref = decoded.child_ref
                      nibble_consumed += len(decoded.prefix)
                  case Leaf:
                      assert remaining_path == decoded.prefix
                      return decoded.value
              # Dereference next_ref:
              if next_ref is a 32-byte hash:
                  node = node_db[next_ref]
              else (inlined RLP < 32 bytes):
                  node = next_ref
              decoded = decode(node)
          # Branch's value-slot at the consumed prefix
          return decoded.value16

  ## RISC-V plan

  Loop, calling:
  - `Decode` for each fetched node to get the variant + field
    offsets.
  - `NodeDb.Lookup` to chase 32-byte hashes.

  Output the matched value as `(ptr, len)` or `(0, 0)` on
  not-found.

  ## PR-K24 status

  Implementation lands in
  `EvmAsm.Codegen.Programs.mptWalkFunction`. Composes the
  K-stack primitives:

    PR-K19  `witness_lookup_by_hash`   hash → bytes in witness
    PR-K20  `rlp_list_nth_item`        RLP item content extraction
    PR-K21  `mpt_node_kind`            leaf / extension / branch
    PR-K22  `mpt_branch_child`         branch slot (hash / empty / inline)
    PR-K23  `hp_decode_nibbles`        leaf / extension path nibbles
    PR-K3   `zkvm_keccak256`           per-element hashing

  ## Calling convention

      Input:
        a0 (input)  : root_hash ptr (32 bytes)
        a1 (input)  : witness.state SSZ list section ptr
        a2 (input)  : witness section_len
        a3 (input)  : path_nibbles ptr (one byte per nibble in [0..15])
        a4 (input)  : path_nibbles_len
        a5 (input)  : value output buffer ptr (256 bytes)
        a6 (input)  : u64 out ptr (matched value byte length)
        ra (input)  : return

      Output:
        a0 = 0  found (32 bytes at *a5 = value bytes; *a6 = length)
        a0 = 1  not found (path leads to empty branch slot or
                a leaf/extension that doesn't match the path)
        a0 = 2  parse error (RLP malformed, hash not in witness,
                or unsupported node form)

  Value buffer cap: 256 bytes. Larger values truncate to 256.

  ## Limits

  Path length capped at 128 nibbles (the typical Ethereum
  storage trie depth -- 64 bytes / 128 nibbles). MPT nodes
  themselves can be arbitrarily large since their bytes live
  in the witness section.

  Inlined branch children (RLP < 32 bytes) are walked
  recursively without a witness lookup. mpt_branch_child writes
  them zero-padded to 32 bytes; the trailing zeros are
  harmless because RLP self-describes its length.

  Path nibbles MUST be one-byte-per-nibble. A future helper
  converts byte-keyed paths (e.g. address[:20]) into nibble
  arrays.

  ## Test fixtures

  See `scripts/codegen-zisk-mpt-walk-check.sh`. Tests cover:
    * Empty witness → not found.
    * 1-leaf MPT where path matches → found.
    * 1-leaf MPT where path mismatches → not found.
    * 2-leaf MPT with branch root (different first nibbles).
    * Multi-level MPT with extension + branch + leaf.
-/

namespace EvmAsm.Stateless.Witness.MPT.Walk

-- TODO(stateless-witness): expose a `cpsTripleWithin` spec
-- over `mpt_walk` once the K-stack primitive specs are
-- formalised.

end EvmAsm.Stateless.Witness.MPT.Walk
