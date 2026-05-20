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

  ## PR-K9 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Witness.MPT.Walk

-- TODO(stateless-witness): expose `mpt_walk(root, path_nibbles,
-- path_len) -> (ptr, len)`.

end EvmAsm.Stateless.Witness.MPT.Walk
