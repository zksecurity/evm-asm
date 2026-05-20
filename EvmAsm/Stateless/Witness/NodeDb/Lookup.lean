/-
  EvmAsm.Stateless.Witness.NodeDb.Lookup

  Lookup a node by its keccak hash. Mirrors Python's
  `node_db[hash]` dict access.

  ## Calling convention

      Input:
        a0 = ptr to 32-byte hash
      Output:
        a0 = ptr to node bytes (0 on miss)
        a1 = node length in bytes (0 on miss)
        a2 = ZKVM_EOK (0) on hit, WITNESS_MISSING_NODE (TBD) on miss

  ## Algorithm (RISC-V plan)

      bucket = hash[0..4] mod NUM_BUCKETS
      walk linked-list at NODE_DB_BUCKETS[bucket]:
        for each (entry_hash, ptr, len):
          if memcmp(entry_hash, hash, 32) == 0:
            return (ptr, len, OK)
        return (0, 0, MISSING_NODE)

  On miss, the caller routes to
  `EvmAsm.Stateless.unimplemented_exit` with reason
  `REASON_WITNESS_MISSING_NODE`. A missing node means the witness
  was incomplete -- the prover did not include a required MPT
  node -- which is a stateless-verification failure.

  ## PR-K9 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Witness.NodeDb.Lookup

-- TODO(stateless-witness): expose `lookup_node(hash_ptr) ->
-- (ptr, len, status)` Program. Walks the NODE_DB_BUCKETS chain.
-- Uses memcmp-by-doubleword over 32 bytes for hash comparison.

end EvmAsm.Stateless.Witness.NodeDb.Lookup
