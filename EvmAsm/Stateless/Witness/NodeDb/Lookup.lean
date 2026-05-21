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

  ## PR-K19 status

  Asm implementation lands in
  `EvmAsm.Codegen.Programs.witnessLookupByHashFunction`. PR-K19
  ships the linear-scan version (O(N) per lookup): walk every
  entry in the SSZ list, compute `keccak256(entry_bytes)`, and
  compare against the target hash. The bucket-chain layout
  described above remains the eventual target -- a follow-up
  PR replaces the linear scan with a pre-built bucket table.

  ## Calling convention (linear scan, PR-K19)

      Input:
        a0 (input)  : SSZ list section ptr (e.g. witness.state
                      or witness.codes section bytes)
        a1 (input)  : section_len
        a2 (input)  : 32-byte target hash ptr
        a3 (input)  : u64 output ptr (receives byte offset
                      within section where the matched entry
                      starts; meaningful only on hit)
        a4 (input)  : u64 output ptr (receives byte length of
                      the matched entry; meaningful only on hit)
        ra (input)  : return

      Output:
        a0 = 0  on hit (entry found)
        a0 = 1  on miss (no entry has the target hash, or
                section was empty)

  Caller computes the matched entry's byte pointer as
  `section_ptr + *out_start_offset`.

  ## Implementation shape

  Uses one 32-byte `.data` scratch (`wlh_scratch_hash`) for the
  per-iteration keccak output. No element-count cap (linear
  scan).
-/

namespace EvmAsm.Stateless.Witness.NodeDb.Lookup

-- TODO(stateless-witness): expose a `cpsTripleWithin` spec
-- over `witness_lookup_by_hash` once the abstract DB semantics
-- are formalised.

end EvmAsm.Stateless.Witness.NodeDb.Lookup
