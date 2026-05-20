/-
  EvmAsm.Stateless.Witness.NodeDb.Program

  Build the keccak-indexed lookup table for MPT nodes from
  `witness.state` (an SSZ List of variable-length ByteLists).

  ## Algorithm (Python reference)

      def build_node_db(state):
          return {keccak256(node_bytes): node_bytes for node_bytes in state}

  ## RISC-V plan

  Input -- already navigated to by `Stateless.SSZ.Decode` (chain
  identical to PR-K7's headers navigation but for the `state`
  field at inner offset 0 instead of `headers` at inner offset 2):

      state_section_addr : start of witness.state list bytes
      state_section_len  : length in bytes

  Iterate:
    For i in 0..N_nodes:
      element_i_start = state_section + inner_offset[i]
      element_i_end   = state_section + inner_offset[i+1] (or section_end)
      element_i_len   = end - start
      h = keccak256(bytes[element_i_start..element_i_end])
      // Insert (h, element_i_start, element_i_len) into NODE_DB_BUCKETS
      bucket_idx = h[0..3] mod NUM_BUCKETS
      append (h, ptr, len) to bucket linked list

  Memory layout for the lookup table lives in
  `Stateless/MemoryLayout.lean` at `NODE_DB_BUCKETS` (4 MiB).

  ## PR-K9 status

  Scaffold only. Composes the keccak wrapper (PR-K3) and the SSZ
  inner-offset navigation primitives (PR-K7). The Program lands
  once the keccak wrapper is available from inside the Stateless
  tree as a Lean callable.
-/

namespace EvmAsm.Stateless.Witness.NodeDb.Program

-- TODO(stateless-witness): expose `build_node_db` Program that
-- walks `witness.state`, keccak-hashes each node via
-- `zkvm_keccak256`, and writes the (hash, ptr, len) tuples to
-- `NODE_DB_BUCKETS`.

end EvmAsm.Stateless.Witness.NodeDb.Program
