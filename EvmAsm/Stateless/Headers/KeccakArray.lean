/-
  EvmAsm.Stateless.Headers.KeccakArray

  Sibling of `KeccakChain` (PR-K15). Walks the same SSZ list
  section but writes EVERY element's keccak256 digest into a
  caller-supplied 32-byte slot, producing an `N × 32`-byte
  table.

  ## Why

  `keccak_chain` (PR-K15) only surfaces the last digest, which
  is sufficient for the lightest-weight chain validation
  (parent_hash check needs only the immediately preceding
  hash). The MPT layer (`Witness/NodeDb`, `Witness/CodeDb`)
  needs *every* digest indexed by position so that downstream
  MPT walks can look up nodes by hash.

  `keccak_array` is therefore the building block for:

    - `build_node_db`: hash every entry in `witness.state`,
      build a `hash → bytes` lookup. PR-K17+ wraps this with
      the bucket-table machinery.
    - `build_code_db`: same shape over `witness.codes`.
    - `validate_headers` (richer variant): hash every entry in
      `witness.headers`, then walk the parent_hash chain
      against the full array (rather than just the last hash).

  ## Contract

  Caller convention:

      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len (0 = empty list)
      a2 (input)  : table base ptr (caller-allocated; must hold
                    `N * 32` writable bytes)
      ra (input)  : return

      a0 (output) : N (element count; 0 if section empty)
      32 bytes at *(table + 32*i) = keccak256(element[i])
        for each i in 0..N. Memory beyond `table + 32*N` is
        not touched.

  Like `keccak_chain`, no element-count cap -- the function is
  a single linear pass over the section. Caller is responsible
  for sizing the table.

  ## Implementation shape

  `headersKeccakArrayFunction` emits `headers_keccak_array:`.
  Same SSZ parsing as `KeccakChain`, but each loop iteration
  computes `out_ptr = table + 32 * i` instead of overwriting
  the same slot. Three differences from `KeccakChain`:

    1. The output slot is reset per-iteration (`a2 = table + 32*i`).
    2. The function still returns `N` in `a0`.
    3. No "N = 0 zero-fill" path -- if `N = 0`, the table is
       simply not touched (caller saw 0 returned and knows the
       slot is meaningless).

  ## PR-K16 status

  Defines the contract. The executable lives in the standalone
  `zisk_headers_keccak_array` probe. PR-K17+ wires this into
  `build_node_db` / `build_code_db`.
-/

namespace EvmAsm.Stateless.Headers

-- TODO(stateless-headers): expose a `cpsTripleWithin` spec
-- once the encoder's overall side-effect surface is captured.

end EvmAsm.Stateless.Headers
