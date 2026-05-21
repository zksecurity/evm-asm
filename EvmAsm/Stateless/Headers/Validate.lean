/-
  EvmAsm.Stateless.Headers.Validate

  Validate that a sequence of RLP-encoded block headers forms a
  contiguous chain. Mirrors the Python `validate_headers` from
  `execution-specs/src/ethereum/forks/amsterdam/stateless.py:178`:

      def validate_headers(encoded_headers):
          assert len(encoded_headers) <= 256, "Too many headers"
          headers      = [_decode_header(b)  for b in encoded_headers]
          block_hashes = [keccak256(b)        for b in encoded_headers]
          for i in range(1, len(headers)):
              if headers[i].parent_hash != block_hashes[i-1]:
                  raise Exception("not contiguous")
          return headers, block_hashes

  ## Algorithm

  Inputs (already navigated to by the caller via
  `EvmAsm.Stateless.SSZ.Decode`):
  - `headers_section_addr` : start of witness.headers SSZ list
  - `headers_section_len`  : section length in bytes
  - `n_headers`            : count derived from first inner u32

  For each header `i in 0..n_headers`:
  1. Compute `el_i_start`, `el_i_end` via the inner offsets table.
  2. `block_hashes[i] := keccak256(bytes[el_i_start..el_i_end])`.
     (Uses `Stateless.Headers.BlockHash`.)
  3. If `i > 0`:
     - RLP-decode `headers[i]` (just enough to extract the
       `parent_hash` field at byte offset 0 of the outer list).
     - Compare `parent_hash == block_hashes[i-1]`.
     - On mismatch, route to `Unimplemented` (PR1 reason
       `WITNESS_NOT_CONTIGUOUS` -- new code to add).

  Output: each `block_hashes[i]` written to a fixed-layout slot
  in `EXECUTION_WITNESS_AREA` (see `MemoryLayout.lean`). The
  decoded headers' `parent_hash` and `state_root` fields are also
  exposed for `Block/Execute` to consume.

  ## Constraint: max 256 headers

  The Python helper asserts `len(encoded_headers) <= 256`. On
  the RISC-V side this becomes a `BNE/BGE` check against
  `n_headers` early; overflow routes to `Unimplemented`.

  ## PR-K18 status

  Asm implementation lands in
  `EvmAsm.Codegen.Programs.headersValidateChainFunction`,
  composing PR-K16 `headers_keccak_array` (per-header digest
  table) with PR-K17 `headers_parent_hash` (RLP extraction).

  Calling convention (`headers_validate_chain`):
    a0 (input)  : SSZ list section ptr (witness.headers)
    a1 (input)  : section_len
    a2 (input)  : u64 output ptr (receives element count N)
    ra (input)  : return
    a0 (output) : 0  iff every `header[i].parent_hash` for i ≥ 1
                    equals `keccak256(header[i-1])`
                    AND every header's RLP-decode of the first
                    field succeeds
                 1  on any mismatch (or RLP-decode failure)
    8 bytes at *a2 = N (element count)

  N ≤ 1 always returns 0 (no chain links to check).

  ## Side effects

  Uses a 256 × 32 = 8 KB `.data` scratch (`vh_keccak_table`)
  to hold every per-header digest; reuses
  `vh_extracted_parent_hash` (32 B) as a one-slot scratch for
  the RLP-extracted field. PR-K18+ exports this same scratch
  area as the `block_hashes[]` lookup that
  `Block/Execute` consumes (mirroring
  `EXECUTION_WITNESS_AREA` in `MemoryLayout.lean`).

  ## Wiring

  Standalone probe `zisk_headers_validate_chain` exercises the
  function on synthetic SSZ-encoded header lists. PR-K19+ wires
  it into the stateless guest's STF.
-/

namespace EvmAsm.Stateless.Headers.Validate

-- TODO(stateless-headers): expose a `cpsTripleWithin` spec
-- over `headers_validate_chain` once the per-header keccak
-- semantics are formalised.

end EvmAsm.Stateless.Headers.Validate
