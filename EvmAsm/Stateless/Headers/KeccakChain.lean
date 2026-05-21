/-
  EvmAsm.Stateless.Headers.KeccakChain

  Iterate over an SSZ-encoded list of byte-strings (the SSZ shape
  used by `witness.headers` and `witness.state` /
  `witness.codes`), compute `keccak256(element_bytes)` for each
  element, and surface the last element's hash and the element
  count to the caller.

  ## Why

  Ethereum-side validation of the witness lists treats every
  entry as an opaque byte string and identifies it by its
  `keccak256` digest:

    - `witness.state`  : node_db keyed by keccak256(node_bytes)
    - `witness.codes`  : code_db keyed by keccak256(code_bytes)
    - `witness.headers`: per-header block hash for chain check

  The `keccak_chain` primitive walks one such list and stamps
  the digest of its *last* element to the caller's output
  buffer (and returns the element count). Higher-level passes
  use this as the building block for:

    - `validate_headers`: each `header.parent_hash` must equal
      keccak256 of the preceding header bytes; the chain ends
      with the per-block hash this primitive produces.
    - `build_node_db` / `build_code_db`: a follow-up PR keeps
      ALL the digests (not just the last one) in a `.bss`
      lookup table for MPT walks to query.

  This PR ships the simplest read-only flavour: walk the list,
  hash each element, and surface the last digest.

  ## SSZ list section format (same as PR-S11)

      bytes  0 .. 4N        : N u32 LE inner offsets
      bytes  4N .. end      : concatenated element bytes

  `N = offset_0 / 4` for non-empty sections. An empty section
  (`section_len = 0`) represents `N = 0`.

  ## Contract

  Caller convention:

      a0 (input)  : SSZ list section ptr (read-only)
      a1 (input)  : section_len in bytes (0 = empty list)
      a2 (input)  : 32-byte output ptr (receives last-element
                    digest; zeroed if N = 0)
      ra (input)  : return

      a0 (output) : N (element count; 0 for empty section)
      32 bytes at *a2 : keccak256(element[N-1]) if N > 0, else 0

  Cap: no element count cap (the function is a straight loop
  through the section without any scratch state proportional to
  N).

  ## Implementation shape

  `headersKeccakChainFunction` emits the labelled function
  `headers_keccak_chain:`. Internally it reads the inner-offset
  table, iterates `i = 0..N`, and on each iteration calls
  `zkvm_keccak256(el_i_start, el_i_len, last_hash_out)` --
  reusing the caller-supplied output buffer as a single
  rolling 32-byte slot. After the last iteration the slot
  contains exactly the last element's digest; the function
  returns `N` in `a0`.

  No new `.data` scratch is needed beyond what `zkvm_keccak256`
  already requires (the 200-byte sponge state at
  `zk3_state`).

  ## PR-K15 status

  Defines the contract. The executable lives where it's
  inlined (the dedicated probe `zisk_headers_keccak_chain` is
  the standalone smoke test). PR-K16+ wires this into the
  stateless guest's output as a diagnostic field at
  `OUTPUT[56..88]`, alongside the existing
  `header_count` (PR6) and SSZ root (PR-K7 keccak stub) fields.
-/

namespace EvmAsm.Stateless.Headers

-- TODO(stateless-headers): expose a `cpsTripleWithin` spec
-- once the encoder's overall side-effect surface is captured.

end EvmAsm.Stateless.Headers
