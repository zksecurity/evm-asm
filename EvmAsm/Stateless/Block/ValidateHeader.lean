/-
  EvmAsm.Stateless.Block.ValidateHeader

  Validate a single block header against its parent. Mirrors
  Python's `validate_header` from `forks/amsterdam/fork.py`.

  ## Checks (Yellow Paper / fork-specific)

  - `header.parent_hash == keccak256(rlp(parent_header))`
  - `header.timestamp > parent_header.timestamp`
  - `header.gas_used <= header.gas_limit`
  - `|header.gas_limit - parent_header.gas_limit| <
     parent_header.gas_limit / 1024` (gas limit drift)
  - `header.number == parent_header.number + 1`
  - `header.base_fee_per_gas` follows EIP-1559 formula
  - `header.blob_gas_used` <= MAX_BLOB_GAS (EIP-4844)
  - `header.excess_blob_gas` per EIP-4844 schedule

  ## Reuse

  - `Stateless.Headers.BlockHash` for the parent-hash check.
  - `Stateless.Headers.Decode` to lift fields out of the parent
    header RLP.
  - U256 / Uint comparison helpers from `Evm64/`.

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Block.ValidateHeader

-- TODO(stateless-block): expose `validate_header(header,
-- parent_header)` Program. Routes failures to
-- `unimplemented_exit` with a header-specific reason code.

end EvmAsm.Stateless.Block.ValidateHeader
