/-
  EvmAsm.Stateless.Transaction.Decode

  Decode an Ethereum transaction from its RLP-encoded bytes.
  Mirrors Python's `decode_transaction` from
  `forks/amsterdam/transactions.py`.

  ## Wire format (post-Berlin)

  Type-prefix dispatch:
    - Byte 0 == 0x01: EIP-2930 access list (LegacyAccessList)
    - Byte 0 == 0x02: EIP-1559 dynamic fee
    - Byte 0 == 0x03: EIP-4844 blob
    - Byte 0 == 0x04: EIP-7702 set code
    - Else: legacy (full RLP from byte 0)

  Each type has its own RLP body shape (different number of
  fields, different ordering). The decoder dispatches and lifts
  into a flat in-memory tx struct (PR-K11 uses a per-type
  scratch slot).

  ## EIP-7702 / 4844 caveats

  PR-K11 scaffolds these but the implementation routes both to
  `unimplemented_exit` with reason `REASON_EIP7702_DELEGATION`
  or `REASON_EIP4844_BLOB`. (See PR1 / `Stateless.Unimplemented`.)
  PR-K1x lifts the restrictions once we have ECRECOVER and KZG
  in scope.

  ## PR-K11 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Transaction.Decode

-- TODO(stateless-tx): expose `decode_transaction(ptr, len, out)`
-- with type-prefix dispatch.

end EvmAsm.Stateless.Transaction.Decode
