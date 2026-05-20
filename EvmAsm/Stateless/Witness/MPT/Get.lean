/-
  EvmAsm.Stateless.Witness.MPT.Get

  Top-level `mpt_get(root, key) -> Option Bytes`. Composes `Walk`
  + key hashing (Ethereum MPTs use `keccak256(key)` as the path
  nibbles for account/storage tries).

  ## Algorithm

      def mpt_get(root, key):
          path = keccak256(key) as nibbles    # 64 nibbles
          return walk(root, path)

  ## RISC-V plan

  1. Call `zkvm_keccak256(key_ptr, key_len, hash_scratch)`.
  2. Expand hash_scratch's 32 bytes into 64 nibbles (4-bit halves)
     at a scratch slot.
  3. Call `mpt_walk(root_hash, nibble_ptr, 64)`.

  ## PR-K9 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.Witness.MPT.Get

-- TODO(stateless-witness): expose `mpt_get(root, key_ptr,
-- key_len) -> (value_ptr, value_len)`.

end EvmAsm.Stateless.Witness.MPT.Get
