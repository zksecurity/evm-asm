/-
  EvmAsm.Stateless.VM.Precompiles

  Dispatch for precompile addresses (0x01..0x14 + 0x100 for
  P256VERIFY). All precompile calls in the stateless guest route
  here, and **every dispatch routes to `unimplemented_exit`**
  with the precompile-specific reason code.

  ## Why precompiles are out of scope

  Per the project plan (see `~/.claude/plans/please-cut-a-branch-warm-wand.md`
  and `PLAN.md` "Stateless Guest"), precompile dispatch is
  explicitly out of scope for the first pass:

  - ECRECOVER, SHA-256, RIPEMD-160, IDENTITY, MODEXP
  - ALT_BN128 ADD / MUL / PAIRING (BN254)
  - BLAKE2F
  - POINT_EVALUATION (EIP-4844 KZG)
  - BLS12-381 G1/G2 ADD/MSM, PAIRING, MAP
  - SECP256R1_VERIFY (P256)

  Each call site triggers `REASON_PRECOMPILE + addr` per the
  reason-code table in `Stateless/Unimplemented.lean`.

  ## What's NOT in this file

  Hashes needed for **block processing** (KECCAK256 for header
  hashing, MPT, code hashing, tx hashing, address derivation;
  SHA-256 for SSZ Merkleization of the output) are bridged
  separately and do NOT route through this file. They live in
  `EvmAsm/EL/Keccak*EcallBridge.lean` (existing) and
  `EvmAsm/Stateless/Bridges/Sha256EcallBridge.lean` (scaffolded
  in PR-K12). See `docs/execution-specs-feedback.md` #1 for the
  cost-picture discussion.

  ## PR-K12 status

  Scaffold only.
-/

namespace EvmAsm.Stateless.VM.Precompiles

-- TODO(stateless-vm): expose `precompile_dispatch(address, ...)
-- -> unimplemented_exit(REASON_PRECOMPILE + address)`. Trivial
-- dispatcher.

end EvmAsm.Stateless.VM.Precompiles
