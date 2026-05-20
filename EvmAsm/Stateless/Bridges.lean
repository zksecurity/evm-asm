/-
  EvmAsm.Stateless.Bridges

  Umbrella for the cryptographic-accelerator bridges the stateless
  guest needs **inside** block processing (i.e. NOT precompile
  dispatch -- see `Stateless.VM.Precompiles`).

  ## Two bridges in this PR

  - **ECRECOVER** (`Ecrecover*EcallBridge.lean`) for transaction
    sender recovery. Same shape as the existing
    `EvmAsm/EL/Keccak*EcallBridge.lean` (input bridge / result
    bridge / ECALL bridge composition).
  - **SHA-256** (`Sha256EcallBridge.lean`) for SSZ
    `hash_tree_root` computation -- the
    `new_payload_request_root` field of the SSZ output.
    Currently blocked on the ziskemu 0.18.0 vs 0.15.0 source
    layout mismatch (PR-S1 deferred).

  ## What's NOT here

  - **KECCAK256**: already bridged at `EvmAsm/EL/Keccak*EcallBridge.lean`.
    Programs in `Stateless/` call into the existing bridge.
  - Precompile-only crypto (BN254 / BLS12 / Blake2f / KZG /
    P256VERIFY / RIPEMD160): out of scope; precompile dispatch
    routes to `Stateless.VM.Precompiles` which routes to
    `unimplemented_exit`.

  ## PR-K12 status

  Scaffolds only -- no live Programs yet.
-/

import EvmAsm.Stateless.Bridges.EcrecoverEcallBridge
import EvmAsm.Stateless.Bridges.EcrecoverInputBridge
import EvmAsm.Stateless.Bridges.EcrecoverResultBridge
import EvmAsm.Stateless.Bridges.Sha256EcallBridge
