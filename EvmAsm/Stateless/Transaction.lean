/-
  EvmAsm.Stateless.Transaction

  Umbrella for the transaction-level STF subtree. Mirrors the
  Python helpers in `forks/amsterdam/transactions.py` and
  `fork.py:process_transaction`.

  ## Subtree

  - `Decode.lean`        — `decode_transaction(bytes) -> Tx`. Dispatches
                           on the type-prefix byte (0x01 EIP-2930,
                           0x02 EIP-1559, 0x03 EIP-4844 blob,
                           0x04 EIP-7702 setcode, else legacy).
  - `Validate.lean`      — pre-execution sanity: nonce, balance,
                           gas_price >= base_fee, chain_id, etc.
  - `RecoverSender.lean` — `recover_sender(tx) -> Address` via the
                           secp256k1_ecrecover zkvm-standards
                           accelerator (currently Unimplemented;
                           PR-E1 wires the bridge).
  - `Process.lean`       — `process_transaction(tx, sender,
                           tx_state)`: deduct upfront cost, run
                           `execute_message` (VM), refund, pay
                           priority fee. Returns gas_used + success.
  - `Spec.lean`          — cpsTriple placeholders.

  All sub-files are scaffolds in PR-K11.
-/

import EvmAsm.Stateless.Transaction.Decode
import EvmAsm.Stateless.Transaction.Validate
import EvmAsm.Stateless.Transaction.RecoverSender
import EvmAsm.Stateless.Transaction.Process
import EvmAsm.Stateless.Transaction.Spec
