/-
  EvmAsm.Stateless.Entry

  Top-level `run_stateless_guest` Program. Mirrors the Python
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py:33`
  entry point.

  Once `Stateless.SSZ.Decode`, `Stateless.Headers`, `Stateless.Witness`,
  `Stateless.Block`, `Stateless.Transaction`, and `Stateless.VM` are
  populated, this file will compose them in the canonical order:

  ```
  read_input from INPUT_ADDR + INPUT_DATA_OFFSET
      |
      v
  Stateless.SSZ.Decode.deserialize_stateless_input
      |
      v
  Stateless.Headers.validate_headers
      |
      v
  Stateless.Witness.{NodeDb,CodeDb}.build
      |
      v
  Stateless.ExecutionEngine.execute_new_payload_request
      | (recursively into Block / Transaction / VM)
      v
  Stateless.SSZ.Encode.serialize_stateless_output
      |
      v
  write_output to OUTPUT_ADDR + 0
      |
      v
  HALT
  ```

  ## Memory layout (preconditions)
  - `INPUT_ADDR + INPUT_DATA_OFFSET` holds the host-supplied
    SSZ-encoded `SszStatelessInput`.
  - All RAM in `STATELESS_WORK_BASE .. STATELESS_WORK_BASE + 0x20000000`
    is available for scratch (see `MemoryLayout.lean`).

  ## Side effects (postconditions when fully implemented)
  - Writes the SSZ encoding of `StatelessValidationResult` to
    `OUTPUT_ADDR + 0..N`.
  - Halts with the codegen halt stub.

  ## PR4 status

  Decode + light validation:
    - `Stateless.SSZ.Decode.read_chain_id` reads `chain_id` from the
      host-supplied `SszStatelessInput` on `INPUT_ADDR` into `x10`.
    - `Stateless.SSZ.Decode.decode_validation_bit` reads `offset_1`
      and `offset_3` from the SSZ container header, computes
      `witness_body_length = offset_3 - offset_1`, and sets `x11` to
      `1` iff the witness is empty (body length `== 12`).

  Encode:
    - `Stateless.SSZ.Encode.serialize_stateless_output` writes the
      41-byte SSZ encoding of
      `StatelessValidationResult(root = 0, valid = x11, chain_id = x10)`
      at `OUTPUT_ADDR`.

  Header validation, witness DBs, and STF execution are still
  stubbed. Module paths that aren't implemented yet still call
  `EvmAsm.Stateless.unimplemented_exit` with a distinct reason code
  (precompiles, missing witness nodes, etc.) -- see
  `EvmAsm/Stateless/Unimplemented.lean`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.SSZ.Decode.Program
import EvmAsm.Stateless.SSZ.Encode.Program

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-- PR4 body: decode `chain_id` + validation bit from `INPUT_ADDR`,
    then encode the `StatelessValidationResult` at `OUTPUT_ADDR`.
    Falls through to the halt stub appended by `emitBuildUnit`.

    Replaced in successor PRs by the full decode → validate → execute
    → encode pipeline. -/
def run_stateless_guest : Program :=
  EvmAsm.Stateless.SSZ.Decode.read_chain_id ++
  EvmAsm.Stateless.SSZ.Decode.decode_validation_bit ++
  EvmAsm.Stateless.SSZ.Encode.serialize_stateless_output

end EvmAsm.Stateless
