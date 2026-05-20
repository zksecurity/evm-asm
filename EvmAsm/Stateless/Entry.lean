/-
  EvmAsm.Stateless.Entry

  Top-level `run_stateless_guest` Program. Mirrors the Python
  `execution-specs/src/ethereum/forks/amsterdam/stateless_guest.py:33`
  entry point, but with the body stubbed to `unimplemented_exit
  REASON_STF_BODY` until the SSZ codec, header validator, MPT walker,
  and EVM interpreter land in subsequent PRs.

  Once `Stateless.SSZ.Decode`, `Stateless.SSZ.Encode`,
  `Stateless.Headers`, `Stateless.Witness`, `Stateless.Block`,
  `Stateless.Transaction`, and `Stateless.VM` are populated, this file
  will compose them in the canonical order:

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
  - Halts with `t0 = 0`.

  Current PR1 stub: jumps straight to `unimplemented_exit` with
  `REASON_STF_BODY` so the build wires together and the codegen path
  produces a runnable ELF whose output marker can be diffed by the
  Python harness.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Stateless.MemoryLayout
import EvmAsm.Stateless.Unimplemented

namespace EvmAsm.Stateless

open EvmAsm.Rv64

/-- PR1 stub: load `REASON_STF_BODY` into `a0` and fall through to
    `unimplemented_exit`. The whole stateless guest body is one
    `LI` instruction followed by the 6-instruction `unimplemented_exit`
    sequence. -/
def run_stateless_guest : Program :=
  LI .x10 REASON_STF_BODY ;;
  unimplemented_exit

end EvmAsm.Stateless
