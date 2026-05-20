/-
  EvmAsm.Stateless.EntrySpec

  Placeholder for the top-level `cpsTripleWithin` spec of
  `Stateless.Entry.run_stateless_guest`.

  Final form (post all PRs):
    given an SSZ-encoded `SszStatelessInput` on `INPUT_ADDR`,
    `run_stateless_guest` reaches HALT and the bytes on `OUTPUT_ADDR`
    equal the SSZ encoding of the Python reference's
    `verify_stateless_new_payload` output.

  PR1 form (current): no spec; the body is `unimplemented_exit`. The
  spec will be added in lock-step with the SSZ codec PR.

  TODO(stateless-proofs): per-module cpsTripleWithin specs feed into
  this top-level statement. See `EvmAsm/Stateless/MemoryLayout.lean`
  for the memory contract.
-/

import EvmAsm.Stateless.Entry

namespace EvmAsm.Stateless

-- TODO(stateless-proofs): theorem run_stateless_guest_spec : ...

end EvmAsm.Stateless
