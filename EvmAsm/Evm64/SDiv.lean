/-
  EvmAsm.Evm64.SDiv

  Umbrella for the SDIV opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SDiv`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `sdiv_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.SDiv.AddrNormAttr
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm
import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Evm64.SDiv.Spec
