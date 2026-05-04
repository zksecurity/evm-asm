/-
  EvmAsm.Evm64.DivMod.LoopBodyN2

  Fixed loop body compositions for n=2 (2-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v1 overlaps in the generic spec.

  For n=2, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4080  (both refer to u[j+2])
  2. uAddr + 8 = uBase + signExtend12 4088  (both refer to u[j+1])
  3. vtopBase + signExtend12 32 = sp + signExtend12 40  (both refer to v[1])

  This file eliminates these overlaps by:
  - Expanding the trial spec's let-bindings via dsimp
  - Rewriting uAddr and vtopBase to canonical uBase-relative form
  - Framing only with cells NOT already in the trial spec
  - Composing without cell duplication in any separating conjunction
-/

import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.DivMod.LoopBody.TrialMax
import EvmAsm.Evm64.DivMod.LoopBody.StoreLoop
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq
import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionSkip

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address rewriting lemmas for n=2 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=2: uAddr = uBase + signExtend12 4080 -/
theorem u_addr_eq_n2 {sp j : Word} :
    sp + signExtend12 4056 - (j + (2 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- For n=2: (uBase + signExtend12 4080) + 8 = uBase + signExtend12 4088 -/
theorem u_addr8_eq_n2 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- For n=2: vtopBase + signExtend12 32 = sp + signExtend12 40 -/
theorem vtop_eq_v1_n2 {sp : Word} :
    (sp + ((2 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 40 := by
  divmod_addr

end EvmAsm.Evm64


