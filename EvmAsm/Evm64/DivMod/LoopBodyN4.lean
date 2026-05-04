/-
  EvmAsm.Evm64.DivMod.LoopBodyN4

  Fixed loop body compositions for n=4 (4-limb divisor, m=0, single iteration).
  Eliminates the uAddr/window-cell and vtop/v3 overlaps in the generic spec.

  For n=4, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4064  (both refer to u[j+4])
  2. uAddr + 8 = uBase + signExtend12 4072  (both refer to u[j+3])
  3. vtopBase + signExtend12 32 = sp + signExtend12 56  (both refer to v[3])

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
-- Address rewriting lemmas for n=4 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=4: uAddr = uBase + signExtend12 4064 -/
theorem u_addr_eq_n4 {sp j : Word} :
    sp + signExtend12 4056 - (j + (4 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  divmod_addr

/-- For n=4: (uBase + signExtend12 4064) + 8 = uBase + signExtend12 4072 -/
theorem u_addr8_eq_n4 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4064) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- For n=4: vtopBase + signExtend12 32 = sp + signExtend12 56 -/
theorem vtop_eq_v3_n4 {sp : Word} :
    (sp + ((4 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 56 := by
  divmod_addr

end EvmAsm.Evm64


