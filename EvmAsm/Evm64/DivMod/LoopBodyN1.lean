/-
  EvmAsm.Evm64.DivMod.LoopBodyN1

  Fixed loop body compositions for n=1 (1-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v0 overlaps in the generic spec.

  For n=1, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4088  (both refer to u[j+1])
  2. uAddr + 8 = uBase + signExtend12 0  (both refer to u[j+0])
  3. vtopBase + signExtend12 32 = sp + signExtend12 32  (both refer to v[0])

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
-- Address rewriting lemmas for n=1 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=1: uAddr = uBase + signExtend12 4088 -/
theorem u_addr_eq_n1 {sp j : Word} :
    sp + signExtend12 4056 - (j + (1 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  divmod_addr

/-- For n=1: (uBase + signExtend12 4088) + 8 = uBase + signExtend12 0 -/
theorem u_addr8_eq_n1 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4088) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 0 := by
  divmod_addr

/-- For n=1: vtopBase + signExtend12 32 = sp + signExtend12 32 -/
theorem vtop_eq_v0_n1 {sp : Word} :
    (sp + ((1 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 32 := by
  divmod_addr

end EvmAsm.Evm64
