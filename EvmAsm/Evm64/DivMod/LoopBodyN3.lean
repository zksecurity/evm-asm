/-
  EvmAsm.Evm64.DivMod.LoopBodyN3

  Fixed loop body compositions for n=3 (3-limb divisor).
  Eliminates the uAddr/window-cell and vtop/v2 overlaps in the generic spec.

  For n=3, three address overlaps exist:
  1. uAddr = uBase + signExtend12 4072  (both refer to u[j+3])
  2. uAddr + 8 = uBase + signExtend12 4080  (both refer to u[j+2])
  3. vtopBase + signExtend12 32 = sp + signExtend12 48  (both refer to v[2])

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
-- Address rewriting lemmas for n=3 (no let-bindings, suitable for rw)
-- ============================================================================

/-- For n=3: uAddr = uBase + signExtend12 4072 -/
theorem u_addr_eq_n3 {sp j : Word} :
    sp + signExtend12 4056 - (j + (3 : Word)) <<< (3 : BitVec 6).toNat =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  divmod_addr

/-- For n=3: (uBase + signExtend12 4072) + 8 = uBase + signExtend12 4080 -/
theorem u_addr8_eq_n3 {sp j : Word} :
    ((sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4072) + 8 =
    (sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  divmod_addr

/-- For n=3: vtopBase + signExtend12 32 = sp + signExtend12 48 -/
theorem vtop_eq_v2_n3 {sp : Word} :
    (sp + ((3 : Word) + signExtend12 4095) <<< (3 : BitVec 6).toNat) + signExtend12 32 =
    sp + signExtend12 48 := by
  divmod_addr

end EvmAsm.Evm64


