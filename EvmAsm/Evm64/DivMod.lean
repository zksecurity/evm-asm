-- AddrNormSmokeTests pins canonical shapes from docs/263-addr-norm-inventory.md
-- so silent gaps in @[divmod_addr] coverage become CI failures (issue #263).
import EvmAsm.Evm64.DivMod.AddrNormSmokeTests
-- Counterexamples pins the n4 call-addback inputs that motivated div128 v4.
import EvmAsm.Evm64.DivMod.Counterexamples
-- Spec is the public stack-spec surface and re-exports the split Spec/*
-- modules. It also covers Compose + FullPathN4 + FullPathN4Beq +
-- ModFullPathN4 + EvmWordArith + ModFullPathN4Shift0 + FullPathN4Shift0.
import EvmAsm.Evm64.DivMod.Spec
-- Shift0Dispatcher → Shift0AddbackMod → SpecCall transitively.
-- FullPathN1LoopUnified transitively covers FullPathN1Loop + FullPathN3Loop,
-- which pull in LoopUnifiedN{1,2,3} + LoopComposeN3 + FullPathN{1,2,3}
-- + FullPathN4Loop → LoopIterN4 → LoopBodyN4 → LoopBody → Compose +
-- LoopDefs + EvmWordArith.DivN4Overestimate. ModFullPathN{1,2,3}LoopUnified
-- cover the MOD n=1/n=2/n=3 wrappers. FullPathN2Bundle carries shared N2
-- irreducible intermediates for later full-wrapper refactors.
-- Removed: import EvmAsm.Evm64.DivMod.Spec.V4 (deleted: 716 LOC of unused v4 closure
-- theorems; SpecCallAddbackBeq is reachable via direct imports).
-- Removed: import EvmAsm.Evm64.DivMod.LoopDefs.IterV4InvariantsPhase2 (deleted:
-- file contained only 2 unused private Phase-2 overshoot lemmas, 464 LOC).

import EvmAsm.Evm64.DivMod.Shift0Dispatcher
import EvmAsm.Evm64.DivMod.SpecCall
import EvmAsm.Evm64.DivMod.N4StackSpec
import EvmAsm.Evm64.DivMod.N4StackSpecWithin
import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeq
import EvmAsm.Evm64.DivMod.LoopBody.DoubleAddbackBeqV4NoNop
import EvmAsm.Evm64.DivMod.LoopBody.MulsubFull
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddback
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqV4NoNop
import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqNamed
import EvmAsm.Evm64.DivMod.Compose.SharedLoopPost
import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN1LoopUnified
import EvmAsm.Evm64.DivMod.LoopUnifiedN1.CallIter210NoNop
import EvmAsm.Evm64.DivMod.LoopUnifiedN1.UnifiedNoNop
import EvmAsm.Evm64.DivMod.LoopIterN2NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2AddbackV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2CallAddbackV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4AddbackV4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN4BeqV4NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN2LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle
import EvmAsm.Evm64.DivMod.Compose.FullPathN4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN4CallV4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNop
