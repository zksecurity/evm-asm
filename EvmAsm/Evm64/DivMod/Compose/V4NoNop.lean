/-
  EvmAsm.Evm64.DivMod.Compose.V4NoNop

  Shared no-NOP code surface for v4 div128 migration.
-/

import EvmAsm.Evm64.DivMod.Compose.Base

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 mirror of `sharedDivModCodeNoNop`: shared DIV/MOD blocks with the
    NOP return slot omitted and the final block using `divK_div128_v4`. -/
abbrev sharedDivModCodeNoNop_v4 (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg  base                  (divK_phaseA 1020),
    CodeReq.ofProg (base + phaseBOff)     divK_phaseB,
    CodeReq.ofProg (base + clzOff)        divK_clz,
    CodeReq.ofProg (base + phaseC2Off)    (divK_phaseC2 172),
    CodeReq.ofProg (base + normBOff)      divK_normB,
    CodeReq.ofProg (base + normAOff)      (divK_normA 40),
    CodeReq.ofProg (base + copyAUOff)     divK_copyAU,
    CodeReq.ofProg (base + loopSetupOff)  (divK_loopSetup 464),
    CodeReq.ofProg (base + loopBodyOff)   (divK_loopBody 560 7736),
    CodeReq.ofProg (base + denormOff)     divK_denorm,
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    CodeReq.ofProg (base + div128Off)     divK_div128_v4
  ]

/-- v4 div128 block is included in `sharedDivModCodeNoNop_v4 base`. -/
theorem sharedNoNop_b11_div128_v4_sub {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128_v4) a = some i →
           (sharedDivModCodeNoNop_v4 b) a = some i := by
  unfold sharedDivModCodeNoNop_v4; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left

end EvmAsm.Evm64
