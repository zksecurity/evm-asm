/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4NoNop

  No-NOP wrappers for the n=4 DIV full path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=4 DIV path over `divCode_noNop`: base → base+1068
    (shift ≠ 0, max+skip). -/
theorem evm_div_n4_full_max_skip_spec_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hbltu : isMaxTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Max a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10) base (base + nopOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem))
      (fullDivN4MaxSkipPost sp a0 a1 a2 a3 b0 b1 b2 b3) := by
  have hA := evm_div_n4_preloop_max_skip_spec_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    hbnz hb3nz hshift_nz hbltu hborrow
  have hB := evm_div_n4_max_skip_denorm_epilogue_spec_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hA hB
  exact cpsTripleWithin_mono_nSteps (by decide) hFull

end EvmAsm.Evm64
