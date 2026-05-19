/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

  Small control-invariant helpers for the fixed-loop induction frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedControlInvariant_nextLimb
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  exact hControl.2

theorem expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  rw [expTwoMulFixedControlInvariant_nextLimb hControl]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

end EvmAsm.Evm64.Exp.Compose
