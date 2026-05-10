/-
  EvmAsm.Evm64.Exp.Compose.SquaringStep

  Small EXP full-loop building blocks around the squaring call path.
-/

import EvmAsm.Evm64.Exp.Compose.TopCodeSpecs

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Squaring unmarshal word spec lifted to the top-level EXP code bundle
    unioned with the shared `mul_callable` code. -/
theorem exp_squaring_un_marshal_word_evm_exp_union_spec_within
    (sp evmSp tOld r0 r1 r2 r3 mulTarget : Word) (w : EvmWord)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base : Word) :
    cpsTripleWithin 9 (base + 108) (base + 144)
      ((evmExpCode base mulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) w)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ w.getLimbN 3) **
       evmWordIs sp w ** evmWordIs (evmSp + 32) w) := by
  have h := exp_squaring_un_marshal_word_evm_exp_spec_within
    sp evmSp tOld r0 r1 r2 r3 w mulOff skipOff backOff base
  exact cpsTripleWithin_extend_code (h := h) (hmono := by
    intro a i hcode
    exact CodeReq.union_mono_left a i hcode)

end EvmAsm.Evm64.Exp.Compose
