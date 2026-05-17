/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubFull

  Named-postcondition wrappers for `divK_mulsub_full_spec_within` and
  `divK_mulsub_full_spec_within_noNop`. These expose the mulsub full
  spec with 1 statement let (`uBase`) instead of 35, via `mulsubFullPost`.
-/

import EvmAsm.Evm64.DivMod.LoopBody

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled postcondition for `divK_mulsub_full_spec_within`.
    Hides the 34 mulsub intermediates plus borrow/u4_new; leaves `uBase`
    for address calculations in callers. -/
@[irreducible]
def mulsubFullPost (sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Assertion :=
  let p0_lo := qHat * v0; let p0_hi := rv64_mulhu qHat v0
  let fs0 := p0_lo + (signExtend12 0 : Word)
  let ba0 := if BitVec.ult fs0 (signExtend12 0 : Word) then (1 : Word) else 0
  let pc0 := ba0 + p0_hi; let bs0 := if BitVec.ult u0 fs0 then (1 : Word) else 0
  let un0 := u0 - fs0; let c0 := pc0 + bs0
  let p1_lo := qHat * v1; let p1_hi := rv64_mulhu qHat v1
  let fs1 := p1_lo + c0; let ba1 := if BitVec.ult fs1 c0 then (1 : Word) else 0
  let pc1 := ba1 + p1_hi; let bs1 := if BitVec.ult u1 fs1 then (1 : Word) else 0
  let un1 := u1 - fs1; let c1 := pc1 + bs1
  let p2_lo := qHat * v2; let p2_hi := rv64_mulhu qHat v2
  let fs2 := p2_lo + c1; let ba2 := if BitVec.ult fs2 c1 then (1 : Word) else 0
  let pc2 := ba2 + p2_hi; let bs2 := if BitVec.ult u2 fs2 then (1 : Word) else 0
  let un2 := u2 - fs2; let c2 := pc2 + bs2
  let p3_lo := qHat * v3; let p3_hi := rv64_mulhu qHat v3
  let fs3 := p3_lo + c2; let ba3 := if BitVec.ult fs3 c2 then (1 : Word) else 0
  let pc3 := ba3 + p3_hi; let bs3 := if BitVec.ult u3 fs3 then (1 : Word) else 0
  let un3 := u3 - fs3; let c3 := pc3 + bs3
  let borrow := if BitVec.ult uTop c3 then (1 : Word) else 0
  let u4_new := uTop - c3
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
  (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_new) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ borrow) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3) **
  (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ j) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3) **
  ((uBase + signExtend12 4064) ↦ₘ u4_new)

end EvmAsm.Evm64
