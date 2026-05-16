/-
  EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeqNamed

  Named-postcondition wrappers for `divK_mulsub_correction_addback_beq_spec_within`
  and its no-NOP variant. These expose the combined mulsub+addback+BEQ spec with
  5 statement lets instead of 13, via `n4McaBeqPost`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.CorrectionAddbackBeq

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled postcondition for the mulsub+correction_addback+BEQ spec.
    Hides ab, ab', and the 7 conditional output lets. -/
@[irreducible]
def n4McaBeqPost (sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    Assertion :=
  let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  let carryOut := if carry = 0 then addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
                  else carry
  (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
  (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
  (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
  (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3976 ↦ₘ j) **
  ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
  ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
  ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
  ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
  ((uBase + signExtend12 4064) ↦ₘ u4_out)

theorem n4McaBeqPost_unfold {sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word} :
    n4McaBeqPost sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      (let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
       let c3 := ms.2.2.2.2
       let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
       let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
       let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 v0 v1 v2 v3
       let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                    else qHat + signExtend12 4095
       let un0Out := if carry = 0 then ab'.1 else ab.1
       let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
       let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
       let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
       let u4_out := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
       let carryOut := if carry = 0 then addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3
                       else carry
       (.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ q_out) **
       (.x1 ↦ᵣ j) ** (.x5 ↦ᵣ u4_out) ** (.x6 ↦ᵣ uBase) **
       (.x7 ↦ᵣ carryOut) ** (.x10 ↦ᵣ c3) ** (.x2 ↦ᵣ un3Out) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ un0Out) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ un1Out) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ un2Out) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ un3Out) **
       ((uBase + signExtend12 4064) ↦ₘ u4_out)) := by
  delta n4McaBeqPost; rfl

/-- Named-postcondition wrapper for `divK_mulsub_correction_addback_beq_spec_within`.
    5 statement lets (uBase, ms, c3, carry, ab) instead of 13; postcondition in
    `n4McaBeqPost`. -/
theorem divK_mulsub_correction_addback_beq_named_spec_within
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (sharedDivModCode base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      (n4McaBeqPost sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase ms c3 carry ab hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [n4McaBeqPost_unfold]; exact hp)
    (divK_mulsub_correction_addback_beq_spec_within sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
       v1Old v5Old v6Old v7Old v10Old v2Old base hcarry2_nz hborrow)

/-- Named-postcondition no-NOP wrapper for `divK_mulsub_correction_addback_beq_spec_within_noNop`. -/
theorem divK_mulsub_correction_addback_beq_named_spec_within_noNop
    (sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (v1Old v5Old v6Old v7Old v10Old v2Old : Word)
    (base : Word) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
    (carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) →
    (if BitVec.ult uTop c3 then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 130 (base + div128CallRetOff) (base + storeLoopOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ qHat) **
       (.x1 ↦ᵣ v1Old) ** (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x2 ↦ᵣ v2Old) **
       (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3976 ↦ₘ j) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop))
      (n4McaBeqPost sp uBase qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase ms c3 carry ab hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by simp only [n4McaBeqPost_unfold]; exact hp)
    (divK_mulsub_correction_addback_beq_spec_within_noNop sp qHat j v0 v1 v2 v3 u0 u1 u2 u3 uTop
       v1Old v5Old v6Old v7Old v10Old v2Old base hcarry2_nz hborrow)

end EvmAsm.Evm64
