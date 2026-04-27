/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1v2

  **STUB FILE** for issue #1337 algorithm fix migration.

  Full-step composition for instructions [10]-[34] of the
  `divK_div128_v2` subroutine — the v2 fix that adds a 2nd Phase 1b
  D3 correction iteration (Knuth TAOCP §4.3.1 classical D3 step,
  full 2-iteration version).

  Combines:
  - step-1-init (DIVU+MUL+SUB) — instrs [10..12]
  - clamp-q1 (SRLI+BEQ+ADDI+ADD) — instrs [13..16]
  - prodcheck1 / 1st D3 (LD+MUL+SLLI+OR + BLTU+JAL + ADDI+ADD) — instrs [17..24]
  - prodcheck1b / 2nd D3 (SRLI+BNE + LD+MUL+SLLI+OR+BLTU+JAL+ADDI+ADD) — instrs [25..34]

  into a single refined `q1 / rhat` computation matching the Lean
  abstraction `div128Quot_v2`'s Phase 1 output (q1 = q1c after BOTH
  D3 iterations, rhat = rhatc after BOTH D3 iterations).

  **Status (2026-04-27)**: theorem signature only; proof is a sorry.

  Issue #1337's algorithm fix migration. Tracked in PR #1390.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1b

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 step 1 v2 branch-merged: composes step1_spec + prodcheck1b_merged_spec
    into a cpsBranch where BOTH legs end at base+100. Instrs [10]-[34].
    The cpsBranch shape arises because the 2nd D3 guard at [25..26] either
    skips the body [27..34] (taken leg, rhatHi2 ≠ 0) or executes it (fall-through
    leg, rhatHi2 = 0).

    Mirrors `divK_div128_step2_branch_merged_spec` from Div128Step2.lean.

    Issue #1337 algorithm fix migration. -/
theorem divK_div128_step1_v2_branch_merged_spec
    (sp uHi dHi un1 v1Old v5Old v10Old dlo : Word) (base : Word) :
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi = 0 then rhat else rhat + dHi
    let qDlo1 := q1c * dlo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
    let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
    let qDlo2 := q1' * dlo
    let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    let q1'FT := if BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1'
    let rhat'FT := if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 60) (.SRLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 64) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 72) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 80) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 84) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 88) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 92) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 96) (.ADD .x7 .x7 .x6)))))))))))))))))))))))))
    cpsBranch base cr
      ((.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) **
       (.x5 ↦ᵣ v5Old) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo))
      (base + 100)  -- guard-fires path (rhatHi2 ≠ 0): body skipped, q1 / rhat keep 1st-D3 values
        ((.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1') **
         (.x5 ↦ᵣ qDlo1) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatHi2) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhatHi2 ≠ 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo))
      (base + 100)  -- guard-falls-through (rhatHi2 = 0): body runs, 2nd-D3 applied
        ((.x7 ↦ᵣ rhat'FT) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1'FT) **
         (.x5 ↦ᵣ qDlo2) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatUn1') **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhatHi2 = 0⌝ **
         (sp + signExtend12 3952 ↦ₘ dlo)) := by
  sorry  -- Compose step1_spec (cpsTriple) ⨾ prodcheck1b_merged_spec (cpsBranch)
         -- via cpsTriple_seq_cpsBranch_perm_same_cr. ~80 LOC mirror of
         -- divK_div128_step2_branch_merged_spec.

/-- div128 step 1 v2: trial division q1, clamp, FIRST product check + correction,
    SECOND product check + correction (gated by `rhatc < 2^32` guard).
    Instrs [10]-[34] of `divK_div128_v2` (25 instructions, span = base+100).

    Input: uHi in x7, dHi in x6, un1 in x11, dlo in memory.
    Output: refined q1 in x10, refined rhat in x7 — matching
    `div128Quot_v2`'s Phase 1 output (post-both-D3-iterations).

    The `.x5` / `.x1` postconditions diverge between the 2nd D3 guard's
    fall-through and taken legs; expressed via conditionals on
    `rhatHi2 := rhat' >> 32` (the 2nd guard's input).

    Issue #1337 algorithm fix migration. -/
theorem divK_div128_step1_v2_spec
    (sp uHi dHi un1 v1Old v5Old v10Old dlo : Word) (base : Word) :
    -- Phase 1a (existing logic, copied from step1_spec):
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi = 0 then rhat else rhat + dHi
    -- 1st D3 correction (existing prodcheck1):
    let qDlo1 := q1c * dlo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    let q1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
    -- 2nd D3 correction (new prodcheck1b — gated by rhatHi2 = 0):
    let rhatHi2 := rhat' >>> (32 : BitVec 6).toNat
    let qDlo2 := q1' * dlo
    let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
    -- Final q1 / rhat values matching div128Quot_v2:
    let q1'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                then q1' + signExtend12 4095 else q1'
    let rhat'' := if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2
                  then rhat' + dHi else rhat'
    -- Diverging .x5 / .x1 register postconditions:
    --   guard-taken (rhatHi2 ≠ 0): .x5 = qDlo1 (1st D3 mul result, untouched), .x1 = rhatHi2 (the SRLI)
    --   fall-through (rhatHi2 = 0): .x5 = qDlo2 (2nd D3 mul result), .x1 = rhatUn1' (2nd D3 OR result)
    let x5Exit := if rhatHi2 = 0 then qDlo2 else qDlo1
    let x1Exit := if rhatHi2 = 0 then rhatUn1' else rhatHi2
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x10 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x5 .x10 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x7 .x7 .x5))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x5 .x10 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x5 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 32) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 36) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 40) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 44) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 48) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 52) (.ADDI .x10 .x10 4095))
      (CodeReq.union (CodeReq.singleton (base + 56) (.ADD .x7 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 60) (.SRLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 64) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 68) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 72) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 76) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 80) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 84) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 88) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 92) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 96) (.ADD .x7 .x7 .x6)))))))))))))))))))))))))
    cpsTriple base (base + 100) cr
      ((.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) **
       (.x5 ↦ᵣ v5Old) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ v1Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x7 ↦ᵣ rhat'') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1'') **
       (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ x1Exit) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)) := by
  -- Delegate the structural composition to branch_merged_spec, then flatten
  -- the resulting cpsBranch via cpsBranch_merge_same_cr with two refl bridges.
  -- Mirrors divK_div128_step2_spec from Div128Step2.lean.
  intro q1 rhat hi q1c rhatc qDlo1 rhatUn1 q1' rhat' rhatHi2 qDlo2 rhatUn1'
        q1'' rhat'' x5Exit x1Exit cr
  have hbr := divK_div128_step1_v2_branch_merged_spec sp uHi dHi un1 v1Old v5Old
    v10Old dlo base
  let tgtPost : Assertion :=
    (.x7 ↦ᵣ rhat'') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1'') **
    (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ x1Exit) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)
  have refl_of {P : Assertion} (h : ∀ hp, P hp → tgtPost hp) :
      cpsTriple (base + 100) (base + 100) cr P tgtPost :=
    cpsTriple_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
      (cpsTriple_refl h)
  -- Taken bridge: rhatHi2 ≠ 0 ⟹ q1'' = q1', rhat'' = rhat', x5Exit = qDlo1, x1Exit = rhatHi2
  have h_t : cpsTriple (base + 100) (base + 100) cr _ tgtPost := refl_of (P :=
    (.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1') **
    (.x5 ↦ᵣ qDlo1) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatHi2) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhatHi2 ≠ 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo)) (by
    intro hp hP
    have h_hi_ne : rhatHi2 ≠ 0 := by
      obtain ⟨_, _, _, _, _, hrest⟩ := hP
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hrest
      exact hpure
    have h_and_false : ¬ (rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 = true) :=
      fun ⟨h_eq, _⟩ => h_hi_ne h_eq
    have hq1'' : q1'' = q1' := if_neg h_and_false
    have hrhat'' : rhat'' = rhat' := if_neg h_and_false
    have hx5 : x5Exit = qDlo1 := if_neg h_hi_ne
    have hx1 : x1Exit = rhatHi2 := if_neg h_hi_ne
    show tgtPost hp
    show ((.x7 ↦ᵣ rhat'') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1'') **
         (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ x1Exit) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)) hp
    rw [hq1'', hrhat'', hx5, hx1]
    have hP' : ((.x7 ↦ᵣ rhat') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1') **
                (.x5 ↦ᵣ qDlo1) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatHi2) **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
                (sp + signExtend12 3952 ↦ₘ dlo)) hp :=
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_left h').1 hp').2)))))))) hp hP
    xperm_hyp hP')
  -- Fall-through bridge: rhatHi2 = 0 ⟹ q1'' = q1'FT, rhat'' = rhat'FT, x5Exit = qDlo2, x1Exit = rhatUn1'
  have h_f : cpsTriple (base + 100) (base + 100) cr _ tgtPost := refl_of (P :=
    (.x7 ↦ᵣ (if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat')) **
    (.x6 ↦ᵣ dHi) **
    (.x10 ↦ᵣ (if BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1')) **
    (.x5 ↦ᵣ qDlo2) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatUn1') **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** ⌜rhatHi2 = 0⌝ **
    (sp + signExtend12 3952 ↦ₘ dlo)) (by
    intro hp hP
    have h_hi_eq : rhatHi2 = 0 := by
      obtain ⟨_, _, _, _, _, hrest⟩ := hP
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, _, hrest⟩ := hrest
      obtain ⟨_, _, _, _, ⟨_, hpure⟩, _⟩ := hrest
      exact hpure
    have hq1'' : q1'' = (if BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1') := by
      show (if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 = true then q1' + signExtend12 4095 else q1') = _
      by_cases hult : BitVec.ult rhatUn1' qDlo2 = true
      · rw [if_pos ⟨h_hi_eq, hult⟩, if_pos hult]
      · rw [if_neg (fun ⟨_, h⟩ => hult h), if_neg hult]
    have hrhat'' : rhat'' = (if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat') := by
      show (if rhatHi2 = 0 ∧ BitVec.ult rhatUn1' qDlo2 = true then rhat' + dHi else rhat') = _
      by_cases hult : BitVec.ult rhatUn1' qDlo2 = true
      · rw [if_pos ⟨h_hi_eq, hult⟩, if_pos hult]
      · rw [if_neg (fun ⟨_, h⟩ => hult h), if_neg hult]
    have hx5 : x5Exit = qDlo2 := if_pos h_hi_eq
    have hx1 : x1Exit = rhatUn1' := if_pos h_hi_eq
    show ((.x7 ↦ᵣ rhat'') ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1'') **
         (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ x1Exit) **
         (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) ** (sp + signExtend12 3952 ↦ₘ dlo)) hp
    rw [hq1'', hrhat'', hx5, hx1]
    have hP' : ((.x7 ↦ᵣ (if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat')) **
                (.x6 ↦ᵣ dHi) **
                (.x10 ↦ᵣ (if BitVec.ult rhatUn1' qDlo2 then q1' + signExtend12 4095 else q1')) **
                (.x5 ↦ᵣ qDlo2) ** (.x11 ↦ᵣ un1) ** (.x1 ↦ᵣ rhatUn1') **
                (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
                (sp + signExtend12 3952 ↦ₘ dlo)) hp :=
      sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (fun h' hp' => ((sepConj_pure_left h').1 hp').2)))))))) hp hP
    xperm_hyp hP')
  exact cpsBranch_merge_same_cr hbr h_t h_f

end EvmAsm.Evm64
