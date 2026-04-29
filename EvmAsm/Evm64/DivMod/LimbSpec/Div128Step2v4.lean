/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2v4

  Full-step composition for instructions [40]-[70] of the
  `divK_div128_v4` subroutine — the v4 fix that adds a 2nd Phase 2b
  D3 correction iteration (Knuth TAOCP §4.3.1 classical D3 step,
  full 2-iteration version, Phase 2b half).

  Combines:
  - step-2-init (DIVU+MUL+SUB) — instrs [40..42] (same as v2 step2)
  - clamp-q0 (SRLI+BEQ+ADDI+ADD) — instrs [43..46] (same as v2)
  - Phase 2b guard (SRLI+BNE) — instrs [47..48] (same as v2)
  - Phase 2b 1st D3 with save/restore — instrs [49..60] (NEW shape)
  - Phase 2b 2nd D3 — instrs [61..70] (NEW)

  into a single refined `q0` computation matching the Lean abstraction
  `div128Quot_v4`'s Phase 2 output (q0 = q0'' after BOTH Phase 2b D3
  iterations).

  The v4 Phase 2b structure differs from v2 Phase 2b in two ways:
  1. The 1st D3 saves rhat2c to scratch slot 3936 before clobbering x11
     with un0, then restores it in BOTH BLTU paths so rhat2c is
     available for the 2nd D3 guard.
  2. The 2nd D3 (instrs [61..70]) mirrors Phase 1b's 2nd D3 structure
     but for q0/rhat2 instead of q1/rhat.

  PR-A2 of the v2 → v4 migration plan. Issue #1337 / Issue #61.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2
import EvmAsm.Evm64.DivMod.LoopDefs.IterV4

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The 31 instructions of the step-2-v4 block (instrs [40..70] of
    `divK_div128_v4`), as a plain `List Instr` so `step2v4_sub` can use
    `CodeReq.ofProg_lookup` — the same mechanism as `d128_v4_sub`. -/
def divKDiv128Step2V4Instrs : List Instr :=
  [.DIVU .x5 .x7 .x6,   .MUL .x1 .x5 .x6,   .SUB .x11 .x7 .x1,   -- [0..2]
   .SRLI .x1 .x5 32,     .BEQ .x1 .x0 12,     .ADDI .x5 .x5 4095,   -- [3..5]
   .ADD .x11 .x11 .x6,   .SRLI .x1 .x11 32,   .BNE .x1 .x0 92,      -- [6..8]
   .LD .x1 .x12 3952,    .MUL .x7 .x5 .x1,    .SLLI .x1 .x11 32,    -- [9..11]
   .SD .x12 .x11 3936,   .LD .x11 .x12 3944,  .OR .x1 .x1 .x11,     -- [12..14]
   .BLTU .x1 .x7 12,     .LD .x11 .x12 3936,  .JAL .x0 16,           -- [15..17]
   .ADDI .x5 .x5 4095,   .LD .x11 .x12 3936,  .ADD .x11 .x11 .x6,   -- [18..20]
   .SRLI .x1 .x11 32,    .BNE .x1 .x0 36,     .LD .x1 .x12 3952,    -- [21..23]
   .MUL .x7 .x5 .x1,    .SLLI .x1 .x11 32,   .LD .x11 .x12 3944,   -- [24..26]
   .OR .x1 .x1 .x11,    .BLTU .x1 .x7 8,     .JAL .x0 8,            -- [27..29]
   .ADDI .x5 .x5 4095]                                                  -- [30]

/-- Bundled CodeReq for `divK_div128_step2_v4_spec`. Expressed as
    `CodeReq.ofProg` (not union-of-singletons) so `step2v4_sub` can
    use `ofProg_lookup` — same pattern as `d128_v4_sub` for the full
    `divK_div128_v4` program. `@[irreducible]` to keep let-bindings
    out of theorem signatures. -/
@[irreducible]
def divKDiv128Step2V4Code (base : Word) : CodeReq :=
  CodeReq.ofProg base divKDiv128Step2V4Instrs

private theorem divKDiv128Step2V4Instrs_len : divKDiv128Step2V4Instrs.length = 31 := by decide

/-- Per-instruction subsumption: singleton at byte-offset `4*k` of
    `divKDiv128Step2V4Code base` is included in the CodeReq.
    Exactly analogous to `d128_v4_sub` for the full `divK_div128_v4`
    program — avoids repeating the union-of-singletons form. -/
private theorem step2v4_sub {base : Word} (k : Nat) (addr : Word) (instr : Instr)
    (hk : k < 31)
    (h_addr : addr = base + BitVec.ofNat 64 (4 * k))
    (h_instr : divKDiv128Step2V4Instrs.get ⟨k, by
        have := divKDiv128Step2V4Instrs_len; omega⟩ = instr) :
    ∀ a i, CodeReq.singleton addr instr a = some i →
      (divKDiv128Step2V4Code base) a = some i := by
  subst h_addr; subst h_instr; unfold divKDiv128Step2V4Code
  exact fun a i h => CodeReq.singleton_mono
    (CodeReq.ofProg_lookup base divKDiv128Step2V4Instrs k (by
        have := divKDiv128Step2V4Instrs_len; omega) (by decide)) a i h

/-- Bundled postcondition for `divK_div128_step2_v4_spec`. Hides the
    let-chain for Step 2 v4 trial-division intermediates + Phase 2b
    1st+2nd D3 outcomes.

    The key output is `q0''` (post-2nd-D3 correction), which is what
    `div128Quot_v4` computes. Other registers (x1, x6, x7, x11) hold
    transient end-of-block values that depend on the BLTU path taken;
    the postcondition encodes them via if-then-else on the relevant
    BLTU/BNE conditions. -/
@[irreducible]
def divKDiv128Step2V4Post (sp un21 dHi dlo un0 vScratchOld : Word) : Assertion :=
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo            -- product for 1st D3 check
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 1st D3 result (if outer guard doesn't fire).
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  -- Post-1st-D3 rhat2: equals rhat2c + dHi if 1st BLTU fired, else rhat2c.
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo            -- product for 2nd D3 check
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  -- Phase 2b 2nd D3 result.
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  -- Exit register state at [71]:
  -- x7: un21 (outer BNE) | q0c*dlo (2nd BNE) | q0'*dlo (2nd D3 ran).
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1
                else q0Dlo2
  -- x1: rhat2cHi (outer BNE) | rhat2'Hi (2nd BNE) | rhat2'*2^32|un0 (2nd D3 ran).
  let x1Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi
                else rhat2'Un0
  -- x11: rhat2c (outer BNE) | rhat2' (2nd BNE) | un0 (2nd D3 ran).
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2'
                 else un0
  -- mem3936: vScratchOld if outer BNE fired (SD at [52] not reached),
  --          else rhat2c (saved at [52]).
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
  (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) **
  (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ mem3936Exit)

/-- Bundled postcondition for Phase 2b 1st D3 with save/restore.
    Covers instructions [47..60] of divK_div128_v4 (14 instructions). -/
@[irreducible]
def divKDiv128Phase2b1stD3V4Post (sp q0c rhat2c dlo un0 dHi : Word) : Assertion :=
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let rhat2c_upd :=
    if rhat2cHi = 0 then
      let qDlo := q0c * dlo
      let rhatUn0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
      if BitVec.ult rhatUn0 qDlo then rhat2c + dHi else rhat2c
    else rhat2c
  -- After 1st D3: x5 = q0', x11 = rhat2c_upd, x7 = q0c * dlo (transient).
  (.x5 ↦ᵣ q0') ** (.x11 ↦ᵣ rhat2c_upd) ** (.x6 ↦ᵣ dHi) **
  (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
  (sp + signExtend12 3936 ↦ₘ rhat2c)

/-- **STUB**: Phase 2b 1st D3 with save/restore — instructions [47..60].
    The outer BNE guard at [48] (offset 92) jumps to [71] (past step2_v4
    entirely) when rhat2c >= 2^32. Otherwise runs the 1st D3 mul-check
    with the save/restore of rhat2c to scratch slot 3936.

    This is NOT a standalone cpsTriple (the outer BNE exits step2_v4);
    it is a building block for step2_v4_spec's branch structure. -/
theorem divK_div128_phase2b_1st_d3_v4_spec
    (sp q0c rhat2c dlo un0 dHi v1Old v7Old vScratch : Word) (base : Word) :
    cpsTriple base (base + 56) (divKDiv128Step2V4Code base)
      ((.x5 ↦ᵣ q0c) ** (.x11 ↦ᵣ rhat2c) ** (.x6 ↦ᵣ dHi) **
       (.x1 ↦ᵣ v1Old) ** (.x7 ↦ᵣ v7Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratch))
      (divKDiv128Phase2b1stD3V4Post sp q0c rhat2c dlo un0 dHi) := by
  sorry  -- Covers [47..60] when rhat2c < 2^32 guard doesn't fire globally.
         -- Actually this is NOT right: the outer BNE jumps out of step2_v4.
         -- Simplification: treat step2_v4 as a cpsTriple (ignoring the fact
         -- that BNE branches forward past [71] — which is handled by step2_v4
         -- itself via the outer branch structure). Keep as sorry for now.

/-- **STUB**: full v4 Phase 2 spec — instructions [40..70] of `divK_div128_v4`.

    Mirrors `divK_div128_step2_spec` for the v4 algorithm. Proof structure:
    - [40..42]: step-2-init (same as v2).
    - [43..46]: clamp-q0 (same as v2).
    - [47..48]: Phase 2b guard (same as v2).
    - [49..60]: Phase 2b 1st D3 with save/restore (NEW).
    - [61..70]: Phase 2b 2nd D3 (NEW — mirror of Phase 1b 2nd D3).

    Estimated body: ~700 LOC, mirrors the v2 step2 spec but with the
    added 2nd D3 + save/restore handling. -/
theorem divK_div128_step2_v4_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 vScratchOld : Word) (base : Word) :
    cpsTriple base (base + 124) (divKDiv128Step2V4Code base)
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) **
       (sp + signExtend12 3944 ↦ₘ un0) **
       (sp + signExtend12 3936 ↦ₘ vScratchOld))
      (divKDiv128Step2V4Post sp un21 dHi dlo un0 vScratchOld) := by
  unfold divKDiv128Step2V4Post
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
  let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dlo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
  let rhat2' :=
    if rhat2cHi = 0 then
      if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
    else rhat2c
  let rhat2'Hi := rhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := q0' * dlo
  let rhat2'Un0 := (rhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := div128Quot_phase2b_q0' q0' rhat2' dlo un0
  let x7Exit := if rhat2cHi ≠ 0 then un21
                else if rhat2'Hi ≠ 0 then q0Dlo1 else q0Dlo2
  let x1Exit := if rhat2cHi ≠ 0 then rhat2cHi
                else if rhat2'Hi ≠ 0 then rhat2'Hi else rhat2'Un0
  let x11Exit := if rhat2cHi ≠ 0 then rhat2c
                 else if rhat2'Hi ≠ 0 then rhat2' else un0
  let mem3936Exit := if rhat2cHi ≠ 0 then vScratchOld else rhat2c
  -- Phase A: init+clamp [0..28] — cpsTriple base (base+28).
  -- Reuse divK_div128_step2_upto_guard_spec, extend via step2v4_sub 0..6.
  have hA_raw := divK_div128_step2_upto_guard_spec sp un21 dHi v1Old v5Old v11Old dlo un0 base
  have hA : cpsTriple base (base + 28) (divKDiv128Step2V4Code base) _ _ :=
    cpsTriple_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 0 base (.DIVU .x5 .x7 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 1 (base+4) (.MUL .x1 .x5 .x6) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 2 (base+8) (.SUB .x11 .x7 .x1) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 3 (base+12) (.SRLI .x1 .x5 32) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 4 (base+16) (.BEQ .x1 .x0 12) (by omega) (by bv_omega) (by decide))
       (CodeReq.union_sub
        (step2v4_sub 5 (base+20) (.ADDI .x5 .x5 4095) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 6 (base+24) (.ADD .x11 .x11 .x6) (by omega) (by bv_omega) (by decide))))))))
    hA_raw
  have hAf := cpsTriple_frameR
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
    (by pcFree) hA
  -- Phase B: outer SRLI+BNE guard [28..36] — cpsBranch via step2v4_sub 7+8.
  have hB_raw := divK_div128_phase2b_guard_spec sp rhat2c hi (base + 28) (92 : BitVec 13)
  simp only [show (base + 28 : Word) + 4 = base + 32 from by bv_addr,
             show (base + 28 : Word) + 8 = base + 36 from by bv_addr,
             show (base + 32 : Word) + signExtend13 (92 : BitVec 13) = base + 124 from by
               rv64_addr] at hB_raw
  have hB : cpsBranch (base + 28) (divKDiv128Step2V4Code base) _ _ _ _ _ :=
    cpsBranch_extend_code (hmono := by
      exact CodeReq.union_sub
        (step2v4_sub 7 (base+28) (.SRLI .x1 .x11 32) (by omega) (by bv_omega) (by decide))
        (step2v4_sub 8 (base+32) (.BNE .x1 .x0 92) (by omega) (by bv_omega) (by decide))) hB_raw
  have hBf := cpsBranch_frameR
    ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
     (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
     (sp + signExtend12 3936 ↦ₘ vScratchOld))
    (by pcFree) hB
  have composed_AB := cpsTriple_seq_cpsBranch_perm_same_cr
    (fun h hp => by xperm_hyp hp) hAf hBf
  -- finalPost (merged post at base+124 for both legs).
  let finalPost : Assertion :=
    (.x5 ↦ᵣ q0'') ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ x7Exit) **
    (.x1 ↦ᵣ x1Exit) ** (.x11 ↦ᵣ x11Exit) **
    (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ mem3936Exit)
  -- Taken leg (rhat2cHi ≠ 0): BNE fires, already at base+124.
  -- q0'' = q0c (both D3 guards fire), x7=un21, x1=rhat2cHi, x11=rhat2c, mem3936=vScratchOld.
  -- The taken postcondition of composed_AB:
  let takenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi ≠ 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  have h_taken : cpsTriple (base + 124) (base + 124) (divKDiv128Step2V4Code base)
      takenPost finalPost :=
    cpsTriple_extend_code (hmono := fun _ _ h => by simp [CodeReq.empty] at h)
    (cpsTriple_refl (by
      intro hp htp
      -- Extract ⌜rhat2cHi ≠ 0⌝ from takenPost (inside a have so htp survives).
      -- takenPost = (.x12 ** .x11 ** .x1 ** .x0 ** ⌜rhat2cHi ≠ 0⌝) ** rest.
      have h_ne : rhat2cHi ≠ 0 := by
        obtain ⟨_, _, _, _, hleft, _⟩ := htp
        obtain ⟨_, _, _, _, _, h1⟩ := hleft  -- peel .x12
        obtain ⟨_, _, _, _, _, h2⟩ := h1     -- peel .x11
        obtain ⟨_, _, _, _, _, h3⟩ := h2     -- peel .x1
        obtain ⟨_, _, _, _, _, h4⟩ := h3     -- peel .x0
        obtain ⟨_, hpure⟩ := h4             -- ⌜rhat2cHi ≠ 0⌝
        exact hpure
      -- When rhat2cHi ≠ 0: both D3 guards skip → q0'' = q0c.
      have hq0' : q0' = q0c := by
        show div128Quot_phase2b_q0' q0c rhat2c dlo un0 = q0c
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hrhat2' : rhat2' = rhat2c := by
        show (if rhat2cHi = 0 then _ else rhat2c) = rhat2c
        exact if_neg h_ne
      have hq0'' : q0'' = q0c := by
        show div128Quot_phase2b_q0' q0' rhat2' dlo un0 = q0c
        rw [hq0', hrhat2']
        simp only [div128Quot_phase2b_q0']; exact if_neg h_ne
      have hx7 : x7Exit = un21   := by show (if rhat2cHi ≠ 0 then un21 else _) = un21; exact if_pos h_ne
      have hx1 : x1Exit = rhat2cHi := by show (if rhat2cHi ≠ 0 then rhat2cHi else _) = rhat2cHi; exact if_pos h_ne
      have hx11 : x11Exit = rhat2c  := by show (if rhat2cHi ≠ 0 then rhat2c else _) = rhat2c; exact if_pos h_ne
      have hmem : mem3936Exit = vScratchOld := by show (if rhat2cHi ≠ 0 then vScratchOld else _) = vScratchOld; exact if_pos h_ne
      -- Strip ⌜rhat2cHi ≠ 0⌝ from htp for xperm_hyp.
      -- takenPost = (.x12 ** .x11 ** .x1 ** .x0 ** ⌜...⌝) ** rest.
      -- Strip: 3x sepConj_mono_right to reach .x0 ** ⌜...⌝, then strip.
      have htp' : (((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) ** (.x0 ↦ᵣ 0)) **
          (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
          (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) hp :=
        sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (fun h'' hp'' => ((sepConj_pure_right h'').1 hp'').1)))) hp htp
      -- Rewrite finalPost to explicit form, then xperm_hyp htp'.
      show finalPost hp
      rw [show finalPost = ((.x5 ↦ᵣ q0c) ** (.x6 ↦ᵣ dHi) ** (.x7 ↦ᵣ un21) **
          (.x1 ↦ᵣ rhat2cHi) ** (.x11 ↦ᵣ rhat2c) **
          (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
          (sp + signExtend12 3952 ↦ₘ dlo) **
          (sp + signExtend12 3944 ↦ₘ un0) **
          (sp + signExtend12 3936 ↦ₘ vScratchOld)) from by
        simp only [finalPost, hq0'', hx7, hx1, hx11, hmem]]
      xperm_hyp htp'))
  -- The not-taken postcondition of composed_AB:
  let notTakenPost : Assertion :=
    ((.x12 ↦ᵣ sp) ** (.x11 ↦ᵣ rhat2c) ** (.x1 ↦ᵣ rhat2cHi) **
     (.x0 ↦ᵣ 0) ** ⌜rhat2cHi = 0⌝) **
    (.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0c) **
    (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0) **
    (sp + signExtend12 3936 ↦ₘ vScratchOld)
  -- Not-taken leg (rhat2cHi = 0): run [36..120] → base+124.
  have h_notTaken : cpsTriple (base + 36) (base + 124) (divKDiv128Step2V4Code base)
      notTakenPost finalPost := by
    sorry  -- [36..120] proof via step2v4_sub 9..30:
           -- (C) [9..15] = LD+MUL+SLLI+SD+LD+OR: runBlock with step2v4_sub 9..14.
           -- (D) BLTU cpsBranch at [15] via step2v4_sub 15:
           --       taken [18..20] = ADDI+LD+ADD: step2v4_sub 18+19+20.
           --       not-taken [16..17] = LD+JAL: step2v4_sub 16+17.
           --       cpsBranch_merge_same_cr → cpsTriple (base+36) (base+84).
           -- (E) [21..22] SRLI+BNE guard via step2v4_sub 21+22, guard_off=36 → base+124:
           --       taken → base+124 (identity).
           --       not-taken [23..30] prodcheck2-style:
           --         [23..27] LD+MUL+SLLI+LD+OR: step2v4_sub 23..27.
           --         BLTU [28]: taken [30]=ADDI: step2v4_sub 28+30.
           --                    not-taken [29]=JAL: step2v4_sub 29.
           --       cpsBranch_merge_same_cr → cpsTriple (base+84) (base+124).
           --     cpsTriple_seq → cpsTriple (base+36) (base+124).
  exact cpsTriple_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    (cpsBranch_merge_same_cr composed_AB h_taken h_notTaken)

end EvmAsm.Evm64
