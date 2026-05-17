/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterBridges

  loopPost → iterPre bridge theorems for the named two-MUL saved-bit EXP iteration.

  Split from `SavedBitIterMerge` to stay within the 1200-line Compose/ cap.
  Provides:
  - `expTwoMulIterSkipPost_to_iterPre` (skip/bit=0 path)
  - `expTwoMulIterCondPost_to_iterPre` (cond/bit=1 path)
  - `expTwoMulIterLoopPost_to_iterPre` (combined: both paths)
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

-- Key insight for the 256-iteration loop body proof: the `loopPost` assertion
-- embeds ALL the atoms needed by the NEXT iteration's `iterPre`, except for
-- `d0..d3` which come from `memOwn` atoms (algorithmically irrelevant scratch).
--
-- For the SKIP path (bit = 0):
--   x5' = squareW.getLimbN 3  (next exponent cursor, from skipRest)
--   r0'..r3' = squareW.getLimbN 0..3  (from evmWordIs sp squareW)
--   e0'..e3' = squareW.getLimbN 0..3  (from evmWordIs (evmSp+32) squareW)
--   v18' = bit + signExtend12 0  (from skipRest's x18)
--   vOld' = (base+44)+68  (from skipRest's x1)
--   d0'..d3' = WHATEVER is at evmSp..evmSp+24  (from memOwn atoms)
--
-- For the COND path (bit = 1):
--   x5' = rw.getLimbN 3,  r0'..r3' = rw.getLimbN 0..3
--   e0'..e3' = rw.getLimbN 0..3 (from evmWordIs (evmSp+32) rw)
--   v18' = bit+signExtend12 0, vOld' = (base+152)+68
--   d0'..d3' = WHATEVER is at evmSp..evmSp+24 (from memOwn atoms)
--
-- Proving this existential bridge (expTwoMulIterLoopPost_to_iterPre_exists)
-- requires extracting d0..d3 from memOwn via Classical.choose and reassembling
-- the sepConj — see bead evm-asm-w5mk notes for the proof sketch.

/-- Bridge from `expTwoMulIterSkipPost` (the skip branch of loopPost) to
    `expTwoMulIterPre`.

    After normalizing addresses and stripping pure-fact components (which
    live in empty PartialState singletons), the skip-post and iterPre
    assertions have IDENTICAL atoms.  Each `memOwn` atom is converted to a
    concrete `memIs` via `sepConj_choose_memOwn`, and `sep_perm` closes the
    rearrangement via `ac_rfl` on `Std.Commutative`/`Std.Associative` for `**`.

    This is the `loopPost → iterPre` bridge needed to chain the peel theorem
    for the full 256-iteration loop body induction (evm-asm-w5mk). -/
theorem expTwoMulIterSkipPost_to_iterPre
    {k bit sp evmSp base a0 a1 a2 a3 : Word} {squareW : EvmWord}
    {ps : PartialState} (hk : k ≠ 0)
    (h : expTwoMulIterSkipPost k bit sp evmSp base a0 a1 a2 a3
           squareW (k ≠ 0) ps) :
    ∃ d0 d1 d2 d3,
      expTwoMulIterPre
        (squareW.getLimbN 3) k (bit + signExtend12 0) sp evmSp
        ((base + 44) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 ps := by
  -- Unfold assertions and normalize signExtend12 addresses
  rw [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
      expTwoMulIterBaseFrame_unfold] at h
  simp only [evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero] at h
  -- Normalize compound address arithmetic: evmSp+32+8 → evmSp+40 etc.
  simp only [BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide] at h
  -- Replace ⌜k≠0⌝ with empAssertion and simplify using the equation form
  rw [show (⌜k ≠ 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hk⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  -- After simp: h contains (x18 ↦ᵣ bit) ** ⌜bit = 0⌝ ** ...
  -- Step 1: extract bit=0 as a Prop side condition
  have hbit : bit = 0 := by
    obtain ⟨_, _, _, _, houter, _⟩ := h   -- houter = OUTER (5th = left)
    obtain ⟨_, _, _, _, _, hx18rest⟩ := houter  -- hx18rest = x18 ** ⌜bit=0⌝ ** rest
    obtain ⟨_, _, _, _, _, hb0rest⟩ := hx18rest  -- hb0rest = ⌜bit=0⌝ ** rest
    exact ((sepConj_pure_left _).mp hb0rest).1
  -- Drop ⌜bit=0⌝ using the known side condition
  rw [show (⌜bit = 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hbit⟩⟩] at h
  simp only [sepConj_emp_left'] at h
  -- h now contains exactly the atoms of iterPre, with memOwn instead of memIs
  -- Step 2: bring each memOwn atom to front and extract d0..d3
  -- Use `apply sepConj_choose_memOwn; sep_perm h_*` which lets `sep_perm`
  -- rearrange via ac_rfl before `sepConj_choose_memOwn` extracts the value.
  -- Navigate via obtain to reach the memOwn atoms, then extract via sepConj_choose_memOwn
  obtain ⟨ps_outer, ps_bf, hd_bf, hu_bf, h_outer, h_bf⟩ := h
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_outer
  obtain ⟨ps_x18, ps_r1, hd1, hu1, h_x18, h_r1⟩ := h_sr
  obtain ⟨ps_x2, ps_r2, hd2, hu2, h_x2, h_r2⟩ := h_r1
  obtain ⟨ps_x12, ps_r3, hd3, hu3, h_x12, h_r3⟩ := h_r2
  obtain ⟨ps_x5, ps_r4, hd4, hu4, h_x5, h_r4⟩ := h_r3
  obtain ⟨ps_sp, ps_r5, hd5, hu5, h_sp, h_r5⟩ := h_r4
  obtain ⟨ps_e32, ps_r6, hd6, hu6, h_e32, h_r6⟩ := h_r5
  obtain ⟨ps_x6, ps_r7, hd7, hu7, h_x6, h_r7⟩ := h_r6
  obtain ⟨ps_x7, ps_r8, hd8, hu8, h_x7, h_r8⟩ := h_r7
  obtain ⟨ps_x10, ps_r9, hd9, hu9, h_x10, h_r9⟩ := h_r8
  obtain ⟨ps_x11, ps_r10, hd10, hu10, h_x11, h_r10⟩ := h_r9
  -- h_r10 : (memOwn evmSp ** memOwn(evmSp+8) ** memOwn(evmSp+16) ** memOwn(evmSp+24) ** x1) ps_r10
  obtain ⟨d0, h_d0_chain⟩ := sepConj_choose_memOwn h_r10
  obtain ⟨ps_d0, ps_r11, hd_d0, hu_d0, h_d0, h_r11⟩ := h_d0_chain
  obtain ⟨d1, h_d1_chain⟩ := sepConj_choose_memOwn h_r11
  obtain ⟨ps_d1, ps_r12, hd_d1, hu_d1, h_d1, h_r12⟩ := h_d1_chain
  obtain ⟨d2, h_d2_chain⟩ := sepConj_choose_memOwn h_r12
  obtain ⟨ps_d2, ps_r13, hd_d2, hu_d2, h_d2, h_r13⟩ := h_d2_chain
  obtain ⟨d3, h_d3_chain⟩ := sepConj_choose_memOwn h_r13
  obtain ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩ := h_d3_chain
  -- Build h_d3_full: an assertion applied to the FULL ps using the extracted d values
  -- This is the AC-rearrangement of h with memIs atoms, applied to ps
  -- Use sep_perm on a combined hypothesis built from the components
  have h_d3_full : ((((Reg.x9 ↦ᵣ k) ** Reg.x0 ↦ᵣ 0) **
      (Reg.x18 ↦ᵣ bit) ** (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
      (Reg.x5 ↦ᵣ squareW.getLimbN 3) **
      ((sp ↦ₘ squareW.getLimbN 0) ** (sp + 8 ↦ₘ squareW.getLimbN 1) **
       (sp + 16 ↦ₘ squareW.getLimbN 2) ** (sp + 24 ↦ₘ squareW.getLimbN 3)) **
      ((evmSp + 32 ↦ₘ squareW.getLimbN 0) ** (evmSp + 40 ↦ₘ squareW.getLimbN 1) **
       (evmSp + 48 ↦ₘ squareW.getLimbN 2) ** (evmSp + 56 ↦ₘ squareW.getLimbN 3)) **
      regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
      (evmSp ↦ₘ d0) ** (evmSp + 8 ↦ₘ d1) ** (evmSp + 16 ↦ₘ d2) **
      (evmSp + 24 ↦ₘ d3) ** (Reg.x1 ↦ᵣ base + (44 + 68))) **
      (evmSp + 18446744073709551552 ↦ₘ a0) **
      (evmSp + 18446744073709551560 ↦ₘ a1) **
      (evmSp + 18446744073709551568 ↦ₘ a2) **
      (evmSp + 18446744073709551576 ↦ₘ a3)) ps := by
    refine ⟨ps_outer, ps_bf, hd_bf, hu_bf, ?_, h_bf⟩
    refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
    refine ⟨ps_x18, ps_r1, hd1, hu1, h_x18, ?_⟩
    refine ⟨ps_x2, ps_r2, hd2, hu2, h_x2, ?_⟩
    refine ⟨ps_x12, ps_r3, hd3, hu3, h_x12, ?_⟩
    refine ⟨ps_x5, ps_r4, hd4, hu4, h_x5, ?_⟩
    refine ⟨ps_sp, ps_r5, hd5, hu5, h_sp, ?_⟩
    refine ⟨ps_e32, ps_r6, hd6, hu6, h_e32, ?_⟩
    refine ⟨ps_x6, ps_r7, hd7, hu7, h_x6, ?_⟩
    refine ⟨ps_x7, ps_r8, hd8, hu8, h_x7, ?_⟩
    refine ⟨ps_x10, ps_r9, hd9, hu9, h_x10, ?_⟩
    refine ⟨ps_x11, ps_r10, hd10, hu10, h_x11, ?_⟩
    refine ⟨ps_d0, _, hd_d0, hu_d0, h_d0, ?_⟩
    refine ⟨ps_d1, _, hd_d1, hu_d1, h_d1, ?_⟩
    refine ⟨ps_d2, _, hd_d2, hu_d2, h_d2, ?_⟩
    exact ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩
  -- Provide witnesses and close the iterPre goal
  refine ⟨d0, d1, d2, d3, ?_⟩
  rw [expTwoMulIterPre_unfold, expTwoMulIterBaseFrame_unfold]
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
             signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc]
  sep_perm h_d3_full

/-- Bridge from `expTwoMulIterCondPost` (the cond/multiply branch of loopPost)
    to `expTwoMulIterPre`.

    Mirror of `expTwoMulIterSkipPost_to_iterPre` for the cond path (bit ≠ 0).
    The main structural difference from the skip path:
    - The `a0..a3` atoms live inside `condRest` (not as a separate outer component)
    - `vOld = (base + 152) + 68` (mul-callable return address for cond branch)
    - `bit + se0 ≠ 0` (cond condition, bit = 1)
    - `r0..r3` and `e0..e3` come from `evmWordIs sp rw` and `evmWordIs (evmSp+32) rw` -/
theorem expTwoMulIterCondPost_to_iterPre
    {k bit sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord}
    {ps : PartialState} (hk : k ≠ 0)
    (h : expTwoMulIterCondPost k bit sp evmSp base a0 a1 a2 a3 rw (k ≠ 0) ps) :
    ∃ d0 d1 d2 d3,
      expTwoMulIterPre
        (rw.getLimbN 3) k (bit + signExtend12 0) sp evmSp
        ((base + 152) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 ps := by
  rw [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
      expTwoMulIterCondFrame_unfold] at h
  simp only [evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero] at h
  simp only [BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide] at h
  -- Drop ⌜k≠0⌝
  rw [show (⌜k ≠ 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hk⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  -- Extract bit≠0 from condFrame's ⌜bit≠0⌝ (signExtend12 0 = 0 already normalized)
  have hbitne : bit ≠ 0 := by
    obtain ⟨_, _, _, _, _, hcf⟩ := h    -- h = (inner ** condFrame), get condFrame
    obtain ⟨_, _, _, _, _, hpure⟩ := hcf -- condFrame = (x18 ** ⌜bit≠0⌝)
    exact hpure.2
  -- Drop ⌜bit≠0⌝
  rw [show (⌜bit ≠ 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hbitne⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  -- Navigate via obtain to the memOwn atoms
  -- Structure: (((x9 ** x0) ** condRest) ** x18) ps
  -- condRest = x2 ** x12 ** x5 ** a0..a3 ** sp-subs ** e32-subs ** x6..x11 ** memOwns ** x1
  obtain ⟨ps_inner, ps_x18, hd_x18, hu_x18, h_inner, h_x18⟩ := h
  obtain ⟨ps_x9x0, ps_cr, hd_cr, hu_cr, h_x9x0, h_cr⟩ := h_inner
  obtain ⟨ps_x2, ps_r1, hd1, hu1, h_x2, h_r1⟩ := h_cr
  obtain ⟨ps_x12, ps_r2, hd2, hu2, h_x12, h_r2⟩ := h_r1
  obtain ⟨ps_x5, ps_r3, hd3, hu3, h_x5, h_r3⟩ := h_r2
  obtain ⟨ps_a0, ps_r4, hd4, hu4, h_a0, h_r4⟩ := h_r3
  obtain ⟨ps_a1, ps_r5, hd5, hu5, h_a1, h_r5⟩ := h_r4
  obtain ⟨ps_a2, ps_r6, hd6, hu6, h_a2, h_r6⟩ := h_r5
  obtain ⟨ps_a3, ps_r7, hd7, hu7, h_a3, h_r7⟩ := h_r6
  obtain ⟨ps_sp, ps_r8, hd8, hu8, h_sp, h_r8⟩ := h_r7
  obtain ⟨ps_e32, ps_r9, hd9, hu9, h_e32, h_r9⟩ := h_r8
  obtain ⟨ps_x6, ps_r10, hd10, hu10, h_x6, h_r10⟩ := h_r9
  obtain ⟨ps_x7, ps_r11, hd11, hu11, h_x7, h_r11⟩ := h_r10
  obtain ⟨ps_x10, ps_r12, hd12, hu12, h_x10, h_r12⟩ := h_r11
  obtain ⟨ps_x11, ps_r13, hd13, hu13, h_x11, h_r13⟩ := h_r12
  -- h_r13 : (memOwn evmSp ** memOwn(evmSp+8) ** memOwn(evmSp+16) ** memOwn(evmSp+24) ** x1) ps_r13
  obtain ⟨d0, h_d0_chain⟩ := sepConj_choose_memOwn h_r13
  obtain ⟨ps_d0, ps_r14, hd_d0, hu_d0, h_d0, h_r14⟩ := h_d0_chain
  obtain ⟨d1, h_d1_chain⟩ := sepConj_choose_memOwn h_r14
  obtain ⟨ps_d1, ps_r15, hd_d1, hu_d1, h_d1, h_r15⟩ := h_d1_chain
  obtain ⟨d2, h_d2_chain⟩ := sepConj_choose_memOwn h_r15
  obtain ⟨ps_d2, ps_r16, hd_d2, hu_d2, h_d2, h_r16⟩ := h_d2_chain
  obtain ⟨d3, h_d3_chain⟩ := sepConj_choose_memOwn h_r16
  obtain ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩ := h_d3_chain
  refine ⟨d0, d1, d2, d3, ?_⟩
  rw [expTwoMulIterPre_unfold, expTwoMulIterBaseFrame_unfold]
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
             signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc]
  have h_d3_full :
      ((((Reg.x9 ↦ᵣ k) ** Reg.x0 ↦ᵣ 0) **
        (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
        (Reg.x5 ↦ᵣ rw.getLimbN 3) **
        (evmSp + 18446744073709551552 ↦ₘ a0) **
        (evmSp + 18446744073709551560 ↦ₘ a1) **
        (evmSp + 18446744073709551568 ↦ₘ a2) **
        (evmSp + 18446744073709551576 ↦ₘ a3) **
        ((sp ↦ₘ rw.getLimbN 0) ** (sp + 8 ↦ₘ rw.getLimbN 1) **
         (sp + 16 ↦ₘ rw.getLimbN 2) ** (sp + 24 ↦ₘ rw.getLimbN 3)) **
        ((evmSp + 32 ↦ₘ rw.getLimbN 0) ** (evmSp + 40 ↦ₘ rw.getLimbN 1) **
         (evmSp + 48 ↦ₘ rw.getLimbN 2) ** (evmSp + 56 ↦ₘ rw.getLimbN 3)) **
        regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
        (evmSp ↦ₘ d0) ** (evmSp + 8 ↦ₘ d1) ** (evmSp + 16 ↦ₘ d2) **
        (evmSp + 24 ↦ₘ d3) ** (Reg.x1 ↦ᵣ base + (152 + 68))) **
       (Reg.x18 ↦ᵣ bit)) ps := by
    refine ⟨ps_inner, ps_x18, hd_x18, hu_x18, ?_, h_x18⟩
    refine ⟨ps_x9x0, ps_cr, hd_cr, hu_cr, h_x9x0, ?_⟩
    refine ⟨ps_x2, ps_r1, hd1, hu1, h_x2, ?_⟩
    refine ⟨ps_x12, ps_r2, hd2, hu2, h_x12, ?_⟩
    refine ⟨ps_x5, ps_r3, hd3, hu3, h_x5, ?_⟩
    refine ⟨ps_a0, ps_r4, hd4, hu4, h_a0, ?_⟩
    refine ⟨ps_a1, ps_r5, hd5, hu5, h_a1, ?_⟩
    refine ⟨ps_a2, ps_r6, hd6, hu6, h_a2, ?_⟩
    refine ⟨ps_a3, ps_r7, hd7, hu7, h_a3, ?_⟩
    refine ⟨ps_sp, ps_r8, hd8, hu8, h_sp, ?_⟩
    refine ⟨ps_e32, ps_r9, hd9, hu9, h_e32, ?_⟩
    refine ⟨ps_x6, ps_r10, hd10, hu10, h_x6, ?_⟩
    refine ⟨ps_x7, ps_r11, hd11, hu11, h_x7, ?_⟩
    refine ⟨ps_x10, ps_r12, hd12, hu12, h_x10, ?_⟩
    refine ⟨ps_x11, ps_r13, hd13, hu13, h_x11, ?_⟩
    refine ⟨ps_d0, _, hd_d0, hu_d0, h_d0, ?_⟩
    refine ⟨ps_d1, _, hd_d1, hu_d1, h_d1, ?_⟩
    refine ⟨ps_d2, _, hd_d2, hu_d2, h_d2, ?_⟩
    exact ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩
  sep_perm h_d3_full

/-- Combined `loopPost → iterPre` bridge: covers both skip (bit = 0) and
    cond (bit ≠ 0) branches of `expTwoMulIterLoopPost`.

    This is the key ingredient for the 256-iteration loop body induction:
    each application of the peel theorem needs to transition from the
    loop-back post-state to the next iteration's pre-state. -/
theorem expTwoMulIterLoopPost_to_iterPre
    {k bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord} {ps : PartialState} (hk : k ≠ 0)
    (h : expTwoMulIterLoopPost k bit sp evmSp base a0 a1 a2 a3 squareW rw ps) :
    ∃ e' v18' vOld' r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3',
      expTwoMulIterPre e' k v18' sp evmSp vOld'
        r0' r1' r2' r3' d0 d1 d2 d3 e0' e1' e2' e3' a0 a1 a2 a3 ps := by
  rw [expTwoMulIterLoopPost_unfold] at h
  rcases h with hCond | hSkip
  · -- Cond path (bit ≠ 0)
    obtain ⟨d0, d1, d2, d3, hpre⟩ :=
      expTwoMulIterCondPost_to_iterPre hk hCond
    exact ⟨rw.getLimbN 3, bit + signExtend12 0, (base + 152) + 68,
           rw.getLimbN 0, rw.getLimbN 1, rw.getLimbN 2, rw.getLimbN 3,
           d0, d1, d2, d3,
           rw.getLimbN 0, rw.getLimbN 1, rw.getLimbN 2, rw.getLimbN 3,
           hpre⟩
  · -- Skip path (bit = 0)
    obtain ⟨d0, d1, d2, d3, hpre⟩ :=
      expTwoMulIterSkipPost_to_iterPre hk hSkip
    exact ⟨squareW.getLimbN 3, bit + signExtend12 0, (base + 44) + 68,
           squareW.getLimbN 0, squareW.getLimbN 1, squareW.getLimbN 2, squareW.getLimbN 3,
           d0, d1, d2, d3,
           squareW.getLimbN 0, squareW.getLimbN 1, squareW.getLimbN 2, squareW.getLimbN 3,
           hpre⟩

-- The abstract n-step loop-body spec from loopPost(n) is blocked by Lean 4 elaboration
-- depth when using exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
-- directly in a Nat.rec induction (the peel theorem + succ_step combination produces a term
-- too large for the elaborator at the final `exact` step).
--
-- PROOF SKETCH (see bead evm-asm-w5mk notes):
-- By Nat.rec on n:
--   Base (n=0): exp_loop_body_zero_step_vacuous (vacuous, loopPost(0)=False)
--   Step (k+1): apply expTwoMulIterLoopPost_to_iterPre bridge → iterPre,
--               then apply exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
--               with hExit = vacuous (k≠0) or hExitFinal (k=0), hLoop = IH instantiated at
--               the post-iteration state values (expTwoMulIterBit e', squarW', rwW').
--
-- This would give: cpsTripleWithin (n * 189) ... (loopPost n ...) loopExitPre
-- Combined with hEntry (loopEntryPost → iterPre) and exp_two_mul_full_loop_boundary_of_entry_body_spec_within,
-- this closes the full 256-iteration loop body spec.

end EvmAsm.Evm64.Exp.Compose
