/-
  EvmAsm.Evm64.DivMod.SpecCall

  Call-trial precondition bundles for the 256-bit EVM DIV and MOD
  programs. Extracted from `Spec.lean` to stay under the 1500-line
  file-size guardrail.

  The call-trial variants use `divScratchValuesCall` (19 cells — the
  base `divScratchValues` 15 cells plus 4 extras for the `div128`
  subroutine call path). Used as preconditions of the forthcoming
  `evm_{div,mod}_n4_full_call_{skip,addback}_stack_pre_spec` theorems.

  `divN4StackPreCall` sits next to `divN4StackPre` in `Spec.lean`; this
  file adds the MOD-side counterpart `modN4StackPreCall`.
-/

import EvmAsm.Evm64.DivMod.Spec
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4Shift0

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)
open EvmWord (val256)

/-- Call-trial counterpart to `modN4StackPre`. Identical to `modN4StackPre`
    except the scratch bundle: uses `divScratchValuesCall` (19 cells)
    instead of `divScratchValues` (15 cells).

    Used as the precondition of the forthcoming
    `evm_mod_n4_full_call_{skip,addback}_stack_pre_spec` theorems.
    Definitionally equal to `divN4StackPreCall`. -/
@[irreducible]
def modN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
  (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
  (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
  (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
  (.x11 ↦ᵣ v11) **
  evmWordIs sp a ** evmWordIs (sp + 32) b **
  divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0

theorem pcFree_modN4StackPreCall (sp : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (modN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  delta modN4StackPreCall divScratchValuesCall; pcFree

instance (sp : Word) (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree (modN4StackPreCall sp a b v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0) :=
  ⟨pcFree_modN4StackPreCall sp a b v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratch_un0⟩

/-- Named unfold for `modN4StackPreCall`. Mirror of `divN4StackPreCall_unfold`. -/
theorem modN4StackPreCall_unfold {sp : Word} {a b : EvmWord}
    {v5 v6 v7 v10 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    modN4StackPreCall sp a b v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
     (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
     (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     (.x11 ↦ᵣ v11) **
     evmWordIs sp a ** evmWordIs (sp + 32) b **
     divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
       shiftMem nMem jMem retMem dMem dloMem scratch_un0) := by
  delta modN4StackPreCall; rfl

/-- Call-trial counterpart to `divN4MaxSkipStackPost`. Identical content
    except for the scratch ownership: uses `divScratchOwnCall` (19 cells)
    instead of `divScratchOwn` (15 cells), reflecting the 4 extra scratch
    slots used by the `div128` subroutine call path.

    Paired with `divN4StackPreCall` for the forthcoming
    `evm_div_n4_call_skip_stack_spec`. -/
@[irreducible]
def divN4CallSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
  divScratchOwnCall sp

/-- Named unfold for `divN4CallSkipStackPost`. Mirror of
    `divN4MaxSkipStackPost_unfold` but with `divScratchOwnCall`. -/
theorem divN4CallSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    divN4CallSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
     divScratchOwnCall sp) := by
  delta divN4CallSkipStackPost; rfl

theorem pcFree_divN4CallSkipStackPost (sp : Word) (a b : EvmWord) :
    (divN4CallSkipStackPost sp a b).pcFree := by
  rw [divN4CallSkipStackPost_unfold, divScratchOwnCall_unfold,
      divScratchOwn_unfold]
  pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (divN4CallSkipStackPost sp a b) :=
  ⟨pcFree_divN4CallSkipStackPost sp a b⟩

/-- Call-trial counterpart to `modN4MaxSkipStackPost`. Identical content
    except for the scratch ownership: uses `divScratchOwnCall` (19 cells).
    Paired with `modN4StackPreCall` for the forthcoming
    `evm_mod_n4_call_skip_stack_spec`. -/
@[irreducible]
def modN4CallSkipStackPost (sp : Word) (a b : EvmWord) : Assertion :=
  (.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
  regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
  regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
  evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
  divScratchOwnCall sp

/-- Named unfold for `modN4CallSkipStackPost`. -/
theorem modN4CallSkipStackPost_unfold {sp : Word} {a b : EvmWord} :
    modN4CallSkipStackPost sp a b =
    ((.x12 ↦ᵣ (sp + 32)) ** regOwn .x1 ** regOwn .x2 **
     regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
     regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
     evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
     divScratchOwnCall sp) := by
  delta modN4CallSkipStackPost; rfl

theorem pcFree_modN4CallSkipStackPost (sp : Word) (a b : EvmWord) :
    (modN4CallSkipStackPost sp a b).pcFree := by
  rw [modN4CallSkipStackPost_unfold, divScratchOwnCall_unfold,
      divScratchOwn_unfold]
  pcFree

instance (sp : Word) (a b : EvmWord) :
    Assertion.PCFree (modN4CallSkipStackPost sp a b) :=
  ⟨pcFree_modN4CallSkipStackPost sp a b⟩

/-- Call-path counterpart to `div_n4_max_skip_stack_weaken`. Weakens a
    concrete post state (19-cell `divScratchValuesCall` + 7 register
    values) to `divN4CallSkipStackPost`. Structural mirror of the
    max-path weakener, with `divScratchValuesCall_implies_divScratchOwnCall`
    handling the 19-cell scratch weakening (4 extra cells beyond the 15
    of `divScratchValues`).

    Used by the forthcoming `evm_div_n4_call_skip_stack_spec` — the
    remaining semantic bridge (connecting `div128Quot`'s output to
    `(EvmWord.div a b).getLimbN 0..3`) depends on Knuth B.  -/
theorem div_n4_call_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    (v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word)
    (q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.div a b) **
       divScratchValuesCall sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p) h →
      divN4CallSkipStackPost sp a b h := by
  intro h hp
  delta divN4CallSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p

/-- MOD counterpart of `div_n4_call_skip_stack_weaken`. Same structural
    weakening; only the second operand slot holds `EvmWord.mod a b`
    instead of `EvmWord.div a b`. -/
theorem mod_n4_call_skip_stack_weaken
    (sp : Word) (a b : EvmWord)
    (v1_p v2_p v5_p v6_p v7_p v10_p v11_p : Word)
    (q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
     shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p : Word) :
    ∀ h,
      ((.x12 ↦ᵣ (sp + 32)) **
       (.x1 ↦ᵣ v1_p) ** (.x2 ↦ᵣ v2_p) **
       (.x5 ↦ᵣ v5_p) ** (.x6 ↦ᵣ v6_p) ** (.x7 ↦ᵣ v7_p) **
       (.x10 ↦ᵣ v10_p) ** (.x11 ↦ᵣ v11_p) **
       (.x0 ↦ᵣ (0 : Word)) **
       evmWordIs sp a ** evmWordIs (sp + 32) (EvmWord.mod a b) **
       divScratchValuesCall sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p
         u5_p u6_p u7_p shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p) h →
      modN4CallSkipStackPost sp a b h := by
  intro h hp
  delta modN4CallSkipStackPost
  refine sepConj_mono_right ?_ h hp
  iterate 7 apply sepConj_mono (regIs_implies_regOwn _)
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact divScratchValuesCall_implies_divScratchOwnCall
    sp q0P q1P q2_p q3_p u0P u1P u2P u3P u4_p u5_p u6_p u7_p
    shift_p n_p j_p retMem_p dMem_p dloMem_p scratch_un0_p

-- ============================================================================
-- DIV n=4 call+skip full-path stack-pre wrappers
-- ============================================================================

/-- EvmWord-level wrapper over `evm_div_n4_full_call_skip_spec`: same
    guarantee (full-path DIV from `base` to `base + nopOff` on the n=4 call+skip
    sub-path) but with the operands bundled as `evmWordIs sp a` /
    `evmWordIs (sp+32) b` and the 19 scratch cells bundled as
    `divScratchValuesCall`.

    The postcondition is still the concrete `fullDivN4CallSkipPost` — turning
    that into `divN4CallSkipStackPost` requires the semantic-correctness bridge
    which depends on Knuth B / `div128Quot` correctness (in progress on a
    separate chain).

    The call-trial path needs an extra `halign` hypothesis because the
    `div128` subroutine returns via `JALR` to `base + 516`, and the stack
    spec must account for the alignment requirement on the return address. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_call_skip_stack_pre_spec`: takes
    the precondition as a single `divN4StackPreCall` atom. Mirror of
    `evm_div_n4_full_max_skip_stack_pre_spec_bundled`. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_call_skip_spec`. Same shape
    as `evm_div_n4_full_call_skip_stack_pre_spec` but for the MOD path:
    `divCode → modCode`, `evm_div_n4_full_call_skip_spec →
    evm_mod_n4_full_call_skip_spec`, and `fullDivN4CallSkipPost →
    fullModN4CallSkipPost`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_skip_stack_pre_spec`: takes
    the precondition as a single `modN4StackPreCall` atom. Mirror of
    `evm_div_n4_full_call_skip_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Call-trial addback (BEQ double-addback): EvmWord-level wrappers
-- ============================================================================

/-- EvmWord-level wrapper over `evm_div_n4_full_call_addback_beq_spec`. The
    same shape as `evm_div_n4_full_call_skip_stack_pre_spec` but for the
    addback branch: `hborrow` has the borrow-fires direction
    (`isAddbackBorrowN4CallEvm`) and the BEQ variant also requires the
    `hcarry2_nz` indicator.

    The postcondition is still the concrete `fullDivN4CallAddbackBeqPost`
    — turning that into `divN4CallAddbackBeqStackPost` requires the
    semantic-correctness bridge which depends on Knuth B / `div128Quot`
    correctness (separate chain). -/
theorem evm_div_n4_full_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_call_addback_beq_stack_pre_spec`:
    takes the precondition as a single `divN4StackPreCall` atom. Mirror
    of `evm_div_n4_full_call_skip_stack_pre_spec_bundled` for the addback
    branch. -/
theorem evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hvalid : ValidMemRange sp 8)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz hvalid halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_call_addback_beq_spec`. Same
    shape as `evm_div_n4_full_call_addback_beq_stack_pre_spec` but for the
    MOD path: `divCode → modCode`, `evm_div_n4_full_call_addback_beq_spec →
    evm_mod_n4_full_call_addback_beq_spec`, and `fullDivN4CallAddbackBeqPost
    → fullModN4CallAddbackBeqPost`.

    The MOD version does NOT require the `hvalid : ValidMemRange sp 8`
    hypothesis that the DIV variant carries — the MOD preloop+full-path
    specs don't consume validity hypotheses. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_call_addback_beq_stack_pre_spec`:
    takes the precondition as a single `modN4StackPreCall` atom. Mirror
    of `evm_div_n4_full_call_addback_beq_stack_pre_spec_bundled`. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallEvm a b)
    (hborrow : isAddbackBorrowN4CallEvm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Shift = 0 call-trial skip: DIV EvmWord-level wrapper
-- ============================================================================

/-- Skip-addback condition at n=4 shift=0 path in EvmWord form: the runtime
    borrow check doesn't fire, so the algorithm skips addback after the
    `div128`-computed trial quotient. Shift=0 specialization (no
    normalization applied). -/
def isSkipBorrowN4Shift0Evm (a b : EvmWord) : Prop :=
  isSkipBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                       (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isSkipBorrowN4Shift0Evm_def {a b : EvmWord} :
    isSkipBorrowN4Shift0Evm a b =
    isSkipBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                         (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- EvmWord-level wrapper over `evm_div_n4_full_shift0_call_skip_spec`.
    Shift=0 specialization: b3 already has its top bit set, so no
    normalization is applied and `u4 = 0` at runtime — the call-trial
    BLTU is always taken (there is no `hbltu` hypothesis here).

    The postcondition is the concrete `fullDivN4Shift0CallSkipPost` —
    turning that into a semantic stack post requires the separate Knuth-B
    / div128Quot-correctness chain. -/
theorem evm_div_n4_full_shift0_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_shift0_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_shift0_call_skip_stack_pre_spec`:
    takes the precondition as a single `divN4StackPreCall` atom. -/
theorem evm_div_n4_full_shift0_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_shift0_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_shift0_call_skip_spec`.
    MOD counterpart of `evm_div_n4_full_shift0_call_skip_stack_pre_spec`
    with `divCode → modCode` and `fullDivN4Shift0CallSkipPost →
    fullModN4Shift0CallSkipPost`. -/
theorem evm_mod_n4_full_shift0_call_skip_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_shift0_call_skip_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_shift0_call_skip_stack_pre_spec`:
    takes the precondition as a single `modN4StackPreCall` atom. -/
theorem evm_mod_n4_full_shift0_call_skip_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hborrow : isSkipBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallSkipPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_shift0_call_skip_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Shift = 0 call-trial addback (BEQ): EvmWord-level wrappers (DIV + MOD)
-- ============================================================================

/-- Addback-needed condition at n=4 shift=0 path in EvmWord form. Borrow
    fires (mulsub underflowed), so the algorithm decrements the
    `div128Quot`-computed trial quotient and adds back. -/
def isAddbackBorrowN4Shift0Evm (a b : EvmWord) : Prop :=
  isAddbackBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackBorrowN4Shift0Evm_def {a b : EvmWord} :
    isAddbackBorrowN4Shift0Evm a b =
    isAddbackBorrowN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- Double-addback carry2≠0 condition at n=4 shift=0 path in EvmWord form. -/
def isAddbackCarry2NzN4Shift0Evm (a b : EvmWord) : Prop :=
  isAddbackCarry2NzN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem isAddbackCarry2NzN4Shift0Evm_def {a b : EvmWord} :
    isAddbackCarry2NzN4Shift0Evm a b =
    isAddbackCarry2NzN4Shift0 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                              (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := rfl

/-- EvmWord-level wrapper over `evm_div_n4_full_shift0_call_addback_beq_spec`. -/
theorem evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_div_n4_full_shift0_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec`. -/
theorem evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (divCode base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullDivN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_div_n4_full_shift0_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [divN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper over `evm_mod_n4_full_shift0_call_addback_beq_spec`. -/
theorem evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_shift0_call_addback_beq_spec sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz' hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled version of `evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec`. -/
theorem evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec_bundled (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_z : (clzResult (b.getLimbN 3)).1 = 0)
    (halign : ((base + 516) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + 516)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0Evm a b)
    (hborrow : isAddbackBorrowN4Shift0Evm a b) :
    cpsTriple base (base + nopOff) (modCode base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (fullModN4Shift0CallAddbackBeqPost sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_shift0_call_addback_beq_stack_pre_spec sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  exact cpsTriple_weaken
    (fun _ hp => by rw [modN4StackPreCall_unfold] at hp; exact hp)
    (fun _ hq => hq)
    h

-- ============================================================================
-- Semantic-correctness predicates for n=4 call+skip (task #66)
-- ============================================================================

/-- Semantic-correctness precondition for the n=4 call+skip sub-path: the
    algorithm's trial quotient `qHat = div128Quot u4 u3 b3'` is at least
    `⌊val256(a)/val256(b)⌋`.

    Under the runtime skip-borrow check (`isSkipBorrowN4CallEvm`), the upper
    bound `qHat ≤ ⌊val256(a)/val256(b)⌋` is automatic (via T3 =
    `div128Quot_call_skip_le_val256_div`). Adding this hypothesis pins down
    the tight equality `qHat = ⌊val256(a)/val256(b)⌋`, which then feeds
    the stack-spec post reshape into `evmWordIs (sp+32) (EvmWord.div a b)`.

    Mirror pattern of `n4MaxSkipSemanticHolds` (Spec.lean:208), which packages
    the analogous `c3 = 0` hypothesis for max-skip. Here the semantic content
    is the algorithmic lower bound rather than a mulsub carry. Proving this
    from first principles is Knuth TAOCP Theorem A (normalized divisor
    version) — deferred to a future task (formerly issue #65). The stack
    spec delegates the proof to callers (e.g., the higher-level EVM semantic
    composition), following the same contract as the max-skip family. -/
def n4CallSkipSemanticHolds (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot u4 u3 b3').toNat

theorem n4CallSkipSemanticHolds_def {a b : EvmWord} :
    n4CallSkipSemanticHolds a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot u4 u3 b3').toNat) :=
  rfl

end EvmAsm.Evm64
