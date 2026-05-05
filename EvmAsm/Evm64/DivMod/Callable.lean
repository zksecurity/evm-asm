/-
  EvmAsm.Evm64.DivMod.Callable

  LP64-callable shims around `evm_div` / `evm_mod`.

  Per `docs/sdiv-smod-design.md` §3 (corrected layout, PR #2376), the
  shim is **not** `evm_div ;; cc_ret`: appending `cc_ret` to the program
  text would place it at byte 1268, unreachable from `evm_div`'s exit
  PC. Instead we **replace the NOP** at the existing exit slot with
  `cc_ret`, keeping every other instruction at exactly the same offset
  (so internal branch targets — including `divK_loopBody`'s
  `subr_off = 556` into `divK_div128` — remain valid).

      evm_div  := … ;; ADDI .x0 .x0 0       ;; divK_div128
      evm_div_callable
              := … ;; cc_ret                 ;; divK_div128

  Same total instruction count (1:1 NOP↔cc_ret swap), same byte length
  (1276 bytes = 319 instructions), same exit PC (the slot that holds
  the swapped instruction sits at the same byte offset as the original
  NOP).

  This file is **prep slice A** for evm-asm-8pfe / GH #90: it
  introduces only the Program definitions and length lemmas.
  Code-region helpers, sub-code lemmas and the
  `_function_spec` round-trip will land in follow-up slices.

  Reference: GH #90 (parent evm-asm-34sg), beads slice evm-asm-0tnux.
  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.Compose.Base
import EvmAsm.Evm64.CallingConvention

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Program definitions
-- ============================================================================

/-- LP64-callable wrapper for `evm_div`: swap the NOP at the exit slot
    with `cc_ret`. Every other phase / sub-block, including the
    appended `divK_div128` subroutine and all internal branch offsets,
    is kept at exactly the same instruction index as in `evm_div`. -/
def evm_div_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_div_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128

/-- LP64-callable wrapper for `evm_mod`: same shape as
    `evm_div_callable`, with `divK_mod_epilogue` for the remainder
    output. -/
def evm_mod_callable : Program :=
  divK_phaseA 1020 ;;
  divK_phaseB ;;
  divK_clz ;;
  divK_phaseC2 172 ;;
  divK_normB ;;
  divK_normA 40 ;;
  divK_copyAU ;;
  divK_loopSetup 464 ;;
  divK_loopBody 560 7736 ;;
  divK_denorm ;;
  divK_mod_epilogue 24 ;;
  divK_zeroPath ;;
  cc_ret ;;            -- replaces the NOP at the exit slot
  divK_div128

-- ============================================================================
-- CodeReq abbreviations
-- ============================================================================

/-- 14-block CodeReq layout for `evm_div_callable`. Identical to `divCode`
    (see `Evm64/DivMod/Compose/Base.lean`) except block 12 — the NOP at
    `nopOff = 1068` — is replaced with `cc_ret_code (base + nopOff)` to
    match the NOP↔`cc_ret` swap performed in `evm_div_callable`'s Program
    definition. All other blocks (including the appended `divK_div128`
    subroutine at `div128Off = 1072`) keep the same offset, so internal
    branch targets remain valid.

    No equality bridge with `CodeReq.ofProg base evm_div_callable` is
    proved here; that is a follow-up slice. -/
abbrev evm_div_callable_code (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + epilogueOff)   (divK_div_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),                          -- block 12: NOP ↔ cc_ret swap
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

/-- 14-block CodeReq layout for `evm_mod_callable`. Identical to
    `evm_div_callable_code` except block 10 uses `divK_mod_epilogue`
    (mirrors `modCode` vs `divCode` in `Compose/Base.lean`). -/
abbrev evm_mod_callable_code (base : Word) : CodeReq :=
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
    CodeReq.ofProg (base + epilogueOff)   (divK_mod_epilogue 24),
    CodeReq.ofProg (base + zeroPathOff)   divK_zeroPath,
    cc_ret_code   (base + nopOff),                          -- block 12: NOP ↔ cc_ret swap
    CodeReq.ofProg (base + div128Off)     divK_div128
  ]

-- ============================================================================
-- Per-block subsumption lemmas
--
-- For each of the 14 blocks of `evm_div_callable_code` / `evm_mod_callable_code`
-- (the same 14 union slots as `divCode` / `modCode`, with block 12 being
-- `cc_ret_code` instead of the NOP), prove that the block ⊆ the full callable
-- code. Mirrors the `shared_b*_div` / `shared_b*_mod` pattern from
-- `Compose/Base.lean`, with one extra length lemma for `cc_ret` and a local
-- `skipBlockC` macro that includes it in the simp set used by the skipBlock
-- disjointness step.
--
-- These are what later slices (the `_function_spec` round-trip via
-- `callNear_function_spec`) need to compose `evm_div_stack_spec_within`
-- (over `divCode`) with `ret_spec_within'` (over `cc_ret_code (base + nopOff)`)
-- into the full LP64 callable spec.
-- ============================================================================

/-- `cc_ret = JALR .x0 .x1 0` has length 1. Local mirror of the
    `divK_*_len` lemmas in `Compose/Base.lean`, needed so the local
    `skipBlockC` macro can reduce `cc_ret`'s contribution to the
    disjointness range argument. -/
theorem cc_ret_len : cc_ret.length = 1 := by decide

/-- Local variant of `Compose.Base.skipBlock` that additionally simps
    `cc_ret_len`. Used to skip past the `cc_ret_code` block (slot 12) when
    establishing disjointness in the per-block subsumption proofs below. -/
local macro "skipBlockC" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len, divK_div128_v2_len,
          divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
        bv_omega)))

-- ----------------------------------------------------------------------------
-- evm_div_callable_code per-block subsumption (block 12 = cc_ret)
-- ----------------------------------------------------------------------------

private theorem callable_b0_div {b : Word} : ∀ a i,
    (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
private theorem callable_b1_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b2_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b3_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b4_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b5_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b6_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b7_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b8_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b9_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b10_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b11_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b12_div {b : Word} : ∀ a i,
    (cc_ret_code (b + nopOff)) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b13_div {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left

/-- Bundle the 14 per-block subsumptions for `evm_div_callable_code`.
    The 13 `divK_*` blocks are at the same offsets as in `divCode`; the
    new `cc_ret_code (base + nopOff)` slot replaces the original NOP at
    `nopOff` (block 12). Used downstream to lift block-local specs into
    the full callable code. -/
theorem evm_div_callable_code_block_subs (base : Word) :
    (∀ a i, (CodeReq.ofProg base (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + normBOff) divK_normB) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (cc_ret_code (base + nopOff)) a = some i →
      (evm_div_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128) a = some i →
      (evm_div_callable_code base) a = some i) :=
  ⟨callable_b0_div, callable_b1_div, callable_b2_div, callable_b3_div,
   callable_b4_div, callable_b5_div, callable_b6_div, callable_b7_div,
   callable_b8_div, callable_b9_div, callable_b10_div, callable_b11_div,
   callable_b12_div, callable_b13_div⟩

-- ----------------------------------------------------------------------------
-- evm_mod_callable_code per-block subsumption (mirrors div, block 10 differs)
-- ----------------------------------------------------------------------------

private theorem callable_b0_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg b (divK_phaseA 1020)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]; exact CodeReq.union_mono_left
private theorem callable_b1_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b2_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + clzOff) divK_clz) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b3_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b4_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + normBOff) divK_normB) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b5_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b6_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b7_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; exact CodeReq.union_mono_left
private theorem callable_b8_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b9_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b10_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b11_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b12_mod {b : Word} : ∀ a i,
    (cc_ret_code (b + nopOff)) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod {b : Word} : ∀ a i,
    (CodeReq.ofProg (b + div128Off) divK_div128) a = some i → (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC; skipBlockC
  exact CodeReq.union_mono_left

/-- Bundle the 14 per-block subsumptions for `evm_mod_callable_code`. -/
theorem evm_mod_callable_code_block_subs (base : Word) :
    (∀ a i, (CodeReq.ofProg base (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (cc_ret_code (base + nopOff)) a = some i →
      (evm_mod_callable_code base) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + div128Off) divK_div128) a = some i →
      (evm_mod_callable_code base) a = some i) :=
  ⟨callable_b0_mod, callable_b1_mod, callable_b2_mod, callable_b3_mod,
   callable_b4_mod, callable_b5_mod, callable_b6_mod, callable_b7_mod,
   callable_b8_mod, callable_b9_mod, callable_b10_mod, callable_b11_mod,
   callable_b12_mod, callable_b13_mod⟩

end EvmAsm.Evm64
