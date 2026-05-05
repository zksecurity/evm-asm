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
-- Equality bridges with CodeReq.ofProg
--
-- These connect the 14-block `unionAll` abbreviations with the canonical
-- `CodeReq.ofProg base ·` form produced by `evm_div_callable` /
-- `evm_mod_callable`'s 13-`;;` sequence. The proof iterates
-- `CodeReq.ofProg_append` 13 times, normalizing the running base offset to
-- the named constant from `Compose/Offsets.lean` after each step. Mirrors
-- `evm_mul_code_eq_ofProg` (Multiply/LimbSpec.lean) and `expLoopCode_eq_*`
-- (Exp/Compose/Base.lean) — same pattern, longer chain.
-- ============================================================================

open EvmAsm.Rv64.CodeReq in
theorem evm_div_callable_code_eq_ofProg (base : Word) :
    evm_div_callable_code base = CodeReq.ofProg base evm_div_callable := by
  unfold evm_div_callable_code evm_div_callable cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  -- Block 0 → 1: phaseA ;; rest, advance offset to phaseBOff = 32.
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  -- Block 1 → 2: phaseB, advance to clzOff = 116.
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  -- Block 2 → 3: clz, advance to phaseC2Off = 212.
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  -- Block 3 → 4: phaseC2, advance to normBOff = 228.
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  -- Block 4 → 5: normB, advance to normAOff = 312.
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  -- Block 5 → 6: normA, advance to copyAUOff = 396.
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  -- Block 6 → 7: copyAU, advance to loopSetupOff = 432.
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  -- Block 7 → 8: loopSetup, advance to loopBodyOff = 448.
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  -- Block 8 → 9: loopBody, advance to denormOff = 908.
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  -- Block 9 → 10: denorm, advance to epilogueOff = 1008.
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  -- Block 10 → 11: div_epilogue, advance to zeroPathOff = 1048.
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_div_epilogue 24).length) =
        base + zeroPathOff by rw [divK_divEpilogue_len]; bv_omega]
  -- Block 11 → 12: zeroPath, advance to nopOff = 1068 (the cc_ret slot).
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  -- Block 12 → 13: cc_ret (single instruction), advance to div128Off = 1072.
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]

open EvmAsm.Rv64.CodeReq in
theorem evm_mod_callable_code_eq_ofProg (base : Word) :
    evm_mod_callable_code base = CodeReq.ofProg base evm_mod_callable := by
  unfold evm_mod_callable_code evm_mod_callable cc_ret_code
  simp only [unionAll_cons, unionAll_nil, union_empty_right]
  unfold seq
  unfold Program
  symm
  rw [ofProg_append]
  rw [show base + BitVec.ofNat 64 (4 * (divK_phaseA 1020).length) =
        base + phaseBOff by rw [divK_phaseA_len]; rfl]
  rw [ofProg_append]
  rw [show (base + phaseBOff) + BitVec.ofNat 64 (4 * divK_phaseB.length) =
        base + clzOff by rw [divK_phaseB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + clzOff) + BitVec.ofNat 64 (4 * divK_clz.length) =
        base + phaseC2Off by rw [divK_clz_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + phaseC2Off) + BitVec.ofNat 64 (4 * (divK_phaseC2 172).length) =
        base + normBOff by rw [divK_phaseC2_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normBOff) + BitVec.ofNat 64 (4 * divK_normB.length) =
        base + normAOff by rw [divK_normB_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + normAOff) + BitVec.ofNat 64 (4 * (divK_normA 40).length) =
        base + copyAUOff by rw [divK_normA_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + copyAUOff) + BitVec.ofNat 64 (4 * divK_copyAU.length) =
        base + loopSetupOff by rw [divK_copyAU_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopSetupOff) + BitVec.ofNat 64 (4 * (divK_loopSetup 464).length) =
        base + loopBodyOff by rw [divK_loopSetup_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + loopBodyOff) + BitVec.ofNat 64 (4 * (divK_loopBody 560 7736).length) =
        base + denormOff by rw [divK_loopBody_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + denormOff) + BitVec.ofNat 64 (4 * divK_denorm.length) =
        base + epilogueOff by rw [divK_denorm_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + epilogueOff) + BitVec.ofNat 64 (4 * (divK_mod_epilogue 24).length) =
        base + zeroPathOff by rw [divK_modEpilogue_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + zeroPathOff) + BitVec.ofNat 64 (4 * divK_zeroPath.length) =
        base + nopOff by rw [divK_zeroPath_len]; bv_omega]
  rw [ofProg_append]
  rw [show (base + nopOff) + BitVec.ofNat 64 (4 * cc_ret.length) =
        base + div128Off by
    show (base + nopOff) + BitVec.ofNat 64 (4 * 1) = base + div128Off
    bv_omega]
-- Per-block subsumption lemmas for evm_div_callable_code / evm_mod_callable_code
--
-- Mirror the `shared_b*_div` / `shared_b*_mod` pattern from
-- `EvmAsm.Evm64.DivMod.Compose.Base`. Index `N` uses the divCode/modCode
-- block numbering (0..13). Block 12 is `cc_ret_code (base + nopOff)`
-- instead of the NOP — the offset is identical (both length 1), so the
-- disjointness side conditions match modulo a `cc_ret.length = 1` fact.
-- ============================================================================

/-- `cc_ret = JALR x0 x1 0` is exactly one instruction. -/
theorem cc_ret_len : cc_ret.length = 1 := by decide

/-- Variant of `skipBlock` (from `Compose.Base`) that also knows
    `cc_ret.length = 1`. Needed when the block-being-skipped is
    `cc_ret_code` rather than an `ofProg`-of-named-program, since the
    disjointness `bv_omega` asks for the program length. -/
macro "skipBlockCC" : tactic =>
  `(tactic| apply CodeReq.mono_union_right
      (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
        simp only [divK_phaseA_len, divK_phaseB_len, divK_clz_len, divK_phaseC2_len,
          divK_normB_len, divK_normA_len, divK_copyAU_len, divK_loopSetup_len,
          divK_loopBody_len, divK_denorm_len, divK_divEpilogue_len,
          divK_zeroPath_len, divK_nop_len, divK_div128_len, divK_div128_v2_len,
          divK_div128_v4_len, divK_modEpilogue_len, cc_ret_len] at hk1 hk2
        bv_omega)))

-- ----------------------------------------------------------------------------
-- DIV side
-- ----------------------------------------------------------------------------

private theorem callable_b0_div {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_div_epilogue 24)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_div {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_div {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_div_callable_code b) a = some i := by
  unfold evm_div_callable_code; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

/-- Bundle: every per-block subsumption for `evm_div_callable_code`. Mirrors
    `mul_callable_code_block_subs` (Multiply/Callable.lean) so downstream
    composition slices can destructure ⟨b0, b1, …, b13⟩ in one shot. -/
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
-- MOD side (block 10 uses divK_mod_epilogue; everything else identical)
-- ----------------------------------------------------------------------------

private theorem callable_b0_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg b (divK_phaseA 1020)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left
private theorem callable_b1_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseBOff) divK_phaseB) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b2_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + clzOff) divK_clz) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b3_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + phaseC2Off) (divK_phaseC2 172)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b4_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normBOff) divK_normB) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b5_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + normAOff) (divK_normA 40)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b6_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + copyAUOff) divK_copyAU) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b7_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopSetupOff) (divK_loopSetup 464)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b8_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + loopBodyOff) (divK_loopBody 560 7736)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  exact CodeReq.union_mono_left
private theorem callable_b9_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + denormOff) divK_denorm) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; exact CodeReq.union_mono_left
private theorem callable_b10_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + epilogueOff) (divK_mod_epilogue 24)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b11_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + zeroPathOff) divK_zeroPath) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; exact CodeReq.union_mono_left
private theorem callable_b12_mod {b : Word} :
    ∀ a i, (cc_ret_code (b + nopOff)) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons]
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC; skipBlockCC
  exact CodeReq.union_mono_left
private theorem callable_b13_mod {b : Word} :
    ∀ a i, (CodeReq.ofProg (b + div128Off) divK_div128) a = some i →
      (evm_mod_callable_code b) a = some i := by
  unfold evm_mod_callable_code; simp only [CodeReq.unionAll_cons, cc_ret_code]
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock; skipBlock
  skipBlock; skipBlock; skipBlock; skipBlock; skipBlockCC; exact CodeReq.union_mono_left

/-- Bundle: every per-block subsumption for `evm_mod_callable_code`. Mirror
    of `evm_div_callable_code_block_subs`. -/
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
