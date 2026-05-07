/-
  EvmAsm.Rv64.RLP.Phase4HintReadLoop

  Multi-dword Phase 4 wrapper for the RLP decoder: a loop that repeatedly
  invokes the SP1 HINT_READ syscall to populate an arbitrary-length output
  buffer in 8-byte (one-dword) chunks.

  The body is a 5-instruction loop:

      LI   x5,  0xF1            ; SP1 HINT_READ selector
      ECALL                     ; consume up to 8 bytes into [x10]
      ADDI x10, x10, 8          ; advance buffer pointer by 8 bytes
      ADDI x11, x11, -8         ; decrement remaining-byte counter by 8
      BNE  x11, x0, -16         ; if counter != 0, branch back to ECALL

  The branch target offset `-16` lands at `base + 4` — the ECALL
  instruction (PC of the BNE is `base + 16`, signExtend13 (-16) = -16, and
  `(base + 16) + (-16) = base`; but the SP1 selector at `base` only needs
  to be re-loaded if x5 was clobbered — since ECALL preserves x5 we can
  in principle branch back to ECALL directly. We keep the BNE target at
  `base + 4` so the spec of the body re-uses `(.x5 ↦ᵣ 0xF1)` from the
  prior iteration without re-running LI).

  This file lands ONLY the program assembly and the
  `CodeReq.ofProg`-unfold lemma. The companion `cpsTriple` loop spec
  (memory packing via `bytesToWordLE`, multi-iteration invariant) and
  the whole-input specialization are follow-up sub-slices under
  `evm-asm-fvoat`.

  Distinctive token: `rlp_phase4_hint_read_loop_prog Phase4HintReadLoop`.

  Refs: GH #120 (RLP RISC-V decoder, Phase 4), beads
  `evm-asm-fvoat` (parent, multi-dword wrapper), `evm-asm-2j6ry`
  (this slice).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.Tactics.SeqFrame

namespace EvmAsm.Rv64.RLP

/-- Five-instruction multi-dword HINT_READ loop body.

    Conventions (per the SP1 HINT_READ ABI used in Phase 4):
    * `x10` — destination buffer pointer (in/out, advances by 8 each iter).
    * `x11` — remaining-byte counter (in/out, decrements by 8 each iter).
    * `x5`  — set to `0xF1` (HINT_READ selector); preserved across ECALL.

    The branch-back target is `signExtend13 (-16 : BitVec 13)` from the
    BNE site (`base + 16`), landing at `base + 0` — i.e. the LI re-runs.
    A future revision may shift the BNE target to `base + 4` to skip the
    redundant LI; for the structural-lemma slice the simpler shape is
    preferred. -/
def rlp_phase4_hint_read_loop_prog : Program :=
  [.LI .x5 (BitVec.ofNat 64 0xF1),
   .ECALL,
   .ADDI .x10 .x10 8,
   .ADDI .x11 .x11 (-8),
   .BNE .x11 .x0 (BitVec.ofInt 13 (-16))]

/-- Length lemma: the loop body is 5 instructions = 20 bytes. -/
example : rlp_phase4_hint_read_loop_prog.length = 5 := rfl

/-- `CodeReq.ofProg` unfold for the multi-dword HINT_READ loop body.
    Mirrors `rlp_phase4_hint_read_one_word_code_eq_ofProg`. -/
theorem rlp_phase4_hint_read_loop_code_eq_ofProg (base : Word) :
    CodeReq.ofProg base rlp_phase4_hint_read_loop_prog =
      ((CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF1))).union
        ((CodeReq.singleton (base + 4) .ECALL).union
          ((CodeReq.singleton (base + 8) (.ADDI .x10 .x10 8)).union
            ((CodeReq.singleton (base + 12) (.ADDI .x11 .x11 (-8))).union
              (CodeReq.singleton (base + 16)
                (.BNE .x11 .x0 (BitVec.ofInt 13 (-16)))))))) := by
  simp only [rlp_phase4_hint_read_loop_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]
  bv_addr

/-- The LI .x5 0xF1 spec at instruction offset 0 of the multi-dword
    HINT_READ loop body, lifted to the full 5-instruction loop CodeReq.

    Mirrors the `hli_ext` shape inside
    `rlp_phase4_hint_read_one_word_spec_within` (Phase4HintRead.lean).

    First helper of the four step-lift lemmas planned for the eventual
    `rlp_phase4_hint_read_loop_body_step_spec_within` composition (beads
    `evm-asm-yccms`). -/
theorem rlp_phase4_hint_read_loop_li_step_lift_spec_within (base : Word) :
    cpsTripleWithin 1 base (base + 4)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
      (regOwn .x5)
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) := by
  have hli := li_spec_gen_own_within .x5 (BitVec.ofNat 64 0xF1) base (by nofun)
  apply cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
    (hmono := ?_) (h := hli)
  rw [rlp_phase4_hint_read_loop_code_eq_ofProg]
  exact CodeReq.union_mono_left

/-- Helper: the loop CodeReq has the ADDI .x10 .x10 8 instruction at slot
    `base + 8`. -/
theorem rlp_phase4_hint_read_loop_addi_advance_get (base : Word) :
    (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog) (base + 8) =
      some (.ADDI .x10 .x10 8) := by
  rw [rlp_phase4_hint_read_loop_code_eq_ofProg]
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base) (a' := base + 8)
      (i := .LI .x5 (BitVec.ofNat 64 0xF1)) (by bv_omega)
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base + 4) (a' := base + 8)
      (i := .ECALL) (by bv_omega)
  exact CodeReq.union_hit (CodeReq.singleton_get (base + 8) _)

/-- Helper: the loop CodeReq has the ADDI .x11 .x11 (-8) instruction at slot
    `base + 12`. -/
theorem rlp_phase4_hint_read_loop_addi_dec_get (base : Word) :
    (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog) (base + 12) =
      some (.ADDI .x11 .x11 (-8)) := by
  rw [rlp_phase4_hint_read_loop_code_eq_ofProg]
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base) (a' := base + 12)
      (i := .LI .x5 (BitVec.ofNat 64 0xF1)) (by bv_omega)
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base + 4) (a' := base + 12)
      (i := .ECALL) (by bv_omega)
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base + 8) (a' := base + 12)
      (i := .ADDI .x10 .x10 8) (by bv_omega)
  exact CodeReq.union_hit (CodeReq.singleton_get (base + 12) _)

/-- The ADDI .x10 .x10 8 spec at instruction offset 8 (third instruction)
    of the multi-dword HINT_READ loop body, lifted to the full
    5-instruction loop CodeReq.

    Second helper toward `rlp_phase4_hint_read_loop_body_step_spec_within`
    (beads `evm-asm-yccms`). -/
theorem rlp_phase4_hint_read_loop_addi_advance_step_lift_spec_within
    (base : Word) (v10 : Word) :
    cpsTripleWithin 1 (base + 8) ((base + 8) + 4)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
      (.x10 ↦ᵣ v10)
      (.x10 ↦ᵣ (v10 + signExtend12 (8 : BitVec 12))) := by
  have h := addi_spec_gen_same_within .x10 v10 (8 : BitVec 12) (base + 8) (by nofun)
  apply cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
    (hmono := ?_) (h := h)
  exact CodeReq.singleton_mono (rlp_phase4_hint_read_loop_addi_advance_get base)

/-- The ADDI .x11 .x11 (-8) spec at instruction offset 12 (fourth
    instruction) of the multi-dword HINT_READ loop body, lifted to the
    full 5-instruction loop CodeReq.

    Third helper toward `rlp_phase4_hint_read_loop_body_step_spec_within`
    (beads `evm-asm-yccms`). -/
theorem rlp_phase4_hint_read_loop_addi_dec_step_lift_spec_within
    (base : Word) (v11 : Word) :
    cpsTripleWithin 1 (base + 12) ((base + 12) + 4)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
      (.x11 ↦ᵣ v11)
      (.x11 ↦ᵣ (v11 + signExtend12 (-8 : BitVec 12))) := by
  have h := addi_spec_gen_same_within .x11 v11 (-8 : BitVec 12) (base + 12) (by nofun)
  apply cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
    (hmono := ?_) (h := h)
  exact CodeReq.singleton_mono (rlp_phase4_hint_read_loop_addi_dec_get base)

/-- Helper: the loop CodeReq has the ECALL instruction at slot `base + 4`. -/
theorem rlp_phase4_hint_read_loop_ecall_get (base : Word) :
    (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog) (base + 4) =
      some .ECALL := by
  rw [rlp_phase4_hint_read_loop_code_eq_ofProg]
  refine CodeReq.union_skip ?_ ?_
  · exact CodeReq.singleton_miss (a := base) (a' := base + 4)
      (i := .LI .x5 (BitVec.ofNat 64 0xF1)) (by bv_omega)
  exact CodeReq.union_hit (CodeReq.singleton_get (base + 4) _)

/-- The ECALL HINT_READ spec at instruction offset 4 (second instruction)
    of the multi-dword HINT_READ loop body, lifted to the full
    5-instruction loop CodeReq.

    Mirrors the `hread_ext` shape inside
    `rlp_phase4_hint_read_one_word_spec_within` (Phase4HintRead.lean L72).
    Combined with the LI / ADDI advance / ADDI dec step-lifts above,
    this is the fourth and final per-instruction helper toward the
    eventual `rlp_phase4_hint_read_loop_body_step_spec_within`
    composition (beads `evm-asm-yccms`). -/
theorem rlp_phase4_hint_read_loop_ecall_step_lift_spec_within
    (buf nbytes oldWord : Word) (input : List (BitVec 8)) (base : Word)
    (h_pos : 0 < nbytes.toNat) (h_le8 : nbytes.toNat ≤ 8)
    (h_suff : nbytes.toNat ≤ input.length) :
    cpsTripleWithin 1 (base + 4) ((base + 4) + 4)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs input)
      ((.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
  have h := ecall_hint_read_one_word_spec_gen_within
    buf nbytes oldWord input (base + 4) h_pos h_le8 h_suff
  apply cpsTripleWithin_extend_code
    (cr' := CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
    (hmono := ?_) (h := h)
  exact CodeReq.singleton_mono (rlp_phase4_hint_read_loop_ecall_get base)

/-- Bundled body-step spec for one iteration of the multi-dword
    HINT_READ loop, covering the four straight-line instructions
    (`LI ;; ECALL ;; ADDI x10 +8 ;; ADDI x11 -8`) at offsets 0..16.
    The fifth instruction (the back-branch BNE at offset 16) is the
    loop-control step composed in a follow-up slice.

    Composition of the four step-lift helpers above via three
    applications of `cpsTripleWithin_seq_perm_same_cr`. Authored by
    @pirapira; implemented by Hermes-bot (evm-hermes) for beads
    `evm-asm-yccms` (#120 Phase4HintReadLoop slice 2). -/
theorem rlp_phase4_hint_read_loop_body_step_spec_within
    (buf nbytes oldWord : Word) (input : List (BitVec 8)) (base : Word)
    (h_pos : 0 < nbytes.toNat) (h_le8 : nbytes.toNat ≤ 8)
    (h_suff : nbytes.toNat ≤ input.length) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog)
      ((base + 4 ↦ᵢ .ECALL) ** regOwn .x5 ** (.x10 ↦ᵣ buf) **
        (.x11 ↦ᵣ nbytes) ** (buf ↦ₘ oldWord) ** privateInputIs input)
      ((base + 4 ↦ᵢ .ECALL) **
        (.x10 ↦ᵣ (buf + signExtend12 (8 : BitVec 12))) **
        (.x11 ↦ᵣ (nbytes + signExtend12 (-8 : BitVec 12))) **
        (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
        privateInputIs (input.drop nbytes.toNat)) := by
  -- Step 1: LI .x5 0xF1 at offset 0, framed by the rest.
  have hli := rlp_phase4_hint_read_loop_li_step_lift_spec_within base
  have hli_framed := cpsTripleWithin_frameR
    ((base + 4 ↦ᵢ .ECALL) ** (.x10 ↦ᵣ buf) ** (.x11 ↦ᵣ nbytes) **
      (buf ↦ₘ oldWord) ** privateInputIs input)
    (by pcFree) hli
  -- Step 2: ECALL HINT_READ at offset 4. Normalize exit to `base + 8`.
  have hecall0 := rlp_phase4_hint_read_loop_ecall_step_lift_spec_within
    buf nbytes oldWord input base h_pos h_le8 h_suff
  have h_e0 : (base + 4 : Word) + 4 = base + 8 := by bv_addr
  rw [h_e0] at hecall0
  set hecall := hecall0
  -- Step 3: ADDI .x10 .x10 8 at offset 8.
  have haddi10 := rlp_phase4_hint_read_loop_addi_advance_step_lift_spec_within
    base buf
  -- Step 4: ADDI .x11 .x11 -8 at offset 12.
  have haddi11 := rlp_phase4_hint_read_loop_addi_dec_step_lift_spec_within
    base nbytes
  -- Compose step 1 ;; step 2.
  have h12 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) hli_framed hecall
  -- Frame ADDI .x10 step with the remaining post-step-2 atoms (everything
  -- except `.x10 ↦ᵣ buf` which is the active register cell).
  have haddi10_framed := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ nbytes) **
      (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
      (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
      privateInputIs (input.drop nbytes.toNat))
    (by pcFree) haddi10
  -- (base + 8) + 4 = base + 12 to align endpoints.
  have h_e1 : (base + 8 : Word) + 4 = base + 12 := by bv_addr
  rw [h_e1] at haddi10_framed
  -- Compose step1+2 ;; step 3.
  have h123 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) h12 haddi10_framed
  -- Frame ADDI .x11 step with the remaining atoms (everything except `.x11`).
  have haddi11_framed := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (buf + signExtend12 (8 : BitVec 12))) **
      (buf ↦ₘ bytesToWordLE (input.take nbytes.toNat)) **
      (base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF1)) **
      privateInputIs (input.drop nbytes.toNat))
    (by pcFree) haddi11
  have h_e2 : (base + 12 : Word) + 4 = base + 16 := by bv_addr
  rw [h_e2] at haddi11_framed
  -- Compose step1+2+3 ;; step 4.
  have h1234 :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp) h123 haddi11_framed
  -- Normalize step count `1 + 1 + 1 + 1` to `4`.
  have h1234' : cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base rlp_phase4_hint_read_loop_prog) _ _ := h1234
  -- Final cleanup: rearrange to match the stated postcondition shape and
  -- the goal's preferred pre permutation (`(base + 4 ↦ᵢ .ECALL)` first).
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    h1234'

end EvmAsm.Rv64.RLP
