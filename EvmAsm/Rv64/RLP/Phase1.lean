/-
  EvmAsm.Rv64.RLP.Phase1

  EL.3 Phase 1: RLP prefix classifier.

  Given the first byte `p` of an RLP-encoded item in `x5`, dispatches to one
  of five exits based on the Yellow Paper Appendix B boundaries:

  | Range          | Category      |
  |----------------|---------------|
  | `p < 0x80`     | single byte   |
  | `0x80..0xB7`   | short string  |
  | `0xB8..0xBF`   | long string   |
  | `0xC0..0xF7`   | short list    |
  | `0xF8..0xFF`   | long list     |

  Implementation: a cascade of four `(ADDI x10, x0, K ; BLTU x5, x10, off)`
  steps on the thresholds `0x80, 0xB8, 0xC0, 0xF8`. Each BLTU taken branch is
  one of the first four exits; the final fall-through is the long-list exit.

  Register usage:
    x5  — input prefix byte (zero-extended, `toNat < 256` assumed by caller)
    x10 — scratch (clobbered; holds the last threshold constant on exit)
    x0  — zero register (unchanged)

  This file provides:
    * `rlp_phase1_step_prog` — the 2-instruction cascade-step program
    * `rlp_phase1_classifier_prog` — the full 8-instruction classifier
    * `rlp_phase1_step_code` — the matching `CodeReq`
    * `rlp_phase1_step_spec` — `cpsBranch` spec preserving the dispatch fact
      (`BitVec.ult v5 k_val` on the taken side, `¬…` on the fall-through).
-/

import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.CPSSpec
import EvmAsm.Rv64.Program
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64

-- ============================================================================
-- Program definitions
-- ============================================================================

/-- One cascade step: `ADDI x10, x0, k ; BLTU x5, x10, offset`.
    If `x5 <u k` (unsigned), take the branch; else fall through. -/
def rlp_phase1_step_prog (k : BitVec 12) (offset : BitVec 13) : Program :=
  [.ADDI .x10 .x0 k, .BLTU .x5 .x10 offset]

/-- Full Phase 1 classifier (8 instructions = 32 bytes).

    The four branch offsets are the relative targets of the four taken
    exits (single byte, short string, long string, short list). The
    fall-through at `base + 32` is the long-list exit. -/
def rlp_phase1_classifier_prog
    (off_single off_short_str off_long_str off_short_list : BitVec 13) : Program :=
  rlp_phase1_step_prog 0x80 off_single ++
  rlp_phase1_step_prog 0xB8 off_short_str ++
  rlp_phase1_step_prog 0xC0 off_long_str ++
  rlp_phase1_step_prog 0xF8 off_short_list

example (a b c d : BitVec 13) :
    (rlp_phase1_classifier_prog a b c d).length = 8 := rfl

-- ============================================================================
-- CodeReq for the cascade step
-- ============================================================================

/-- Code requirement for a single cascade step, as `ofProg`. -/
abbrev rlp_phase1_step_code
    (k : BitVec 12) (offset : BitVec 13) (base : Word) : CodeReq :=
  CodeReq.ofProg base (rlp_phase1_step_prog k offset)

-- ============================================================================
-- Spec: cascade step
-- ============================================================================

/-- `cpsBranch` spec for one cascade step.

    Taken (`x5 <u k_val`):     PC := target           (BLTU took the branch)
    Not taken (`¬ x5 <u k_val`): PC := base + 8       (fell through)

    Both postconditions preserve `⌜…⌝` so downstream compositions can case
    on the dispatch result. `k_val = (0 : Word) + signExtend12 k` matches
    the result of `ADDI x10, x0, k` starting from `x0 = 0`. For the RLP
    thresholds (0x80, 0xB8, 0xC0, 0xF8), `k_val.toNat = k.toNat` since all
    four fit in 11 bits (no sign extension). -/
theorem rlp_phase1_step_spec (v5 v10 : Word)
    (k : BitVec 12) (offset : BitVec 13) (base target : Word)
    (htarget : (base + 4) + signExtend13 offset = target) :
    let k_val := (0 : Word) + signExtend12 k
    let code := rlp_phase1_step_code k offset base
    cpsBranch base code
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      target
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) **
         ⌜BitVec.ult v5 k_val⌝)
      (base + 8)
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ k_val) **
         ⌜¬ BitVec.ult v5 k_val⌝) := by
  have ha1 : (base + 4 : Word) + 4 = base + 8 := by bv_omega
  have hd : CodeReq.Disjoint
      (CodeReq.singleton base (.ADDI .x10 .x0 k))
      (CodeReq.singleton (base + 4) (.BLTU .x5 .x10 offset)) :=
    CodeReq.Disjoint.singleton (by bv_omega) _ _
  -- Step 1: ADDI x10, x0, k at base
  have s1 := addi_spec_gen .x10 .x0 v10 0 k base (by nofun)
  have s1' : cpsTriple base (base + 4) (CodeReq.singleton base (.ADDI .x10 .x0 k))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ v10))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 k))) :=
    cpsTriple_consequence _ _ _ _ _ _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsTriple_frame_left _ _ _ _ _ (.x5 ↦ᵣ v5) (by pcFree) s1)
  -- Step 2: BLTU x5, x10, offset at base+4
  have s2_raw := bltu_spec_gen .x5 .x10 offset v5
    ((0 : Word) + signExtend12 k) (base + 4)
  rw [htarget, ha1] at s2_raw
  -- Frame with x0, rearrange pre/post
  have s2' : cpsBranch (base + 4)
      (CodeReq.singleton (base + 4) (.BLTU .x5 .x10 offset))
      ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)))
      target
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) **
         ⌜BitVec.ult v5 ((0 : Word) + signExtend12 k)⌝)
      (base + 8)
        ((.x5 ↦ᵣ v5) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x10 ↦ᵣ ((0 : Word) + signExtend12 k)) **
         ⌜¬ BitVec.ult v5 ((0 : Word) + signExtend12 k)⌝) :=
    cpsBranch_consequence _ _ _ _
      target _ _ (base + 8) _ _
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by xperm_hyp hp)
      (cpsBranch_frame_left _ _ _ _ _ _ _ (.x0 ↦ᵣ (0 : Word)) (by pcFree) s2_raw)
  exact cpsTriple_seq_cpsBranch_with_perm _ _ _ _ hd _ _ _ target _ (base + 8) _
    (fun _ hp => hp) s1' s2'

end EvmAsm.Rv64.RLP
