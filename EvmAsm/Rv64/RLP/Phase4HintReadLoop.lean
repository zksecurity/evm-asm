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

end EvmAsm.Rv64.RLP
