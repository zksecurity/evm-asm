/-
  EvmAsm.Rv64.RLP.Phase4HintLen

  Phase 4 wrappers for the RLP decoder: read private-input metadata.

  This file contains two wrapper families:
  - `rlp_phase4_hint_len_*`   — legacy SP1 HINT_LEN (t0=0xF0); DEPRECATED.
  - `rlp_phase4_read_input_*` — zkvm-standards `read_input` (t0=0xF2);
                                 the migration target from bead evm-asm-lvqji.

  Migration status: new `read_input` wrappers are added alongside the
  deprecated HINT_LEN wrappers.  Slice 4 (`evm-asm-roj93`) retires HINT_LEN
  once the RLP pipeline has fully migrated.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Rv64.HintSpecs
import EvmAsm.Rv64.AddrNorm
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Rv64.RLP

open EvmAsm.Rv64.Tactics

/-- HINT_LEN wrapper: `x5` is overwritten with the SP1 HINT_LEN selector and
    the private-input byte length is returned in `x10`.

    @[deprecated] Use `rlp_phase4_read_input_len_prog` (read_input, t0=0xF2) instead. -/
def rlp_phase4_hint_len_prog : Program :=
  [.LI .x5 (BitVec.ofNat 64 0xF0), .ECALL]

theorem rlp_phase4_hint_len_code_eq_ofProg (base : Word) :
    CodeReq.ofProg base rlp_phase4_hint_len_prog =
      (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF0))).union
        (CodeReq.singleton (base + 4) .ECALL) := by
  simp only [rlp_phase4_hint_len_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

/-- Executable Phase 4 HINT_LEN wrapper spec. The wrapper sets the selector
    register and then invokes ECALL; the postcondition exposes the current
    private-input length in `x10`. -/
theorem rlp_phase4_hint_len_spec_within
    (input : List (BitVec 8)) (base : Word) :
    cpsTripleWithin 2 base (base + 8)
      (CodeReq.ofProg base rlp_phase4_hint_len_prog)
      ((base + 4 ↦ᵢ .ECALL) ** regOwn .x5 ** regOwn .x10 **
        privateInputIs input)
      ((base + 4 ↦ᵢ .ECALL) ** (.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
  rw [rlp_phase4_hint_len_code_eq_ofProg]
  let cr := (CodeReq.singleton base (.LI .x5 (BitVec.ofNat 64 0xF0))).union
    (CodeReq.singleton (base + 4) .ECALL)
  have hli := li_spec_gen_own_within .x5 (BitVec.ofNat 64 0xF0) base (by nofun)
  have hli_ext : cpsTripleWithin 1 base (base + 4) cr
      (regOwn .x5)
      (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · exact CodeReq.union_mono_left
    · exact hli
  have hli_framed := cpsTripleWithin_frameR
    ((base + 4 ↦ᵢ .ECALL) ** regOwn .x10 ** privateInputIs input)
    (by pcFree) hli_ext
  have hlen := ecall_hint_len_spec_gen_own_within input (base + 4)
  have hlen_at_exit : cpsTripleWithin 1 (base + 4) (base + 8)
      (CodeReq.singleton (base + 4) .ECALL)
      (((base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) **
        privateInputIs input) ** regOwn .x10)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (base + 4 ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
    have h_exit : (base + 4 : Word) + 4 = base + 8 := by bv_omega
    simpa only [h_exit] using hlen
  have hlen_ext : cpsTripleWithin 1 (base + 4) (base + 8) cr
      (((base + 4 ↦ᵢ .ECALL) ** (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) **
        privateInputIs input) ** regOwn .x10)
      ((.x10 ↦ᵣ (BitVec.ofNat 64 input.length)) ** (base + 4 ↦ᵢ .ECALL) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF0)) ** privateInputIs input) := by
    apply cpsTripleWithin_extend_code (cr' := cr)
    · apply CodeReq.singleton_mono
      apply CodeReq.union_skip
      · exact CodeReq.singleton_miss (a := base) (a' := base + 4)
          (i := .LI .x5 (BitVec.ofNat 64 0xF0)) (by bv_omega)
      · exact CodeReq.singleton_get (base + 4) .ECALL
    · exact hlen_at_exit
  have hseq := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp)
    hli_framed hlen_ext
  simpa only [Nat.reduceAdd, sepConj_assoc', sepConj_comm', sepConj_left_comm'] using hseq

-- ============================================================================
-- read_input wrappers (zkvm-standards C ABI, t0 = 0xF2)
-- ============================================================================

/-- `read_input` Phase-4 program: ADDI+ADDI+LI+ECALL sequence that calls the
    zkvm-standards `read_input` (t0=0xF2), writing `inputBufBase` to
    `sp + ptr_ptr_off` and `privateInput.length` to `sp + size_ptr_off`.

    Parameters `ptr_ptr_off` / `size_ptr_off` are 12-bit signed SP-relative
    offsets for the two out-pointer cells allocated by the caller. -/
def rlp_phase4_read_input_len_prog
    (ptr_ptr_off size_ptr_off : BitVec 12) : Program :=
  [.ADDI .x10 .x12 ptr_ptr_off,
   .ADDI .x11 .x12 size_ptr_off,
   .LI   .x5  (BitVec.ofNat 64 0xF2),
   .ECALL]

theorem rlp_phase4_read_input_len_code_eq_ofProg
    (ptr_ptr_off size_ptr_off : BitVec 12) (base : Word) :
    CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off) =
      (CodeReq.singleton base (.ADDI .x10 .x12 ptr_ptr_off)).union
        ((CodeReq.singleton (base + 4) (.ADDI .x11 .x12 size_ptr_off)).union
          ((CodeReq.singleton (base + 4 + 4) (.LI .x5 (BitVec.ofNat 64 0xF2))).union
            (CodeReq.singleton (base + 4 + 4 + 4) .ECALL))) := by
  simp only [rlp_phase4_read_input_len_prog, CodeReq.ofProg_cons,
    CodeReq.ofProg_nil, CodeReq.union_empty_right]

theorem rlp_phase4_read_input_len_prog_length
    (ptr_ptr_off size_ptr_off : BitVec 12) :
    (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off).length = 4 := rfl

theorem rlp_phase4_read_input_len_prog_byte_length
    (ptr_ptr_off size_ptr_off : BitVec 12) :
    4 * (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off).length = 16 := rfl

/-- `read_input` Phase-4 spec: four-instruction wrapper that calls
    `read_input` (t0=0xF2) and writes (inputBufBase, privateInput.length)
    to the two SP-relative out-pointer cells.

    Pre:  x12 = sp (stack ptr); x10/x11/x5 caller-owned (any value);
          (sp + ptr_ptr_off) ↦ₘ old_ptr; (sp + size_ptr_off) ↦ₘ old_size;
          inputBufBaseIs buf_base; privateInputIs input.
    Post: (sp + ptr_ptr_off) ↦ₘ buf_base;
          (sp + size_ptr_off) ↦ₘ input.length;
          x10 = sp + ptr_ptr_off; x11 = sp + size_ptr_off; x5 = 0xF2;
          inputBufBaseIs and privateInputIs unchanged.
    Variant: takes specific initial register values for x10/x11/x5. -/
theorem rlp_phase4_read_input_len_spec_within_exact
    (ptr_ptr_off size_ptr_off : BitVec 12)
    (sp buf_base old_ptr old_size v10 v11 v5 : Word)
    (input : List (BitVec 8)) (base : Word)
    (hvalid_a0 : isValidDwordAccess (sp + signExtend12 ptr_ptr_off) = true)
    (hvalid_a1 : isValidDwordAccess (sp + signExtend12 size_ptr_off) = true) :
    cpsTripleWithin 4 base (base + 16)
      (CodeReq.ofProg base (rlp_phase4_read_input_len_prog ptr_ptr_off size_ptr_off))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) ** (.x5 ↦ᵣ v5) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ old_ptr) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ old_size) **
        inputBufBaseIs buf_base ** privateInputIs input)
      ((.x12 ↦ᵣ sp) **
        (.x10 ↦ᵣ sp + signExtend12 ptr_ptr_off) **
        (.x11 ↦ᵣ sp + signExtend12 size_ptr_off) **
        (.x5 ↦ᵣ (BitVec.ofNat 64 0xF2)) **
        (base + 12 ↦ᵢ .ECALL) **
        ((sp + signExtend12 ptr_ptr_off) ↦ₘ buf_base) **
        ((sp + signExtend12 size_ptr_off) ↦ₘ (BitVec.ofNat 64 input.length)) **
        inputBufBaseIs buf_base ** privateInputIs input) := by
  rw [rlp_phase4_read_input_len_code_eq_ofProg]
  have haddi1 := addi_spec_gen_within .x10 .x12 v10 sp ptr_ptr_off base (by nofun)
  have haddi2 := addi_spec_gen_within .x11 .x12 v11 sp size_ptr_off (base + 4) (by nofun)
  have hli3 := li_spec_gen_within .x5 v5 (BitVec.ofNat 64 0xF2) (base + 8) (by nofun)
  have hecall_base := ecall_read_input_spec_gen_within buf_base old_ptr old_size
    (sp + signExtend12 ptr_ptr_off) (sp + signExtend12 size_ptr_off)
    input (base + 4 + 4 + 4) hvalid_a0 hvalid_a1
  have hecall := cpsTripleWithin_frameR ((.x12 ↦ᵣ sp)) (by pcFree) hecall_base
  runBlock haddi1 haddi2 hli3 hecall


end EvmAsm.Rv64.RLP
