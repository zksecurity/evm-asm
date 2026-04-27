/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1b

  **STUB FILE** for issue #1337 algorithm fix migration.

  Provides the block spec for the **2nd D3 correction iteration** added
  by `divK_div128_v2` (in `EvmAsm/Evm64/DivMod/Program.lean`). This is
  the Phase 1b 2nd correction block — instructions [25..34] of the
  fixed `divK_div128_v2` subroutine (10 instructions: SRLI guard +
  BNE skip + 8-instruction D3 step mirroring `Div128ProdCheck1`).

  The block spec proves that under the precondition `q1c, rhatc` (post
  Phase 1a clamp + 1st D3 correction), the 10 instructions correctly
  compute Knuth's classical 2nd D3 correction:
  - if `rhatc < 2^32` (guard condition) AND
    `q1c * dLo > rhatc * 2^32 + un1` (product test),
    then q1' := q1c - 1, rhat' := rhatc + dHi.
  - otherwise q1' := q1c, rhat' := rhatc.

  **Status (2026-04-27)**: theorem signature only; proof is a sorry
  pending the multi-iteration migration. Mirrors the structure of
  `Div128ProdCheck1.divK_div128_prodcheck1_merged_spec` (the 1st D3
  block) and `Div128ProdCheck2.div128Quot_phase2b_q0'`
  (Phase 2b's guarded D3, structurally identical).

  Issue #1337's algorithm fix migration. Tracked in PR #1389.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck1
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se21_12)

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 product check 1b (Knuth classical 2nd D3 correction).
    Instrs [25]-[34] of `divK_div128_v2`. Both guard branches and both
    BLTU paths merge at `base + 40`.

    Layout:
    - [25] SRLI x1 x7 32       — rhat >> 32 (guard)
    - [26] BNE  x1 x0 36       — if rhat ≥ 2^32, skip → [35]
    - [27] LD   x1 x12 3952    — dLo (only if rhat < 2^32)
    - [28] MUL  x5 x10 x1      — q1 * dLo
    - [29] SLLI x1 x7 32       — rhat << 32
    - [30] OR   x1 x1 x11      — rhat*2^32 + un1
    - [31] BLTU x1 x5 8        — if rhs < lhs → correct [33]
    - [32] JAL  x0 12          — skip → [35]
    - [33] ADDI x10 x10 4095   — q1--
    - [34] ADD  x7 x7 x6       — rhat += dHi

    The guard at [25..26] mirrors Phase 2b's guard at
    `divK_div128.[37..38]`; the body at [27..34] mirrors the 1st D3
    block at `divK_div128.[17..24]` (= `divK_div128_prodcheck1_merged_spec`).

    **Output spec**: matches the Lean abstraction
    `div128Quot_v2`'s 2nd D3 step:
    ```
    let q1' := if rhatc < 2^32 ∧ rhatUn1' < q1c * dLo
               then q1c - 1 else q1c
    let rhat' := if rhatc < 2^32 ∧ rhatUn1' < q1c * dLo
                 then rhatc + dHi else rhatc
    ```

    **Status**: `sorry`. Proof is parallel to
    `divK_div128_prodcheck1_merged_spec` plus a guard-handling case
    split (~50 LOC additional, ~250 LOC total mirroring
    `Div128ProdCheck1.lean`).

    Issue #1337 algorithm fix migration. -/
theorem divK_div128_prodcheck1b_merged_spec
    (sp q1c rhatc dHi un1 v1Old v5Old dlo : Word) (base : Word) :
    let qDlo := q1c * dlo
    let rhatUn1' := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    -- Guard: 2nd D3 fires only if rhatc < 2^32.
    let guard_pass : Bool := (rhatc >>> (32 : BitVec 6).toNat) = (0 : Word)
    let q1' :=
      if guard_pass && BitVec.ult rhatUn1' qDlo
      then q1c + signExtend12 4095 else q1c
    let rhat' :=
      if guard_pass && BitVec.ult rhatUn1' qDlo
      then rhatc + dHi else rhatc
    let cr :=
      CodeReq.union (CodeReq.singleton base (.SRLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 4) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 8) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 12) (.MUL .x5 .x10 .x1))
      (CodeReq.union (CodeReq.singleton (base + 16) (.SLLI .x1 .x7 32))
      (CodeReq.union (CodeReq.singleton (base + 20) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 24) (.BLTU .x1 .x5 8))
      (CodeReq.union (CodeReq.singleton (base + 28) (.JAL .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 32) (.ADDI .x10 .x10 4095))
       (CodeReq.singleton (base + 36) (.ADD .x7 .x7 .x6))))))))))
    cpsTriple base (base + 40) cr
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1c) ** (.x7 ↦ᵣ rhatc) ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ v5Old) ** (.x1 ↦ᵣ v1Old) ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo))
      ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ q1') ** (.x7 ↦ᵣ rhat') ** (.x11 ↦ᵣ un1) **
       (.x5 ↦ᵣ qDlo) ** (.x1 ↦ᵣ rhatUn1') ** (.x6 ↦ᵣ dHi) **
       (sp + signExtend12 3952 ↦ₘ dlo)) := by
  sorry

end EvmAsm.Evm64
