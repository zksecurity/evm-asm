/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step2

  Full-step composition for instrs [30]-[46] of the `div128` subroutine —
  combining step-2-init (DIVU+MUL+SUB), clamp-q0 (SRLI+BEQ+ADDI+ADD),
  Phase 2b guard (SRLI+BNE — Knuth TAOCP §4.3.1 Step D3), and prodcheck2
  (LD+MUL+SLLI+LD+OR + BLTU+JAL + ADDI) into a single refined `q0`
  computation for the low 64 bits.

  Thirtieth chunk of the `LimbSpec.lean` split tracked by issue #312.
  The consumer surface is unchanged: `LimbSpec.lean` re-exports this file
  so every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Clamp
import EvmAsm.Evm64.DivMod.LimbSpec.Div128ProdCheck2
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Tail
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- div128 step 2: trial division q0, clamp, Phase 2b guard, product check.
    Instrs [30]-[46] (17 instructions). Includes the Knuth TAOCP §4.3.1
    Step D3 guard (SRLI + BNE at instrs [37]-[38]) that skips the
    product check when `rhat2c >= 2^32`.

    Input: un21 in x7, dHi in x6, dlo/un0 in memory.
    Output: refined q0 in x5 (= `div128Quot_phase2b_q0' q0c rhat2c dlo un0`).

    **NOTE**: output's x7, x1, x11 values differ between guard-fires and
    guard-doesn't-fire paths:
    - Guard fires (rhat2c_hi ≠ 0): x7 = un21 (unchanged), x1 = rhat2c_hi,
      x11 = rhat2c.
    - Guard doesn't fire (rhat2c_hi = 0): x7 = q0Dlo, x1 = rhat2Un0,
      x11 = un0.

    The postcondition uses `rhat2c_hi = 0`-aware selectors to capture this. -/
theorem divK_div128_step2_spec
    (sp un21 dHi v1Old v5Old v11Old dlo un0 : Word) (base : Word) :
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi = 0 then rhat2 else rhat2 + dHi
    let q0Dlo := q0c * dlo
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
    let rhat2c_hi := rhat2c >>> (32 : BitVec 6).toNat
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dlo un0
    -- Exit values for registers that differ between guard-fires/doesn't
    -- paths. On guard-fires: x7 keeps un21 (MUL not run), x1 keeps
    -- rhat2c_hi (loaded by SRLI), x11 keeps rhat2c (un0 not loaded).
    -- On guard-doesn't-fire: x7 holds q0Dlo, x1 holds rhat2Un0, x11 holds un0.
    let x7_exit := if rhat2c_hi = 0 then q0Dlo else un21
    let x1_exit := if rhat2c_hi = 0 then rhat2Un0 else rhat2c_hi
    let x11_exit := if rhat2c_hi = 0 then un0 else rhat2c
    let cr :=
      CodeReq.union (CodeReq.singleton base (.DIVU .x5 .x7 .x6))
      (CodeReq.union (CodeReq.singleton (base + 4) (.MUL .x1 .x5 .x6))
      (CodeReq.union (CodeReq.singleton (base + 8) (.SUB .x11 .x7 .x1))
      (CodeReq.union (CodeReq.singleton (base + 12) (.SRLI .x1 .x5 32))
      (CodeReq.union (CodeReq.singleton (base + 16) (.BEQ .x1 .x0 12))
      (CodeReq.union (CodeReq.singleton (base + 20) (.ADDI .x5 .x5 4095))
      (CodeReq.union (CodeReq.singleton (base + 24) (.ADD .x11 .x11 .x6))
      (CodeReq.union (CodeReq.singleton (base + 28) (.SRLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 32) (.BNE .x1 .x0 36))
      (CodeReq.union (CodeReq.singleton (base + 36) (.LD .x1 .x12 3952))
      (CodeReq.union (CodeReq.singleton (base + 40) (.MUL .x7 .x5 .x1))
      (CodeReq.union (CodeReq.singleton (base + 44) (.SLLI .x1 .x11 32))
      (CodeReq.union (CodeReq.singleton (base + 48) (.LD .x11 .x12 3944))
      (CodeReq.union (CodeReq.singleton (base + 52) (.OR .x1 .x1 .x11))
      (CodeReq.union (CodeReq.singleton (base + 56) (.BLTU .x1 .x7 8))
      (CodeReq.union (CodeReq.singleton (base + 60) (.JAL .x0 8))
       (CodeReq.singleton (base + 64) (.ADDI .x5 .x5 4095)))))))))))))))))
    cpsTriple base (base + 68) cr
      ((.x7 ↦ᵣ un21) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ v5Old) **
       (.x1 ↦ᵣ v1Old) ** (.x11 ↦ᵣ v11Old) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0))
      ((.x7 ↦ᵣ x7_exit) ** (.x6 ↦ᵣ dHi) ** (.x5 ↦ᵣ q0') **
       (.x1 ↦ᵣ x1_exit) ** (.x11 ↦ᵣ x11_exit) **
       (.x12 ↦ᵣ sp) ** (.x0 ↦ᵣ 0) **
       (sp + signExtend12 3952 ↦ₘ dlo) ** (sp + signExtend12 3944 ↦ₘ un0)) := by
  intro q0 rhat2 hi q0c rhat2c q0Dlo rhat2Un0 rhat2c_hi q0' x7_exit x1_exit x11_exit cr
  -- TODO(#61 Phase 2b coordinated fix): compose step2_init + clamp_q0 +
  -- phase2b_guard (cpsBranch) + prodcheck2_merged (on fall-through), then
  -- merge via cpsBranch_merge_same_cr into this unified cpsTriple. The
  -- `div128Quot_phase2b_q0'` helper now guards the mul-check with
  -- `rhat2c >>> 32 = 0`, so under the guard-fires leg, `q0' = q0c`; under
  -- the guard-doesn't-fire leg, `q0' = (if BitVec.ult rhat2Un0 q0Dlo then
  -- q0c + signExtend12 4095 else q0c)` matching the unguarded
  -- `divK_div128_prodcheck2_merged_spec` post.
  sorry

end EvmAsm.Evm64
