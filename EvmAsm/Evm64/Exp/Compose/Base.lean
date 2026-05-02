/-
  EvmAsm.Evm64.Exp.Compose.Base

  Shared composition infrastructure for EXP: `expCode` (the union of all
  sub-block `CodeReq`s), subsumption helpers tying sub-block codes back to
  `expCode`, and shared length lemmas.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c). Concrete
  definitions will be added in the loop-composition slice (evm-asm-w5mk).
-/

import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Length of the EXP prologue block, restated in the composition namespace so
    future `skipBlock`-style subsumption proofs can use a compact simp set. -/
theorem exp_prologue_len : (EvmAsm.Evm64.exp_prologue).length = 6 := by
  exact EvmAsm.Evm64.exp_prologue_length

/-- Length of the EXP epilogue block, restated in the composition namespace. -/
theorem exp_epilogue_len : (EvmAsm.Evm64.exp_epilogue).length = 9 := by
  exact EvmAsm.Evm64.exp_epilogue_length

/-- First EXP composition code skeleton: the verified boundary blocks around
    the loop. The loop body and callable-multiply blocks will extend this
    union as their composed specs land. -/
abbrev expBoundaryCode (base : Word) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_prologue,
    CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue
  ]

theorem expBoundaryCode_prologue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (expBoundaryCode base) a = some i := by
  unfold expBoundaryCode
  simp only [CodeReq.unionAll_cons]
  exact CodeReq.union_mono_left

theorem expBoundaryCode_epilogue_sub {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + 24) EvmAsm.Evm64.exp_epilogue) a = some i →
      (expBoundaryCode base) a = some i := by
  unfold expBoundaryCode
  simp only [CodeReq.unionAll_cons]
  apply CodeReq.mono_union_right
    (CodeReq.ofProg_disjoint_range (fun k1 k2 hk1 hk2 => by
      simp only [exp_prologue_len, exp_epilogue_len] at hk1 hk2
      bv_omega))
  exact CodeReq.union_mono_left

end EvmAsm.Evm64.Exp.Compose
