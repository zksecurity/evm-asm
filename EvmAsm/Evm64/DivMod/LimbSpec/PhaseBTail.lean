/-
  EvmAsm.Evm64.DivMod.LimbSpec.PhaseBTail

  CPS spec for the Knuth Algorithm D "phase B tail":
    * `divK_phaseB_tail_code` / `divK_phaseB_tail_spec` — 5-instruction
      block (SD n, ADDI n-1, SLLI ×8, ADD sp + offset, LD b[n-1]) that
      stores `n` to scratch and loads the leading limb of the divisor.

  Tenth chunk of the `LimbSpec.lean` split tracked by issue #312. The
  consumer surface is unchanged: `LimbSpec.lean` re-exports this file so
  every existing `import EvmAsm.Evm64.DivMod.LimbSpec` still sees the
  spec.
-/

import EvmAsm.Evm64.DivMod.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.ControlFlow
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

abbrev divK_phaseB_tail_code (base : Word) : CodeReq :=
  CodeReq.ofProg base (divK_phaseB.drop 16)

/-- Phase B tail: store n to scratch, compute sp + (n-1)*8, load b[n-1].
    x5 = n on entry. On exit, x5 = leading limb b[n-1].

    The leading-limb address `sp + (n-1)*8 + 32` is written inline in the
    pre and post — callers already rewrite it to the concrete slot per
    `n` via simp, so hoisting it into a `let` just added a leading
    `intro` and made the statement less direct. -/
theorem divK_phaseB_tail_spec (sp n leading_limb nMem : Word) (base : Word) :
    cpsTriple base (base + 20) (divK_phaseB_tail_code base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ leading_limb) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat + signExtend12 32) ↦ₘ leading_limb)) := by
  have I0 := sd_spec_gen .x12 .x5 sp n nMem 3984 base
  have I1 := addi_spec_gen_same .x5 n 4095 (base + 4) (by nofun)
  have I2 := slli_spec_gen_same .x5 (n + signExtend12 4095) 3 (base + 8) (by nofun)
  have I3 := add_spec_gen_rd_eq_rs2 .x5 .x12 sp
    ((n + signExtend12 4095) <<< (3 : BitVec 6).toNat) (base + 12) (by nofun)
  have I4 := ld_spec_gen_same .x5
    (sp + (n + signExtend12 4095) <<< (3 : BitVec 6).toNat) leading_limb 32 (base + 16) (by nofun)
  runBlock I0 I1 I2 I3 I4

end EvmAsm.Evm64
