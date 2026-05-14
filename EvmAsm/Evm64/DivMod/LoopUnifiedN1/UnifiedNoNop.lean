import EvmAsm.Evm64.DivMod.LoopUnifiedN1.CallIter210NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- No-NOP variant of `divK_loop_n1_unified_spec_within`. -/
theorem divK_loop_n1_unified_spec_within_noNop (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : bltu_3 = BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1 bltu_3 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 808 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost bltu_3 bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  cases bltu_3 <;> simp only [iterN1_true, iterN1_false] at hbltu_2 hbltu_1 hbltu_0
  · -- bltu_3 = false -> max
    have hbltu_3' : ¬BitVec.ult u1 v0 := by
      rw [show BitVec.ult u1 v0 = false from hbltu_3.symm]; decide
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_n1_max_iter210_spec_within_noNop bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base halign
      hbltu_3' hbltu_2 hbltu_1 hbltu_0 hcarry2
  · -- bltu_3 = true -> call
    have hbltu_3' : BitVec.ult u1 v0 := hbltu_3.symm ▸ rfl
    exact divK_loop_n1_call_iter210_spec_within_noNop bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old
      retMem dMem dloMem scratch_un0 base
      halign
      hbltu_3' hbltu_2 hbltu_1 hbltu_0 hcarry2

end EvmAsm.Evm64
