import EvmAsm.Evm64.DivMod.LoopUnifiedN1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_3)

/-- No-NOP variant of `divK_loop_n1_call_iter210_spec_within`. -/
theorem divK_loop_n1_call_iter210_spec_within_noNop (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 808 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN1PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0)
      (loopN1UnifiedPost true bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  let r3 := iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=3 call spec (includes scratch)
  have J3 := divK_loop_body_n1_call_unified_j3_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old retMem dMem dloMem scratch_un0 base halign
    hbltu_3
    (hcarry2 (div128Quot u1 u0 v0) u0 u1 u2 u3 uTop : isAddbackCarry2NzN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop)
  intro_lets at J3
  -- Frame j=3 with iter210 extra atoms only (scratch consumed by call)
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J3
  -- iter210 unified spec (inputs from j=3 call output, scratch = j=3 call values)
  have H210 := divK_loop_n1_iter210_unified_spec_within_noNop bltu_2 bltu_1 bltu_0
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2)
    r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3
    u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    (base + div128CallRetOff) v0 (div128DLo v0) (div128Un0 u0) base halign
    hbltu_2 hbltu_1 hbltu_0 hcarry2
  -- Frame iter210 with j=3 carried atoms
  have H210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) H210
  -- Compose j=3 and iter210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1Call loopExitPostN1 loopExitPost at hp
      delta loopN1Iter210PreWithScratch loopN1Iter210Pre at ⊢
      simp only [] at hp ⊢
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f H210f
  exact cpsTripleWithin_weaken
    (fun h hp => by delta loopN1PreWithScratch loopN1Pre at hp; xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPost loopN1Iter210Post loopN1Iter10Post loopIterPostN1 at hp ⊢
      simp only [iterN1_true, ite_true, sepConj_emp_right'] at hp ⊢
      have hr3 : r3 = iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop := rfl
      have hub3 : u_base_3 = sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      have hqa3 : q_addr_3 = sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat := rfl
      simp only [hr3, hub3, hqa3] at hp
      rw [sepConj_assoc'] at hp
      cases bltu_2 <;> cases bltu_1 <;> cases bltu_0 <;> xperm_hyp hp)
    full

/-- No-NOP N1 call path wrapper with the loop scratch precondition split so
    callers can keep exact `x1` ownership outside the loop precondition. -/
theorem divK_loop_n1_call_iter210_spec_within_noNop_noX1_pre (bltu_2 bltu_1 bltu_0 : Bool)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop
     u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : bltu_2 = BitVec.ult (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : bltu_1 = BitVec.ult (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hbltu_0 : bltu_0 = BitVec.ult (iterN1 bltu_1 v0 v1 v2 v3 u0_orig_1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1 bltu_2 v0 v1 v2 v3 u0_orig_2
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1).2.1 v0)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 808 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN1PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 q3Old q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 ** regOwn .x1)
      (loopN1UnifiedPost true bltu_2 bltu_1 bltu_0 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 retMem dMem dloMem scratch_un0) := by
  exact cpsTripleWithin_weaken
    (loopN1PreWithScratchNoX1_to_loopN1PreWithScratch
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0)
    (fun h hp => hp)
    (divK_loop_n1_call_iter210_spec_within_noNop bltu_2 bltu_1 bltu_0
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0_orig_2 u0_orig_1 u0_orig_0
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0
      base halign hbltu_3 hbltu_2 hbltu_1 hbltu_0 hcarry2)

end EvmAsm.Evm64
