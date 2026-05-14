/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4Shift0

  Full n=4 DIV path composition for the shift=0 case:
  pre-loop → loop body (j=0) → shift=0 epilogue.
  Composes base → base+1068 for the b[3]≠0, shift=0 case.

  When shift=0, normalization is identity (b'=b, u=a, u4=0).
  Since u4=0 < b3 (b3≠0), the BLTU condition is always taken → call path only.
  Two sub-cases: skip (borrow=0) and addback (borrow≠0).
-/

-- `FullPathN4Beq` transitively imports `FullPathN4`.
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Beq
import EvmAsm.Evm64.DivMod.Compose.FullPathN4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

-- ============================================================================
-- Address form helpers (duplicated from FullPathN4 where they are private)
-- ============================================================================

-- se12_32, se12_40, se12_48, se12_56, ult_zero_of_ne are in Base.lean

-- `x1_val_n4` now lives in `Compose/Base.lean` (shared with FullPathN4).

-- ============================================================================
-- Condition definitions for shift=0 call path
-- ============================================================================

/-- Skip addback condition at n=4 with shift=0 call path: borrow = 0. -/
def isSkipBorrowN4Shift0 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let qHat := div128Quot (0 : Word) a3 b3
  (if BitVec.ult (0 : Word) (mulsubN4_c3 qHat b0 b1 b2 b3 a0 a1 a2 a3)
   then (1 : Word) else 0) = (0 : Word)

-- ============================================================================
-- Postcondition definitions for preloop + loop body (shift=0)
-- ============================================================================

/-- Postcondition for pre-loop + call+skip loop body at n=4, shift=0.
    Uses unnormalized b[] and a[] directly (no shift). -/
@[irreducible]
def preloopShift0CallSkipPostN4 (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  loopBodyN4SkipPost sp (0 : Word) qHat b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word))


-- ============================================================================
-- Pre-loop + loop body (shift=0, call+skip): base → base+904
-- ============================================================================

/-- n=4 pre-loop + call+skip loop body: base → base+904 (shift = 0). -/
theorem evm_div_n4_preloop_shift0_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126) base (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopShift0CallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isSkipBorrowN4Shift0 at hborrow
  -- Pre-loop: base → base+448 (shift=0)
  have hPre := evm_div_n4_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z


  -- Frame preloop with x11, jMem, retMem, dMem, dloMem, scratch_un0
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- Loop body: base+448 → base+904, call+skip with v=b, u=a, uTop=0
  have hbltu : BitVec.ult (0 : Word) b3 := ult_zero_of_ne hb3nz
  have hLoop := divK_loop_body_n4_call_skip_j0_norm sp base
    jMem (4 : Word) ((clzResult b3).1) ((clzResult b3).2 >>> (63 : Nat)) b3
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 halign

    hbltu
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  -- Frame loop body with a[], q[1-3]=0, padding, shift=0
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop'
  -- Compose preloop → loop body
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopShift0CallSkipPostN4; simp only [hshift_z] at hq; xperm_hyp hq)
    hFull

/-- No-NOP variant of `evm_div_n4_preloop_shift0_call_skip_spec`. -/
theorem evm_div_n4_preloop_shift0_call_skip_spec_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126) base (base + denormOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopShift0CallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isSkipBorrowN4Shift0 at hborrow
  have hPre := evm_div_n4_shift0_to_loopSetup_spec_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  have hbltu : BitVec.ult (0 : Word) b3 := ult_zero_of_ne hb3nz
  have hLoop := divK_loop_body_n4_call_skip_j0_norm_noNop sp base
    jMem (4 : Word) ((clzResult b3).1) ((clzResult b3).2 >>> (63 : Nat)) b3
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 halign

    hbltu
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop'
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta preloopShift0CallSkipPostN4; simp only [hshift_z] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Unfold lemma for preloopShift0CallSkipPostN4
-- ============================================================================

/-- Unfold preloopShift0CallSkipPostN4 to expanded sp-relative form. -/
theorem preloopShift0CallSkipPostN4_unfold {sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    preloopShift0CallSkipPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3 =
    let qHat := div128Quot (0 : Word) a3 b3
    let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ ms.2.2.2.2) ** (.x11 ↦ᵣ qHat) **
     (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + signExtend12 4056) ↦ₘ ms.1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
     ((sp + 56) ↦ₘ b3) ** ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
     ((sp + signExtend12 4088) ↦ₘ qHat)) **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ b3) **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ div_un0) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 3992) ↦ₘ (0 : Word)) := by
  delta preloopShift0CallSkipPostN4
  simp only [loopBodyN4SkipPost, loopBodySkipPost, loopExitPostN4_j0_eq, se12_32, se12_40, se12_48, se12_56]

-- ============================================================================
-- Full path postcondition for n=4 DIV (shift=0, call+skip)
-- ============================================================================

/-- Full path postcondition for n=4 DIV (shift=0, call+skip).
    No denormalization needed since shift=0. -/
@[irreducible]
def fullDivN4Shift0CallSkipPost (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ qHat) **
  (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ ms.2.2.2.1) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ qHat) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ qHat) ** ((sp + 40) ↦ₘ (0 : Word)) **
  ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ ms.1) **
  ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
  ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
  ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
  ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
  (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)

-- ============================================================================
-- Full n=4 DIV path (shift=0, call+skip): base → base+1068
-- ============================================================================

/-- Full n=4 DIV path: base → base+1068 (shift=0, call+skip).
    Composes pre-loop + loop body + shift=0 epilogue. -/
theorem evm_div_n4_full_shift0_call_skip_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12) base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN4Shift0CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  -- 1. Pre-loop + loop body: base → base+904
  have hA := evm_div_n4_preloop_shift0_call_skip_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  -- 2. Post-loop: base+904 → base+1068 (shift=0 epilogue)
  have hB := evm_div_shift0_epilogue_spec_within sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (0 : Word)
    ms.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    ms.2.2.2.2
    qHat 0 0 0
    b0 b1 b2 b3
    rfl
  -- Frame post-loop with remaining atoms
  have hBF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ ms.1) **
     ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
     ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
     ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3) **
     (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
     (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopShift0CallSkipPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN4Shift0CallSkipPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

/-- No-NOP variant of `evm_div_n4_full_shift0_call_skip_spec`. -/
theorem evm_div_n4_full_shift0_call_skip_spec_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hborrow : isSkipBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 126 + 12) base (base + nopOff) (divCode_noNop base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN4Shift0CallSkipPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  have hA := evm_div_n4_preloop_shift0_call_skip_spec_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hborrow
  have hB := evm_div_shift0_epilogue_spec_within_noNop sp base
    ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (0 : Word)
    ms.2.2.2.1 (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    ms.2.2.2.2
    qHat 0 0 0
    b0 b1 b2 b3
    rfl
  have hBF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ ms.1) **
     ((sp + signExtend12 4048) ↦ₘ ms.2.1) **
     ((sp + signExtend12 4040) ↦ₘ ms.2.2.1) **
     ((sp + signExtend12 4032) ↦ₘ ms.2.2.2.1) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word) - ms.2.2.2.2) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ qHat) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3) **
     (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
     (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    (by pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopShift0CallSkipPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN4Shift0CallSkipPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

-- ============================================================================
-- Condition definitions for shift=0 call+addback (BEQ) path
-- ============================================================================

/-- Addback condition at n=4 with shift=0 call path: borrow ≠ 0. Mulsub
    with trial quotient `div128Quot 0 a3 b3` underflows, so the algorithm
    decrements the trial quotient and adds back `b` to the partial remainder. -/
def isAddbackBorrowN4Shift0 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let qHat := div128Quot (0 : Word) a3 b3
  (if BitVec.ult (0 : Word) (mulsubN4_c3 qHat b0 b1 b2 b3 a0 a1 a2 a3)
   then (1 : Word) else 0) ≠ (0 : Word)

/-- Double-addback carry2 ≠ 0 condition at n=4 shift=0 call path (expressed
    over raw a/b). Shift=0 specialization of `isAddbackCarry2NzN4CallAb`:
    v=b, u=a, uTop=0 (no normalization). -/
def isAddbackCarry2NzN4Shift0 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isAddbackCarry2NzN4Call b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word)

-- ============================================================================
-- Postcondition for preloop + call+addback BEQ loop body (shift=0)
-- ============================================================================

/-- Postcondition for pre-loop + call+addback BEQ loop body at n=4, shift=0.
    Uses unnormalized b[] and a[] directly (no shift) with uTop=0. Mirror
    of `preloopShift0CallSkipPostN4` but with `loopBodyN4AddbackBeqPost`
    replacing `loopBodyN4SkipPost`. -/
@[irreducible]
def preloopShift0CallAddbackBeqPostN4
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let div_un0 := (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  loopBodyN4AddbackBeqPost sp (0 : Word) qHat b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word))

-- ============================================================================
-- Pre-loop + loop body (shift=0, call+addback BEQ): base → base+denormOff
-- ============================================================================

/-- n=4 pre-loop + call+addback BEQ loop body: base → base+denormOff (shift = 0).
    Mirror of `evm_div_n4_preloop_shift0_call_skip_spec` with the call+skip
    loop body replaced by call+addback (BEQ double-addback) variant.

    At runtime the shift=0 path sets uTop=0 and passes raw b, a to the loop
    body — see the call to `divK_loop_body_n4_call_addback_j0_beq_norm` below. -/
theorem evm_div_n4_preloop_shift0_call_addback_beq_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202) base (base + denormOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (preloopShift0CallAddbackBeqPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  unfold isAddbackBorrowN4Shift0 at hborrow
  unfold isAddbackCarry2NzN4Shift0 at hcarry2_nz
  -- Pre-loop: base → base+loopBodyOff (shift=0)
  have hPre := evm_div_n4_shift0_to_loopSetup_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    hbnz hb3nz hshift_z
  -- Frame preloop with x11, jMem, retMem, dMem, dloMem, scratch_un0
  have hPreF := cpsTripleWithin_frameR
    ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
     (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
    (by pcFree) hPre
  -- Loop body: base+loopBodyOff → base+denormOff, call+addback BEQ with v=b, u=a, uTop=0
  have hbltu : BitVec.ult (0 : Word) b3 := ult_zero_of_ne hb3nz
  have hLoop := divK_loop_body_n4_call_addback_j0_beq_norm sp base
    jMem (4 : Word) ((clzResult b3).1) ((clzResult b3).2 >>> (63 : Nat)) b3
    v11Old (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
    b0 b1 b2 b3 a0 a1 a2 a3 (0 : Word) (0 : Word)
    retMem dMem dloMem scratch_un0 halign
    hbltu hcarry2_nz
  intro_lets at hLoop
  have hLoop' := hLoop hborrow
  -- Frame loop body with a[], q[1-3]=0, padding, shift=0
  have hLoopF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ (clzResult b3).1))
    (by pcFree) hLoop'
  -- Compose preloop → loop body
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [x1_val_n4] at hp
      xperm_hyp hp) hPreF hLoopF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by
      delta preloopShift0CallAddbackBeqPostN4
      simp only [hshift_z] at hq
      xperm_hyp hq)
    hFull

-- ============================================================================
-- Unfold lemma for preloopShift0CallAddbackBeqPostN4
-- ============================================================================

/-- Unfold `preloopShift0CallAddbackBeqPostN4` to expanded sp-relative form.
    Mirror of `preloopCallAddbackBeqPostN4_unfold` for the shift=0 case
    (raw a/b/u, uTop=0). -/
theorem preloopShift0CallAddbackBeqPostN4_unfold
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    preloopShift0CallAddbackBeqPostN4 sp base a0 a1 a2 a3 b0 b1 b2 b3 =
    let qHat := div128Quot (0 : Word) a3 b3
    let dLo := (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un0 := (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
    let c3 := ms.2.2.2.2
    let u4_new := (0 : Word) - c3
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
    let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
    let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
                 else qHat + signExtend12 4095
    let un0Out := if carry = 0 then ab'.1 else ab.1
    let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
    let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
    let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
    let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
    ((.x12 ↦ᵣ sp) ** (.x1 ↦ᵣ signExtend12 4095) **
     (.x5 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ sp + signExtend12 4056) **
     (.x7 ↦ᵣ sp + signExtend12 4088) ** (.x10 ↦ᵣ c3) ** (.x11 ↦ᵣ q_out) **
     (.x2 ↦ᵣ un3Out) ** (.x0 ↦ᵣ (0 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + signExtend12 4056) ↦ₘ un0Out) **
     ((sp + 40) ↦ₘ b1) ** ((sp + signExtend12 4048) ↦ₘ un1Out) **
     ((sp + 48) ↦ₘ b2) ** ((sp + signExtend12 4040) ↦ₘ un2Out) **
     ((sp + 56) ↦ₘ b3) ** ((sp + signExtend12 4032) ↦ₘ un3Out) **
     ((sp + signExtend12 4024) ↦ₘ u4_out) **
     ((sp + signExtend12 4088) ↦ₘ q_out)) **
    (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
    (sp + signExtend12 3960 ↦ₘ b3) **
    (sp + signExtend12 3952 ↦ₘ dLo) **
    (sp + signExtend12 3944 ↦ₘ div_un0) **
    ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
    ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
    ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
    ((sp + signExtend12 3992) ↦ₘ (0 : Word)) := by
  delta preloopShift0CallAddbackBeqPostN4 loopBodyN4AddbackBeqPost loopBodyAddbackBeqPost
  simp only [loopExitPostN4_j0_eq, se12_32, se12_40, se12_48, se12_56]

-- ============================================================================
-- Full path postcondition for n=4 DIV (shift=0, call+addback BEQ)
-- ============================================================================

/-- Full path postcondition for n=4 DIV (shift=0, call+addback BEQ).
    Mirror of `fullDivN4CallAddbackBeqPost` specialized to shift=0 (no
    denormalization step; raw a/b/u limbs, uTop=0). -/
@[irreducible]
def fullDivN4Shift0CallAddbackBeqPost
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let u4_new := (0 : Word) - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  (.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q_out) **
  (.x6 ↦ᵣ (0 : Word)) ** (.x7 ↦ᵣ (0 : Word)) **
  (.x2 ↦ᵣ un3Out) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ (0 : Word)) **
  ((sp + signExtend12 3992) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4088) ↦ₘ q_out) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
  ((sp + 32) ↦ₘ q_out) ** ((sp + 40) ↦ₘ (0 : Word)) **
  ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
  ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 4056) ↦ₘ un0Out) **
  ((sp + signExtend12 4048) ↦ₘ un1Out) **
  ((sp + signExtend12 4040) ↦ₘ un2Out) **
  ((sp + signExtend12 4032) ↦ₘ un3Out) **
  ((sp + signExtend12 4024) ↦ₘ u4_out) **
  ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
  (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
  (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
  (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ b3) **
  (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
  (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat)

/-- `fullDivN4Shift0CallAddbackBeqPost` is pc-free. -/
theorem pcFree_fullDivN4Shift0CallAddbackBeqPost
    {sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word} :
    (fullDivN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3).pcFree := by
  delta fullDivN4Shift0CallAddbackBeqPost
  pcFree

instance pcFreeInst_fullDivN4Shift0CallAddbackBeqPost
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    Assertion.PCFree (fullDivN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3) :=
  ⟨pcFree_fullDivN4Shift0CallAddbackBeqPost⟩

-- ============================================================================
-- Full n=4 DIV path (shift=0, call+addback BEQ): base → base+nopOff
-- ============================================================================

/-- Full n=4 DIV path: base → base+nopOff (shift=0, call+addback BEQ).
    Composes pre-loop + call+addback BEQ loop body + shift=0 DIV epilogue.
    Mirror of `evm_div_n4_full_shift0_call_skip_spec` for the addback
    branch, and of `evm_div_n4_full_call_addback_beq_spec` for the
    shift=0 specialization. -/
theorem evm_div_n4_full_shift0_call_addback_beq_spec (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_z : (clzResult b3).1 = 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hcarry2_nz : isAddbackCarry2NzN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrow : isAddbackBorrowN4Shift0 a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 9 + 4 + 202 + 12) base (base + nopOff) (divCode base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b3).2 >>> (63 : Nat)) **
       (.x1 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) ** (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
       (sp + signExtend12 3968 ↦ₘ retMem) ** (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) ** (sp + signExtend12 3944 ↦ₘ scratch_un0))
      (fullDivN4Shift0CallAddbackBeqPost sp base a0 a1 a2 a3 b0 b1 b2 b3) := by
  let qHat := div128Quot (0 : Word) a3 b3
  let ms := mulsubN4 qHat b0 b1 b2 b3 a0 a1 a2 a3
  let c3 := ms.2.2.2.2
  let u4_new := (0 : Word) - c3
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 u4_new b0 b1 b2 b3
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 ab.2.2.2.2 b0 b1 b2 b3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0 b1 b2 b3
  let q_out := if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
               else qHat + signExtend12 4095
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u4_out  := if carry = 0 then ab'.2.2.2.2 else ab.2.2.2.2
  -- 1. Pre-loop + loop body: base → base+denormOff
  have hA := evm_div_n4_preloop_shift0_call_addback_beq_spec sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0
    hbnz hb3nz hshift_z halign hcarry2_nz hborrow
  -- 2. Post-loop: base+denormOff → base+nopOff (shift=0 DIV epilogue)
  have hB := evm_div_shift0_epilogue_spec_within sp base
    un0Out un1Out un2Out un3Out (0 : Word)
    un3Out (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    c3 q_out 0 0 0
    b0 b1 b2 b3
    rfl
  -- Frame post-loop with remaining atoms (u0..u3 slots are NOT in the
  -- epilogue's pre since shift=0 skips the denorm step; they stay in the frame)
  have hBF := cpsTripleWithin_frameR
    (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ un0Out) **
     ((sp + signExtend12 4048) ↦ₘ un1Out) **
     ((sp + signExtend12 4040) ↦ₘ un2Out) **
     ((sp + signExtend12 4032) ↦ₘ un3Out) **
     ((sp + signExtend12 4024) ↦ₘ u4_out) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
     (sp + signExtend12 3976 ↦ₘ (0 : Word)) **
     (.x1 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ q_out) **
     (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
     (sp + signExtend12 3960 ↦ₘ b3) **
     (sp + signExtend12 3952 ↦ₘ (b3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat) **
     (sp + signExtend12 3944 ↦ₘ (a3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat))
    (by pcFree) hB
  -- 3. Compose A + B
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      simp only [preloopShift0CallAddbackBeqPostN4_unfold] at hp
      xperm_hyp hp) hA hBF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta fullDivN4Shift0CallAddbackBeqPost; rw [sepConj_assoc'] at hq; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
