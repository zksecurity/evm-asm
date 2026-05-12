import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulIterBaseFrame
    (evmSp a0 a1 a2 a3 : Word) : Assertion :=
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)

theorem expTwoMulIterBaseFrame_unfold {evmSp a0 a1 a2 a3 : Word} :
    expTwoMulIterBaseFrame evmSp a0 a1 a2 a3 =
      (((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)) := by
  delta expTwoMulIterBaseFrame
  rfl

@[irreducible]
def expTwoMulIterSkipRest
    (bit sp evmSp base : Word) (w : EvmWord) : Assertion :=
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ (w * w).getLimbN 3) **
  evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ ((base + 44) + 68))

theorem expTwoMulIterSkipRest_unfold {bit sp evmSp base : Word} {w : EvmWord} :
    expTwoMulIterSkipRest bit sp evmSp base w =
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝ **
       (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ (w * w).getLimbN 3) **
       evmWordIs sp (w * w) ** evmWordIs (evmSp + 32) (w * w) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 44) + 68))) := by
  delta expTwoMulIterSkipRest
  rfl

@[irreducible]
def expTwoMulIterCondRest
    (sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord) : Assertion :=
  (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
  (.x5 ↦ᵣ rw.getLimbN 3) **
  ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
  ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
  ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
  ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
  evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  memOwn evmSp ** memOwn (evmSp + 8) **
  memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
  (.x1 ↦ᵣ ((base + 152) + 68))

theorem expTwoMulIterCondRest_unfold
    {sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord} :
    expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw =
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
       (.x5 ↦ᵣ rw.getLimbN 3) **
       ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
       ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
       ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
       ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
       evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       memOwn evmSp ** memOwn (evmSp + 8) **
       memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
       (.x1 ↦ᵣ ((base + 152) + 68))) := by
  delta expTwoMulIterCondRest
  rfl

@[irreducible]
def expTwoMulIterCondFrame (bit : Word) : Assertion :=
  (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
  ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝

theorem expTwoMulIterCondFrame_unfold {bit : Word} :
    expTwoMulIterCondFrame bit =
      ((.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
       ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝) := by
  delta expTwoMulIterCondFrame
  rfl

@[irreducible]
def expTwoMulIterCondPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (rw : EvmWord)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜exitCond⌝) ** expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw) **
  expTwoMulIterCondFrame bit

theorem expTwoMulIterCondPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {rw : EvmWord}
    {exitCond : Prop} :
    expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw exitCond =
      ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜exitCond⌝) ** expTwoMulIterCondRest sp evmSp base a0 a1 a2 a3 rw) **
       expTwoMulIterCondFrame bit) := by
  delta expTwoMulIterCondPost
  rfl

@[irreducible]
def expTwoMulIterSkipPost
    (iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word) (w : EvmWord)
    (exitCond : Prop) : Assertion :=
  (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
   ⌜exitCond⌝) ** expTwoMulIterSkipRest bit sp evmSp base w) **
  expTwoMulIterBaseFrame evmSp a0 a1 a2 a3

theorem expTwoMulIterSkipPost_unfold
    {iterCountNew bit sp evmSp base a0 a1 a2 a3 : Word} {w : EvmWord}
    {exitCond : Prop} :
    expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w exitCond =
      ((((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) **
        ⌜exitCond⌝) ** expTwoMulIterSkipRest bit sp evmSp base w) **
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3) := by
  delta expTwoMulIterSkipPost
  rfl

theorem exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_named_posts_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base loopTarget : Word)
    (hbase : base &&& 1 = 0)
    (hsqmt : mulTarget = ((base + 44) + 64) + signExtend21 squaringMulOff)
    (hcondmt : mulTarget = ((base + 152) + 64) + signExtend21 condMulOff)
    (hd : CodeReq.Disjoint
            (evmExpMsbSavedBitTwoMulCode
              base squaringMulOff condMulOff skipOff backOff)
            (mul_callable_code mulTarget))
    (hskip : (base + 148 : Word) + signExtend13 skipOff = base + 256)
    (hback : ((base + 256) + 4 : Word) + signExtend13 backOff = loopTarget) :
    let bit := e >>> (63 : BitVec 6).toNat
    let w := expResultWord r0 r1 r2 r3
    let aw := expResultWord a0 a1 a2 a3
    let rw := (w * w) * aw
    let iterCountNew := iterCount + signExtend12 ((-1 : BitVec 12))
    cpsBranchWithin
      (((3 + 1 + (17 + 64 + 9) + 1) + 2) + ((17 + 64 + 9) + 2))
      (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x5 ↦ᵣ e) ** regOwn .x6 ** regOwn .x10 ** (.x18 ↦ᵣ v18) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        regOwn .x7 ** regOwn .x11 ** (.x1 ↦ᵣ vOld) **
        (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ iterCount)) **
       expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)
      loopTarget
        (fun h =>
          expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
            (iterCountNew ≠ 0) h ∨
          expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w
            (iterCountNew ≠ 0) h)
      (base + 264)
        (fun h =>
          expTwoMulIterCondPost iterCountNew bit sp evmSp base a0 a1 a2 a3 rw
            (iterCountNew = 0) h ∨
          expTwoMulIterSkipPost iterCountNew bit sp evmSp base a0 a1 a2 a3 w
            (iterCountNew = 0) h) := by
  intro bit w aw rw iterCountNew
  rw [expTwoMulIterBaseFrame_unfold]
  exact cpsBranchWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rcases hp with hp | hp
      · left
        simpa [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
          expTwoMulIterCondFrame_unfold] using hp
      · right
        simpa [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
          expTwoMulIterBaseFrame_unfold] using hp)
    (fun _ hp => by
      rcases hp with hp | hp
      · left
        simpa [expTwoMulIterCondPost_unfold, expTwoMulIterCondRest_unfold,
          expTwoMulIterCondFrame_unfold] using hp
      · right
        simpa [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
          expTwoMulIterBaseFrame_unfold] using hp)
    (exp_msb_saved_bit_two_mul_full_iter_owned_scratch_branch_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 mulTarget
      squaringMulOff condMulOff skipOff backOff base loopTarget
      hbase hsqmt hcondmt hd hskip hback)

end EvmAsm.Evm64.Exp.Compose
