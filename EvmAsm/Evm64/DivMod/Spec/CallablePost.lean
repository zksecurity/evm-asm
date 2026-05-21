/-
  EvmAsm.Evm64.DivMod.Spec.CallablePost

  Reusable postcondition weakeners for callable DIV/MOD no-NOP dispatcher
  surfaces that frame exact x1/x9 separately.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Concrete no-NOP DIV callable post bundle produced by the bzero and
    branch-local dispatcher proofs before weakening to the public callable
    postcondition. -/
@[irreducible]
def divConcretePostNoX1Frame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem divConcretePostNoX1Frame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.div a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
        evmWordIs sp a **
        divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta divConcretePostNoX1Frame
  rfl

theorem divConcretePostNoX1Frame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [divConcretePostNoX1Frame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- Weaken the concrete no-NOP DIV callable post bundle to the public
    callable postcondition plus the caller-framed exact `x1` and `x9` atoms. -/
theorem divConcretePostNoX1_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      divConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [divConcretePostNoX1Frame_unfold] at hp
  rw [divStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
        regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.div a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- Split the historical no-`x1` DIV stack post into the callable public post
    plus separate `x1` ownership. This is the ownership-only bridge; exact
    return-address preservation requires a stronger upstream post. -/
theorem divStackDispatchPostNoX1_weaken_callable_own_x1
    (sp : Word) (a b : EvmWord) :
  ∀ h : PartialState,
      divStackDispatchPostNoX1 sp a b h →
      (divStackDispatchPostCallable sp a b ** regOwn .x1) h := by
  intro h hp
  rw [divStackDispatchPostNoX1_unfold] at hp
  rw [divStackDispatchPostCallable_unfold]
  rw [divScratchOwnCall_unfold] at hp
  rw [divScratchOwnCallNoX1_unfold]
  xperm_hyp hp

/-- Framed variant of `divStackDispatchPostNoX1_weaken_callable_own_x1`
    preserving an exact caller-owned `x9` atom. -/
theorem divStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (x9Val : Word) :
  ∀ h : PartialState,
      (divStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ x9Val)) h →
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  apply sepConj_mono_left
  · exact fun hLeft hpLeft =>
      divStackDispatchPostNoX1_weaken_callable_own_x1 sp a b hLeft hpLeft
  · exact hp

/-- Weaken an exact caller-framed `x1` callable post to the ownership-only
    callable post shape, preserving an exact caller-owned `x9` atom. -/
theorem divStackDispatchPostCallable_exact_x1_weaken_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (raVal x9Val : Word) :
  ∀ h : PartialState,
      ((divStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h →
      ((divStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  exact sepConj_mono_left
    (sepConj_mono_right (regIs_implies_regOwn .x1 (v := raVal)))
    h hp

/-- Concrete no-NOP MOD callable post bundle before weakening. -/
@[irreducible]
def modConcretePostNoX1Frame (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) : Assertion :=
  (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
    (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
   ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0))

theorem modConcretePostNoX1Frame_unfold
    {sp : Word} {a b : EvmWord}
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0 =
    (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
      (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) **
     ((.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
      (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
      evmWordIs sp a **
      divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)) := by
  delta modConcretePostNoX1Frame
  rfl

theorem modConcretePostNoX1Frame_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val raVal v2 v6 v7 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [modConcretePostNoX1Frame_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

/-- MOD counterpart of `divConcretePostNoX1_weaken_callable_frame`. -/
theorem modConcretePostNoX1_weaken_callable_frame
    (sp : Word) (a b : EvmWord)
    {x9Val raVal v2 v6 v7 v11 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word} :
    ∀ h : PartialState,
      modConcretePostNoX1Frame sp a b x9Val raVal v2 v6 v7 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 h →
      (((modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) **
        (.x9 ↦ᵣ x9Val)) h) := by
  intro h hp
  rw [modConcretePostNoX1Frame_unfold] at hp
  rw [modStackDispatchPostCallable_unfold]
  simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hp ⊢
  have hOwn :
      (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
        (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
        regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
        regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
    refine sepConj_mono ?_ ?_ h hp
    · intro hLeft hpLeft
      exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
        sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
          retMem dMem dloMem scratch_un0 hLeft hpLeft
    · apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
      apply sepConj_mono_right
      apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
      apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
      apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
      exact fun _ hp => hp
  exact by xperm_hyp hOwn

/-- Split the historical no-`x1` MOD stack post into the callable public post
    plus separate `x1` ownership. This mirrors
    `divStackDispatchPostNoX1_weaken_callable_own_x1`. -/
theorem modStackDispatchPostNoX1_weaken_callable_own_x1
    (sp : Word) (a b : EvmWord) :
  ∀ h : PartialState,
      modStackDispatchPostNoX1 sp a b h →
      (modStackDispatchPostCallable sp a b ** regOwn .x1) h := by
  intro h hp
  rw [modStackDispatchPostNoX1_unfold] at hp
  rw [modStackDispatchPostCallable_unfold]
  rw [divScratchOwnCall_unfold] at hp
  rw [divScratchOwnCallNoX1_unfold]
  xperm_hyp hp

/-- Framed variant of `modStackDispatchPostNoX1_weaken_callable_own_x1`
    preserving an exact caller-owned `x9` atom. -/
theorem modStackDispatchPostNoX1_weaken_callable_own_x1_frame_x9
    (sp : Word) (a b : EvmWord) (x9Val : Word) :
  ∀ h : PartialState,
      (modStackDispatchPostNoX1 sp a b ** (.x9 ↦ᵣ x9Val)) h →
      ((modStackDispatchPostCallable sp a b ** regOwn .x1) **
        (.x9 ↦ᵣ x9Val)) h := by
  intro h hp
  apply sepConj_mono_left
  · exact fun hLeft hpLeft =>
      modStackDispatchPostNoX1_weaken_callable_own_x1 sp a b hLeft hpLeft
  · exact hp

end EvmAsm.Evm64
