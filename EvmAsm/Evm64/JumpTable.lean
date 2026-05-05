/-
  EvmAsm.Evm64.JumpTable

  RV64-level jump-table layout assertion for EVM opcode dispatch (GH #106
  slice 1).

  This file is the layout-only slice: it introduces

    * `dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion`

      A separation-logic assertion that the 256 × 8 = 2048-byte memory region
      starting at `base` holds the address of the handler for each opcode.
      Entry `i` lives at byte offset `8 * i.val`, stored as a 64-bit dword.

    * `evmJumpTableIs` — alias for the EVM-side name expected by GH #106.

    * `dispatchTableIs_lookup` — projects out a single `memIs` cell at
      `base + 8 * i.val` from the full table assertion, plus the corresponding
      `isValidDwordAccess` validity fact.

  Subsequent slices (#106 slice 2..5) add the actual RV64 program (LBU /
  SLLI / ADD / LD / JALR), the `dispatch_spec` Hoare triple, and the
  INVALID-handler default. See bead `evm-asm-77w8s`.

  Distinctive token: dispatchTableIs-slice1-layout-#106
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-! ## Layout assertion -/

/-- Auxiliary recursive table assertion over the first `n ≤ 256` entries.

    `dispatchTableAux base handlers n h` owns the `n` consecutive 8-byte
    cells at `base + 0, base + 8, ..., base + 8*(n-1)`, each holding the
    handler address for opcode `i < n`.

    Threading the bound `n ≤ 256` lets us index `handlers` with a real
    `Fin 256` element without packaging a separate `Nat → Word` view. -/
def dispatchTableAux (base : Word) (handlers : Fin 256 → Word) :
    (n : Nat) → n ≤ 256 → Assertion
  | 0,     _ => empAssertion
  | k + 1, h =>
      dispatchTableAux base handlers k (Nat.le_of_succ_le h) **
        ((base + BitVec.ofNat 64 (8 * k)) ↦ₘ handlers ⟨k, h⟩)

/-- The full RV64 jump-table layout assertion: 256 dword cells starting at
    `base`, with entry `i` holding `handlers i`. -/
def dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableAux base handlers 256 (Nat.le_refl _)

/-- EVM-side alias for `dispatchTableIs`, matching the naming convention
    used by other `evm…Is` assertions (`evmStackIs`, `evmMemIs`, …). -/
abbrev evmJumpTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIs base handlers

/-! ## Unfolding lemmas -/

@[simp] theorem dispatchTableAux_zero
    {base : Word} {handlers : Fin 256 → Word} {h : 0 ≤ 256} :
    dispatchTableAux base handlers 0 h = empAssertion := rfl

theorem dispatchTableAux_succ
    {base : Word} {handlers : Fin 256 → Word}
    {k : Nat} {h : k + 1 ≤ 256} :
    dispatchTableAux base handlers (k + 1) h =
      (dispatchTableAux base handlers k (Nat.le_of_succ_le h) **
        ((base + BitVec.ofNat 64 (8 * k)) ↦ₘ handlers ⟨k, h⟩)) := rfl

theorem dispatchTableIs_unfold
    {base : Word} {handlers : Fin 256 → Word} :
    dispatchTableIs base handlers =
      dispatchTableAux base handlers 256 (Nat.le_refl _) := rfl

theorem evmJumpTableIs_unfold
    {base : Word} {handlers : Fin 256 → Word} :
    evmJumpTableIs base handlers = dispatchTableIs base handlers := rfl

/-! ## pcFree -/

theorem pcFree_dispatchTableAux
    {base : Word} {handlers : Fin 256 → Word}
    {n : Nat} {h : n ≤ 256} :
    (dispatchTableAux base handlers n h).pcFree := by
  induction n with
  | zero => exact pcFree_emp
  | succ k ih =>
      rw [dispatchTableAux_succ]
      exact pcFree_sepConj ih pcFree_memIs

theorem pcFree_dispatchTableIs
    {base : Word} {handlers : Fin 256 → Word} :
    (dispatchTableIs base handlers).pcFree := by
  unfold dispatchTableIs; exact pcFree_dispatchTableAux

theorem pcFree_evmJumpTableIs
    {base : Word} {handlers : Fin 256 → Word} :
    (evmJumpTableIs base handlers).pcFree := pcFree_dispatchTableIs

instance (base : Word) (handlers : Fin 256 → Word) (n : Nat) (h : n ≤ 256) :
    Assertion.PCFree (dispatchTableAux base handlers n h) :=
  ⟨pcFree_dispatchTableAux⟩

instance (base : Word) (handlers : Fin 256 → Word) :
    Assertion.PCFree (dispatchTableIs base handlers) :=
  ⟨pcFree_dispatchTableIs⟩

instance (base : Word) (handlers : Fin 256 → Word) :
    Assertion.PCFree (evmJumpTableIs base handlers) :=
  ⟨pcFree_evmJumpTableIs⟩

/-! ## Lookup projection

    From the full table assertion we can recover the memory contents and
    validity fact at any entry `i : Fin 256`. -/

/-- Inductive lookup: the prefix `dispatchTableAux base handlers n h` owns
    every cell strictly below index `n`. -/
theorem holdsFor_dispatchTableAux_lookup
    {base : Word} {handlers : Fin 256 → Word}
    {n : Nat} {hn : n ≤ 256}
    {s : MachineState}
    (hs : (dispatchTableAux base handlers n hn).holdsFor s)
    (i : Nat) (hi : i < n) :
    s.getMem (base + BitVec.ofNat 64 (8 * i)) = handlers ⟨i, Nat.lt_of_lt_of_le hi hn⟩ ∧
      isValidDwordAccess (base + BitVec.ofNat 64 (8 * i)) = true := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
      rw [dispatchTableAux_succ] at hs
      rcases Nat.lt_or_ge i k with h_lt | h_ge
      · -- i < k: recurse on the left conjunct
        have hL : (dispatchTableAux base handlers k (Nat.le_of_succ_le hn)).holdsFor s :=
          holdsFor_sepConj_elim_left hs
        exact ih hL h_lt
      · -- k ≤ i and i < k+1, so i = k
        have h_eq : i = k := Nat.le_antisymm (Nat.le_of_lt_succ hi) h_ge
        subst h_eq
        have hR : ((base + BitVec.ofNat 64 (8 * i)) ↦ₘ handlers ⟨i, hn⟩).holdsFor s :=
          holdsFor_sepConj_elim_right hs
        exact holdsFor_memIs.mp hR

/-- The `dispatchTableIs` projection used by the dispatch-spec slice (slice
    3): from the table assertion at `base`, conclude the dword at
    `base + 8 * opcode` equals the handler address `handlers opcode`, and
    that this address is dword-valid. -/
theorem holdsFor_dispatchTableIs_lookup
    {base : Word} {handlers : Fin 256 → Word}
    {s : MachineState}
    (hs : (dispatchTableIs base handlers).holdsFor s)
    (i : Fin 256) :
    s.getMem (base + BitVec.ofNat 64 (8 * i.val)) = handlers i ∧
      isValidDwordAccess (base + BitVec.ofNat 64 (8 * i.val)) = true := by
  unfold dispatchTableIs at hs
  have h := holdsFor_dispatchTableAux_lookup hs i.val i.isLt
  -- The `Fin` packaging in `h` differs from `i` only in proof component.
  rcases i with ⟨iv, hiv⟩
  simpa using h

/-- Same projection through the EVM-side alias. -/
theorem holdsFor_evmJumpTableIs_lookup
    {base : Word} {handlers : Fin 256 → Word}
    {s : MachineState}
    (hs : (evmJumpTableIs base handlers).holdsFor s)
    (i : Fin 256) :
    s.getMem (base + BitVec.ofNat 64 (8 * i.val)) = handlers i ∧
      isValidDwordAccess (base + BitVec.ofNat 64 (8 * i.val)) = true :=
  holdsFor_dispatchTableIs_lookup hs i

end EvmAsm.Evm64
