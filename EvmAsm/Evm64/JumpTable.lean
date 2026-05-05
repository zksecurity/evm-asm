/-
  EvmAsm.Evm64.JumpTable

  RV64 memory layout for the EVM opcode dispatch table (GH #106 slice 1).

  The dispatch table is a 2048-byte region (256 entries × 8 bytes) at a
  doubleword-aligned base address. Entry `i` holds the address of the
  RV64 handler for opcode byte `i`. Subsequent slices implement the
  RV64 program that loads the entry for the current opcode and jumps to
  it (`dispatch_spec`), and the INVALID-handler default (#106 slice 4).

  Surface:
    * `dispatchTableIs base handlers` — the separation-logic assertion
      that 256 consecutive doubleword cells at `base, base+8, …,
      base+2040` hold the handler addresses given by
      `handlers : Fin 256 → Word`.
    * `dispatchTableIs_lookup` — projection: from the assertion,
      conclude `s.getMem (base + i.val * 8) = handlers i` for any
      opcode `i : Fin 256`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Auxiliary: assert the first `k` entries (entries `0..k-1`) of the
    dispatch table at `base` hold the handler addresses given by
    `handlers`. Recursion is on `k`; the head case (`k+1`) peels entry
    `k`. We require `k ≤ 256` so that the index `⟨k, _⟩ : Fin 256` is
    well-formed. -/
def dispatchTableIsTake (base : Word) (handlers : Fin 256 → Word) :
    (k : Nat) → k ≤ 256 → Assertion
  | 0, _ => empAssertion
  | k + 1, hk =>
    ((base + BitVec.ofNat 64 (k * 8)) ↦ₘ handlers ⟨k, hk⟩) **
      dispatchTableIsTake base handlers k (Nat.le_of_succ_le hk)

/-- Assert that 256 consecutive doubleword cells starting at `base`
    hold the dispatch-table entries given by `handlers`. The base
    address must be 8-byte aligned (caller's obligation, encoded
    indirectly via `isValidDwordAccess` on each cell). -/
def dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIsTake base handlers 256 (Nat.le_refl _)

-- ============================================================================
-- pcFree
-- ============================================================================

theorem pcFree_dispatchTableIsTake {base : Word} {handlers : Fin 256 → Word}
    {k : Nat} {hk : k ≤ 256} :
    (dispatchTableIsTake base handlers k hk).pcFree := by
  induction k with
  | zero => exact pcFree_emp
  | succ k ih =>
    unfold dispatchTableIsTake
    exact pcFree_sepConj pcFree_memIs (ih (hk := Nat.le_of_succ_le hk))

theorem pcFree_dispatchTableIs {base : Word} {handlers : Fin 256 → Word} :
    (dispatchTableIs base handlers).pcFree :=
  pcFree_dispatchTableIsTake

instance (base : Word) (handlers : Fin 256 → Word) :
    Assertion.PCFree (dispatchTableIs base handlers) :=
  ⟨pcFree_dispatchTableIs⟩

-- ============================================================================
-- Lookup projection
-- ============================================================================

/-- From the iterated assertion `dispatchTableIsTake base handlers k hk`
    holding for `s`, the memory cell at `base + i.val * 8` reads as
    `handlers i` for any opcode index `i` whose value is below `k`. -/
theorem dispatchTableIsTake_lookup
    {base : Word} {handlers : Fin 256 → Word} {s : MachineState} :
    ∀ {k : Nat} (hk : k ≤ 256) (i : Fin 256),
      i.val < k →
      (dispatchTableIsTake base handlers k hk).holdsFor s →
      s.getMem (base + BitVec.ofNat 64 (i.val * 8)) = handlers i
  | 0, _, _, hi, _ => by exact absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, i, hi, h => by
    unfold dispatchTableIsTake at h
    by_cases heq : i.val = k
    · -- entry just peeled
      have h1 := holdsFor_sepConj_elim_left h
      have hgm := holdsFor_memIs_getMem h1
      have hi_eq : i = ⟨k, hk⟩ := by
        apply Fin.ext; exact heq
      rw [hi_eq]; exact hgm
    · -- entry deeper in the table
      have h2 := holdsFor_sepConj_elim_right h
      have hi' : i.val < k := by omega
      exact dispatchTableIsTake_lookup (Nat.le_of_succ_le hk) i hi' h2

/-- Top-level lookup: from `(dispatchTableIs base handlers).holdsFor s`,
    the memory cell at `base + i.val * 8` reads as `handlers i`. -/
theorem dispatchTableIs_lookup
    {base : Word} {handlers : Fin 256 → Word} {s : MachineState}
    (i : Fin 256)
    (h : (dispatchTableIs base handlers).holdsFor s) :
    s.getMem (base + BitVec.ofNat 64 (i.val * 8)) = handlers i :=
  dispatchTableIsTake_lookup (Nat.le_refl _) i i.isLt h

end EvmAsm.Evm64
