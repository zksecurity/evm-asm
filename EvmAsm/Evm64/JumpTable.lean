/-
  EvmAsm.Evm64.JumpTable

  Slice 1 of GH #106 (opcode dispatch via jump table).

  Defines the `dispatchTableIs` separation-logic assertion describing a
  256-entry handler-address table laid out at consecutive doubleword
  cells in RV64 memory:

      base + 0   ↦ₘ handlers[0]
      base + 8   ↦ₘ handlers[1]
      ...
      base + 8·k ↦ₘ handlers[k]
      ...
      base + 8·255 ↦ₘ handlers[255]

  This module only fixes the layout and proves the basic projection
  (`getMem (base + 8·opcode) = handlers[opcode]` from
  `dispatchTableIs.holdsFor`). The dispatch RV64 program (LBU/SLLI/ADD/
  LD/JALR sequence) and its Hoare triple land in subsequent slices
  (`evm-asm-kvygx`, `evm-asm-afkny`, `evm-asm-3ho93`).

  No new tactics, no existing files modified — strictly additive.
-/

import EvmAsm.Rv64.Basic
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Auxiliary builder: assertion describing handler-address dwords for
    the `count` entries with indices `[start, start + count)`, where
    `start + count ≤ 256`.

    Entries are chained by `**` from index `start` upward; the recursion
    is on the residual `count`. The companion `dispatchTableIs` below
    fixes `start = 0` and `count = 256`. -/
def dispatchTableIs.aux (base : Word) (handlers : Fin 256 → Word) :
    (start : Nat) → (count : Nat) → Assertion
  | _,     0     => empAssertion
  | start, n + 1 =>
    if h : start < 256 then
      ((base + BitVec.ofNat 64 (8 * start)) ↦ₘ handlers ⟨start, h⟩)
        ** dispatchTableIs.aux base handlers (start + 1) n
    else
      empAssertion

/-- Layout assertion for a 256-entry RV64 jump table at base address
    `base`. Entry `i` holds the handler address `handlers i` in the
    doubleword cell at `base + 8·i`. -/
def dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIs.aux base handlers 0 256

/-- Convenience alias: `evmJumpTableIs` is identical to
    `dispatchTableIs` but reads more naturally inside EVM-level specs. -/
def evmJumpTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  dispatchTableIs base handlers

@[simp] theorem evmJumpTableIs_eq (base : Word) (handlers : Fin 256 → Word) :
    evmJumpTableIs base handlers = dispatchTableIs base handlers := rfl

/-! ### Projection: read one handler-address entry from the layout. -/

/-- Helper: `dispatchTableIs.aux` with `count = 0` is `empAssertion`. -/
@[simp] theorem dispatchTableIs.aux_zero (base : Word)
    (handlers : Fin 256 → Word) (start : Nat) :
    dispatchTableIs.aux base handlers start 0 = empAssertion := rfl

/-- Helper: unfold one step of the auxiliary builder when `start < 256`. -/
theorem dispatchTableIs.aux_succ (base : Word)
    (handlers : Fin 256 → Word) {start : Nat} (h : start < 256) (n : Nat) :
    dispatchTableIs.aux base handlers start (n + 1)
      = (((base + BitVec.ofNat 64 (8 * start)) ↦ₘ handlers ⟨start, h⟩)
        ** dispatchTableIs.aux base handlers (start + 1) n) := by
  simp only [dispatchTableIs.aux, dif_pos h]

/-- The auxiliary layout assertion forces the dword at
    `base + 8·(start + k)` to read back the corresponding handler entry,
    for any `k < count` with `start + count ≤ 256`. -/
theorem dispatchTableIs.aux_getMem
    {base : Word} {handlers : Fin 256 → Word}
    {start count : Nat} (hsum : start + count ≤ 256)
    {s : MachineState}
    (hP : (dispatchTableIs.aux base handlers start count).holdsFor s)
    (k : Nat) (hk : k < count) :
    s.getMem (base + BitVec.ofNat 64 (8 * (start + k)))
      = handlers ⟨start + k, by omega⟩ := by
  induction count generalizing start k with
  | zero => omega
  | succ n ih =>
    have hstart : start < 256 := by omega
    rw [dispatchTableIs.aux_succ base handlers hstart n] at hP
    have hP_left  := holdsFor_sepConj_elim_left  hP
    have hP_right := holdsFor_sepConj_elim_right hP
    match k with
    | 0 =>
      -- The leading cell directly matches the head sepConj entry.
      have hmem := (holdsFor_memIs.mp hP_left).1
      simpa [Nat.add_zero] using hmem
    | k' + 1 =>
      -- Step into the tail: shift `start ↦ start+1`, `k' < n`.
      have hk' : k' < n := Nat.lt_of_succ_lt_succ hk
      have hsum' : (start + 1) + n ≤ 256 := by omega
      have hrec := ih (start := start + 1) hsum' hP_right k' hk'
      have hidx : start + (k' + 1) = (start + 1) + k' := by omega
      have hfin :
          (⟨start + (k' + 1), by omega⟩ : Fin 256)
            = ⟨(start + 1) + k', by omega⟩ := by
        apply Fin.ext; exact hidx
      rw [hfin, show (8 * (start + (k' + 1))) = (8 * ((start + 1) + k')) by omega]
      exact hrec

/-- **Projection lemma.** If the 256-entry jump-table layout holds at
    `base`, then for every opcode byte `opcode : Fin 256` the dword cell
    at `base + 8·opcode` reads back the corresponding handler address
    `handlers opcode`. -/
theorem dispatchTableIs_getMem
    {base : Word} {handlers : Fin 256 → Word}
    {s : MachineState}
    (hP : (dispatchTableIs base handlers).holdsFor s)
    (opcode : Fin 256) :
    s.getMem (base + BitVec.ofNat 64 (8 * opcode.val))
      = handlers opcode := by
  have hk : opcode.val < 256 := opcode.isLt
  have h := dispatchTableIs.aux_getMem
    (base := base) (handlers := handlers)
    (start := 0) (count := 256) (by omega) hP opcode.val hk
  -- `start = 0` collapses `start + k = k` and `⟨k, _⟩ = opcode`.
  have hfin : (⟨0 + opcode.val, by omega⟩ : Fin 256) = opcode := by
    apply Fin.ext; simp
  simpa [Nat.zero_add, hfin] using h

end EvmAsm.Evm64
