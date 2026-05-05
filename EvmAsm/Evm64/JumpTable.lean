/-
  EvmAsm.Evm64.JumpTable

  RV64 memory-layout assertion for the opcode jump-table dispatch (GH #106
  slice 1 / beads `evm-asm-3pyqn`).

  The jump table is a 256-entry, 8-byte-per-entry block in RV64 memory:
  the handler address for opcode byte `i` lives at `base + i*8`. Together
  with a follow-up dispatch program (LBU opcode; SLLI 3; ADD base; LD;
  JALR — slice 2) and a corresponding Hoare triple (slice 3), this forms
  the RV64 surface for the `HandlerTable` semantic dispatcher
  (`EvmAsm.Evm64.HandlerTable`).

  This slice only introduces the assertion shape and basic structural
  lemmas (PC-freeness, list-form characterization, cons/nil unfolds, and
  byte-size constants). The dispatch program and `dispatch_spec` land in
  later slices under parent `evm-asm-77w8s` (GH #106).

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- List-form helper: assert that consecutive 8-byte memory cells starting
    at `base` hold the addresses listed in `addrs`, each at offset
    `i * 8`. Recursive on the list so `pcFree` and structural equalities
    follow the standard `evmStackIs`-style induction. -/
def jumpTableListIs (base : Word) (addrs : List Word) : Assertion :=
  match addrs with
  | [] => empAssertion
  | a :: rest => (base ↦ₘ a) ** jumpTableListIs (base + 8) rest

/-- Assertion that an RV64 jump table for the opcode dispatcher lives at
    `base`. The table has 256 entries of 8 bytes each (2048 bytes total);
    `handlers i` is the RV64 address of the handler for opcode byte `i`. -/
def dispatchTableIs (base : Word) (handlers : Fin 256 → Word) : Assertion :=
  jumpTableListIs base ((List.finRange 256).map handlers)

/-- The total number of bytes occupied by a `dispatchTableIs` block:
    256 entries × 8 bytes = 2048 bytes. -/
def dispatchTableBytes : Nat := 256 * 8

@[simp] theorem dispatchTableBytes_eq : dispatchTableBytes = 2048 := rfl

-- ---------------------------------------------------------------------------
-- Structural equalities
-- ---------------------------------------------------------------------------

@[simp] theorem jumpTableListIs_nil (base : Word) :
    jumpTableListIs base [] = empAssertion := rfl

@[simp] theorem jumpTableListIs_cons (base : Word) (a : Word) (rest : List Word) :
    jumpTableListIs base (a :: rest) =
      ((base ↦ₘ a) ** jumpTableListIs (base + 8) rest) := rfl

-- ---------------------------------------------------------------------------
-- pcFree
-- ---------------------------------------------------------------------------

theorem pcFree_jumpTableListIs (base : Word) (addrs : List Word) :
    (jumpTableListIs base addrs).pcFree := by
  induction addrs generalizing base with
  | nil => simpa [jumpTableListIs] using pcFree_emp
  | cons a rest ih =>
    simp only [jumpTableListIs]
    exact pcFree_sepConj pcFree_memIs (ih (base + 8))

instance (base : Word) (addrs : List Word) :
    Assertion.PCFree (jumpTableListIs base addrs) :=
  ⟨pcFree_jumpTableListIs base addrs⟩

theorem pcFree_dispatchTableIs (base : Word) (handlers : Fin 256 → Word) :
    (dispatchTableIs base handlers).pcFree := by
  unfold dispatchTableIs
  exact pcFree_jumpTableListIs _ _

instance (base : Word) (handlers : Fin 256 → Word) :
    Assertion.PCFree (dispatchTableIs base handlers) :=
  ⟨pcFree_dispatchTableIs base handlers⟩

-- ---------------------------------------------------------------------------
-- Length characterization
-- ---------------------------------------------------------------------------

@[simp] theorem dispatchTableIs_length_handlers (handlers : Fin 256 → Word) :
    ((List.finRange 256).map handlers).length = 256 := by
  simp

end EvmAsm.Evm64
