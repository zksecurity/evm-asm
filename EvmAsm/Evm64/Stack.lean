/-
  EvmAsm.Evm64.Stack

  Separation logic assertions for 256-bit EVM values stored as
  4 little-endian 64-bit limbs in consecutive doubleword-aligned memory.
-/

import EvmAsm.Evm64.Basic
import EvmAsm.Rv64.SepLogic

namespace EvmAsm.Rv64

open EvmWord

/-- Assert that 4 consecutive memory doublewords hold the limbs of an EvmWord.
    The limbs are stored little-endian: addr+0 is the LSB limb, addr+24 is the MSB limb. -/
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) **
  ((addr + 8) ↦ₘ v.getLimb 1) **
  ((addr + 16) ↦ₘ v.getLimb 2) **
  ((addr + 24) ↦ₘ v.getLimb 3)

/-- Assert an EVM stack starting at sp. Each element is 32 bytes (4 × 8-byte limbs). -/
def evmStackIs (sp : Addr) (values : List EvmWord) : Assertion :=
  match values with
  | [] => empAssertion
  | v :: vs => evmWordIs sp v ** evmStackIs (sp + 32) vs

theorem pcFree_evmWordIs (addr : Addr) (v : EvmWord) :
    (evmWordIs addr v).pcFree := by
  unfold evmWordIs
  exact pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
    (pcFree_sepConj (pcFree_memIs _ _)
                    (pcFree_memIs _ _)))

theorem pcFree_evmStackIs (sp : Addr) (values : List EvmWord) :
    (evmStackIs sp values).pcFree := by
  induction values generalizing sp with
  | nil => exact pcFree_emp
  | cons v vs ih => exact pcFree_sepConj (pcFree_evmWordIs sp v) (ih (sp + 32))

instance (addr : Addr) (v : EvmWord) : Assertion.PCFree (evmWordIs addr v) :=
  ⟨pcFree_evmWordIs addr v⟩

instance (sp : Addr) (values : List EvmWord) : Assertion.PCFree (evmStackIs sp values) :=
  ⟨pcFree_evmStackIs sp values⟩

theorem evmStackIs_cons (sp : Addr) (v : EvmWord) (vs : List EvmWord) :
    evmStackIs sp (v :: vs) = (evmWordIs sp v ** evmStackIs (sp + 32) vs) := rfl

theorem evmStackIs_nil (sp : Addr) :
    evmStackIs sp [] = empAssertion := rfl

end EvmAsm.Rv64
