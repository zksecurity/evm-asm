/-
  EvmAsm.Evm64.PrecompileDispatch

  Pure precompile dispatch outcome surface for GH #116.
-/

import EvmAsm.Evm64.PrecompileResult

namespace EvmAsm.Evm64

namespace PrecompileDispatch

/-- Decode a precompile target from an EVM account address. -/
def decode? (addr : Address) : Option Precompile :=
  Precompile.ofAddress? addr

/-- Byte-length-only gas cost for a precompile input, when known without
    payload-specific decoding. -/
def gasCost? (input : PrecompileInput) : Option Nat :=
  Precompile.precompileGasCost? input.target input.input.length

/-- Predicate form used by CALL-family dispatch before invoking a precompile. -/
def precompileGasAffordable (input : PrecompileInput) : Prop :=
  ∃ cost, gasCost? input = some cost ∧ cost ≤ input.gas

/-- Dispatch wrapper for known-cost precompiles. Payload-specific gas schedules
    stay as `none` until their executable-spec bridges provide decoded costs. -/
def dispatch? (input : PrecompileInput) (out : List (BitVec 8)) : Option PrecompileResult :=
  match gasCost? input with
  | none => none
  | some cost =>
      if cost ≤ input.gas then
        some (PrecompileResult.ok out (input.gas - cost))
      else
        some (PrecompileResult.fail input.gas)

/-- Address-level dispatch wrapper used before constructing an opcode-level
    CALL-family state transition. -/
def dispatchAddress? (addr caller : Address) (payload out : List (BitVec 8)) (gas : Nat) :
    Option PrecompileResult :=
  match decode? addr with
  | none => none
  | some target =>
      dispatch?
        { target := target
          caller := caller
          input := payload
          gas := gas }
        out

theorem decode?_address (p : Precompile) :
    decode? p.address = some p := by
  exact Precompile.ofAddress?_address p

theorem decode?_zero :
    decode? (0 : Address) = none := by
  exact Precompile.ofAddress?_zero

theorem gasCost?_eq (input : PrecompileInput) :
    gasCost? input = Precompile.precompileGasCost? input.target input.input.length := rfl

theorem precompileGasAffordable_of_gasCost?_le {input : PrecompileInput} {cost : Nat}
    (h_cost : gasCost? input = some cost) (h_le : cost ≤ input.gas) :
    precompileGasAffordable input := by
  exact ⟨cost, h_cost, h_le⟩

theorem dispatch?_none_of_gasCost?_none {input : PrecompileInput} {out : List (BitVec 8)}
    (h_cost : gasCost? input = none) :
    dispatch? input out = none := by
  simp [dispatch?, h_cost]

theorem dispatch?_ok_of_gasCost?_le {input : PrecompileInput} {out : List (BitVec 8)}
    {cost : Nat} (h_cost : gasCost? input = some cost) (h_le : cost ≤ input.gas) :
    dispatch? input out = some (PrecompileResult.ok out (input.gas - cost)) := by
  simp [dispatch?, h_cost, h_le]

theorem dispatch?_fail_of_gasCost?_gt {input : PrecompileInput} {out : List (BitVec 8)}
    {cost : Nat} (h_cost : gasCost? input = some cost) (h_gt : input.gas < cost) :
    dispatch? input out = some (PrecompileResult.fail input.gas) := by
  have h_not : ¬ cost ≤ input.gas := Nat.not_le.mpr h_gt
  simp [dispatch?, h_cost, h_not]

theorem dispatchAddress?_none_zero (caller : Address) (payload out : List (BitVec 8))
    (gas : Nat) :
    dispatchAddress? 0 caller payload out gas = none := by
  unfold dispatchAddress?
  rw [decode?_zero]

theorem dispatchAddress?_address (p : Precompile) (caller : Address)
    (payload out : List (BitVec 8)) (gas : Nat) :
    dispatchAddress? p.address caller payload out gas =
      dispatch?
        { target := p
          caller := caller
          input := payload
          gas := gas }
        out := by
  simp [dispatchAddress?, decode?_address p]

end PrecompileDispatch

end EvmAsm.Evm64
