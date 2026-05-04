/-
  EvmAsm.EL.CreateResultBridge

  Bridge from CREATE-family results to the EVM stack result word (GH #115).
-/

import EvmAsm.EL.Create

namespace EvmAsm.EL

namespace CreateResultBridge

/-- Stack word pushed by CREATE/CREATE2 after execution.

    Successful deployments push the created address as a 256-bit word.
    Reverts, failures, and malformed deployed results without an address push
    zero. Distinctive token: CreateResultBridge.createResultStackWord #115. -/
def createResultStackWord (result : CreateResult) : Word256 :=
  match result.status, result.address? with
  | .deployed, some address => address.zeroExtend 256
  | _, _ => 0

theorem createResultStackWord_deployed
    (address : Address) (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    createResultStackWord
        { status := .deployed
          address? := some address
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      address.zeroExtend 256 := rfl

theorem createResultStackWord_deployed_none
    (state : WorldState) (returndata : List Byte) (gasRemaining : Nat) :
    createResultStackWord
        { status := .deployed
          address? := none
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      0 := rfl

theorem createResultStackWord_reverted
    (address? : Option Address) (state : WorldState) (returndata : List Byte)
    (gasRemaining : Nat) :
    createResultStackWord
        { status := .reverted
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      0 := by
  cases address? <;> rfl

theorem createResultStackWord_failed
    (address? : Option Address) (state : WorldState) (returndata : List Byte)
    (gasRemaining : Nat) :
    createResultStackWord
        { status := .failed
          address? := address?
          state := state
          returndata := returndata
          gasRemaining := gasRemaining } =
      0 := by
  cases address? <;> rfl

theorem createResultStackWord_eq_zero_of_not_deployed
    {result : CreateResult} (h_status : result.status ≠ .deployed) :
    createResultStackWord result = 0 := by
  cases result with
  | mk status address? state returndata gasRemaining =>
      cases status <;> simp_all [createResultStackWord]

theorem createResultStackWord_eq_zero_of_address_none
    {result : CreateResult} (h_addr : result.address? = none) :
    createResultStackWord result = 0 := by
  cases result with
  | mk status address? state returndata gasRemaining =>
      cases status <;> simp_all [createResultStackWord]

theorem createResultStackWord_eq_address_of_matches
    {result : CreateResult} {address : Address}
    (h_match : result.status = .deployed ∧ result.address? = some address) :
    createResultStackWord result = address.zeroExtend 256 := by
  cases result with
  | mk status address? state returndata gasRemaining =>
      rcases h_match with ⟨h_status, h_addr⟩
      cases status <;> simp_all [createResultStackWord]

end CreateResultBridge

end EvmAsm.EL
