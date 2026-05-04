/-
  EvmAsm.EL.CreateEffects

  Pure successful-deployment world-state effect for CREATE and CREATE2
  (GH #115).  This module sits between the request/address surface and
  the later opcode handler specs: once a creation request has produced
  runtime code and an address, `deployResult` records the account that
  appears in the world state and the deployed `CreateResult`.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CreateAddress

namespace EvmAsm.EL
namespace CreateEffects

/-- Account installed by a successful CREATE-family deployment.

    The storage root is left as zero in this pure model until a trie-backed
    storage-root bridge exists.  The nonce is `1`, matching the post-Spurious
    Dragon creation rule modeled by the executable spec surface. -/
def deployedAccount (request : CreateRequest) (codeHash : Hash256) : Account :=
  { nonce := 1
    balance := request.value
    storageRoot := 0
    codeHash := codeHash
    code := request.initcode }

/-- Successful CREATE-family effect: install the deployed account at the
    derived address and return a deployed result with empty returndata. -/
def deployResult
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) : CreateResult :=
  { status := .deployed
    address? := some address
    state := WorldState.setAccount state address (deployedAccount request codeHash)
    returndata := []
    gasRemaining := gasRemaining }

theorem deployedAccountNonce (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).nonce = 1 := rfl

theorem deployedAccountBalance (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).balance = request.value := rfl

theorem deployedAccountCodeHash (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).codeHash = codeHash := rfl

theorem deployedAccountCode (request : CreateRequest) (codeHash : Hash256) :
    (deployedAccount request codeHash).code = request.initcode := rfl

/-- The deployed result reports the successful status. -/
theorem deployResultDeployed
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).deployed := rfl

theorem deployResultAddress?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).address? =
      some address := rfl

theorem deployResultReturndata
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).returndata = [] := rfl

theorem deployResultGasRemaining
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    (deployResult state request address codeHash gasRemaining).gasRemaining =
      gasRemaining := rfl

/-- Distinctive token: `CreateEffects.deployResultAccount`. -/
theorem deployResultAccount
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.getAccount
        (deployResult state request address codeHash gasRemaining).state
        address =
      some (deployedAccount request codeHash) := by
  simp [deployResult]

theorem deployResultAccount_ne
    (state : WorldState) (request : CreateRequest) {address other : Address}
    (codeHash : Hash256) (gasRemaining : Nat) (h_ne : other ≠ address) :
    WorldState.getAccount
        (deployResult state request address codeHash gasRemaining).state
        other =
      WorldState.getAccount state other := by
  simp [deployResult, WorldState.getAccount_setAccount_ne, h_ne]

theorem deployResultCode?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.accountCode?
        (deployResult state request address codeHash gasRemaining).state
        address =
      some request.initcode := by
  simp [deployResult, deployedAccount]

theorem deployResultCodeHash?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.accountCodeHash?
        (deployResult state request address codeHash gasRemaining).state
        address =
      some codeHash := by
  simp [deployResult, deployedAccount]

theorem deployResultBalance?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.accountBalance?
        (deployResult state request address codeHash gasRemaining).state
        address =
      some request.value := by
  simp [deployResult, deployedAccount]

theorem deployResultNonce?
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    WorldState.accountNonce?
        (deployResult state request address codeHash gasRemaining).state
        address =
      some 1 := by
  simp [deployResult, deployedAccount]

theorem deployResultAddressMatches
    (state : WorldState) (request : CreateRequest) (address : Address)
    (codeHash : Hash256) (gasRemaining : Nat) :
    CreateAddress.resultAddressMatches
      (deployResult state request address codeHash gasRemaining)
      address := by
  exact ⟨rfl, rfl⟩

end CreateEffects
end EvmAsm.EL
