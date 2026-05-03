/-
  EvmAsm.EL.WorldStateAccount

  Account-existence helpers for the pure EL world-state model (GH #123).
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

namespace Account

/-- Canonical empty account placeholder used when touching a missing account. -/
def empty : Account :=
  { nonce := 0
    balance := 0
    storageRoot := 0
    codeHash := 0
    code := [] }

/-- Coarse empty-account predicate for account lifecycle hooks. -/
def isEmpty (account : Account) : Prop :=
  account.nonce = 0 ∧ account.balance = 0 ∧ account.storageRoot = 0 ∧
    account.codeHash = 0 ∧ account.code = []

@[simp] theorem isEmpty_empty : isEmpty empty := by
  simp [isEmpty, empty]

end Account

namespace WorldState

/-- Account existence as a proposition over `getAccount`. -/
def accountExists (state : WorldState) (addr : Address) : Prop :=
  ∃ account, getAccount state addr = some account

/-- Touch an address by installing `Account.empty` when no account exists. -/
def ensureAccount (state : WorldState) (addr : Address) : WorldState :=
  match getAccount state addr with
  | some _ => state
  | none => setAccount state addr Account.empty

theorem accountExists_iff_getAccount_isSome (state : WorldState) (addr : Address) :
    accountExists state addr ↔ (getAccount state addr).isSome = true := by
  cases h_account : getAccount state addr <;> simp [accountExists, h_account]

@[simp] theorem not_accountExists_empty (addr : Address) :
    ¬ accountExists empty addr := by
  simp [accountExists]

theorem accountExists_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountExists (setAccount state addr account) addr := by
  exact ⟨account, getAccount_setAccount_same state addr account⟩

theorem accountExists_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountExists (setAccount state addr account) other ↔ accountExists state other := by
  simp [accountExists, getAccount_setAccount_ne state account h_ne]

theorem ensureAccount_of_existing
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : getAccount state addr = some account) :
    ensureAccount state addr = state := by
  simp [ensureAccount, h_account]

theorem getAccount_ensureAccount_existing
    {state : WorldState} {addr : Address} {account : Account}
    (h_account : getAccount state addr = some account) :
    getAccount (ensureAccount state addr) addr = some account := by
  simp [ensureAccount, h_account]

theorem getAccount_ensureAccount_missing
    {state : WorldState} {addr : Address}
    (h_missing : getAccount state addr = none) :
    getAccount (ensureAccount state addr) addr = some Account.empty := by
  simp [ensureAccount, h_missing]

theorem accountExists_ensureAccount (state : WorldState) (addr : Address) :
    accountExists (ensureAccount state addr) addr := by
  unfold ensureAccount
  cases h_account : getAccount state addr with
  | none =>
      exact accountExists_setAccount_same state addr Account.empty
  | some account =>
      exact ⟨account, h_account⟩

theorem getAccount_ensureAccount_ne
    (state : WorldState) {addr other : Address} (h_ne : other ≠ addr) :
    getAccount (ensureAccount state addr) other = getAccount state other := by
  unfold ensureAccount
  cases h_account : getAccount state addr with
  | none => exact getAccount_setAccount_ne state Account.empty h_ne
  | some _ => rfl

theorem ensureAccount_idempotent (state : WorldState) (addr : Address) :
    ensureAccount (ensureAccount state addr) addr = ensureAccount state addr := by
  unfold ensureAccount
  cases h_account : getAccount state addr with
  | none =>
      simp [getAccount_setAccount_same]
  | some account =>
      simp [h_account]

end WorldState

end EvmAsm.EL
