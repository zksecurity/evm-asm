/-
  EvmAsm.EL.WorldStateFrame

  Frame lemmas for independent account and storage updates (GH #123).
-/

import EvmAsm.EL.WorldState

namespace EvmAsm.EL

namespace WorldState

/-- Storage writes do not change account lookup.
    Distinctive token: WorldStateFrame.getAccount_setStorage #123. -/
theorem getAccount_setStorage
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    getAccount (setStorage state storageAddr key value) addr = getAccount state addr := rfl

theorem accountCode?_setStorage
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    accountCode? (setStorage state storageAddr key value) addr = accountCode? state addr := rfl

theorem accountCodeHash?_setStorage
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    accountCodeHash? (setStorage state storageAddr key value) addr =
      accountCodeHash? state addr := rfl

theorem accountBalance?_setStorage
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    accountBalance? (setStorage state storageAddr key value) addr =
      accountBalance? state addr := rfl

theorem accountNonce?_setStorage
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) (value : Word256) :
    accountNonce? (setStorage state storageAddr key value) addr = accountNonce? state addr := rfl

/-- Account writes do not change storage lookup. -/
theorem getStorage_setAccount
    (state : WorldState) (addr storageAddr : Address) (account : Account) (key : StorageKey) :
    getStorage (setAccount state addr account) storageAddr key =
      getStorage state storageAddr key := rfl

theorem getStorage_deleteAccount
    (state : WorldState) (addr storageAddr : Address) (key : StorageKey) :
    getStorage (deleteAccount state addr) storageAddr key =
      getStorage state storageAddr key := rfl

theorem getStorage_setAccountCode
    (state : WorldState) (addr storageAddr : Address) (codeHash : Hash256) (code : List Byte)
    (key : StorageKey) :
    getStorage (setAccountCode state addr codeHash code) storageAddr key =
      getStorage state storageAddr key := by
  unfold setAccountCode
  cases getAccount state addr <;> rfl

theorem getStorage_setAccountBalance
    (state : WorldState) (addr storageAddr : Address) (balance : Word256) (key : StorageKey) :
    getStorage (setAccountBalance state addr balance) storageAddr key =
      getStorage state storageAddr key := by
  unfold setAccountBalance
  cases getAccount state addr <;> rfl

theorem getStorage_setAccountNonce
    (state : WorldState) (addr storageAddr : Address) (nonce : Nat) (key : StorageKey) :
    getStorage (setAccountNonce state addr nonce) storageAddr key =
      getStorage state storageAddr key := by
  unfold setAccountNonce
  cases getAccount state addr <;> rfl

end WorldState

end EvmAsm.EL
