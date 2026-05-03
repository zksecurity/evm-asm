/-
  EvmAsm.EL.WorldState

  Pure Ethereum world-state model (GH #123 slice 1). This module deliberately
  has no RISC-V dependency; later Evm64 storage/syscall slices can bridge this
  model to concrete ECALL interfaces and separation-logic assertions.
-/

namespace EvmAsm.EL

abbrev Byte := BitVec 8
abbrev Address := BitVec 160
abbrev Word256 := BitVec 256
abbrev Hash256 := BitVec 256
abbrev StorageKey := Word256

/-- Ethereum account data relevant to the execution layer. Code bytes are kept
    with the account so CREATE/CALL-family slices can relate code hashes to the
    executable code region later. -/
structure Account where
  nonce : Nat
  balance : Word256
  storageRoot : Hash256
  codeHash : Hash256
  code : List Byte
  deriving Repr

/-- Pure world state: account existence plus per-account storage slots. Missing
    storage slots read as zero through `getStorage`. -/
structure WorldState where
  accounts : Address → Option Account
  storage : Address → StorageKey → Word256

namespace WorldState

def empty : WorldState :=
  { accounts := fun _ => none
    storage := fun _ _ => 0 }

def getAccount (state : WorldState) (addr : Address) : Option Account :=
  state.accounts addr

def setAccount (state : WorldState) (addr : Address) (account : Account) : WorldState :=
  { state with accounts := fun addr' => if addr' = addr then some account else state.accounts addr' }

def deleteAccount (state : WorldState) (addr : Address) : WorldState :=
  { state with accounts := fun addr' => if addr' = addr then none else state.accounts addr' }

/-- Read an account's code bytes when the account exists. -/
def accountCode? (state : WorldState) (addr : Address) : Option (List Byte) :=
  (getAccount state addr).map (fun account => account.code)

/-- Read an account's code hash when the account exists. -/
def accountCodeHash? (state : WorldState) (addr : Address) : Option Hash256 :=
  (getAccount state addr).map (fun account => account.codeHash)

/-- Update an existing account's code bytes and code hash. Missing accounts are unchanged. -/
def setAccountCode
    (state : WorldState) (addr : Address) (codeHash : Hash256) (code : List Byte) :
    WorldState :=
  match getAccount state addr with
  | none => state
  | some account => setAccount state addr { account with codeHash := codeHash, code := code }

def getStorage (state : WorldState) (addr : Address) (key : StorageKey) : Word256 :=
  state.storage addr key

def setStorage
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    WorldState :=
  { state with storage := fun addr' key' =>
      if addr' = addr then
        if key' = key then value else state.storage addr' key'
      else
        state.storage addr' key' }

@[simp] theorem getAccount_empty (addr : Address) :
    getAccount empty addr = none := rfl

@[simp] theorem getStorage_empty (addr : Address) (key : StorageKey) :
    getStorage empty addr key = 0 := rfl

@[simp] theorem getAccount_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    getAccount (setAccount state addr account) addr = some account := by
  simp [getAccount, setAccount]

theorem getAccount_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    getAccount (setAccount state addr account) other = getAccount state other := by
  simp [getAccount, setAccount, h_ne]

@[simp] theorem getAccount_deleteAccount_same
    (state : WorldState) (addr : Address) :
    getAccount (deleteAccount state addr) addr = none := by
  simp [getAccount, deleteAccount]

theorem getAccount_deleteAccount_ne
    (state : WorldState) {addr other : Address} (h_ne : other ≠ addr) :
    getAccount (deleteAccount state addr) other = getAccount state other := by
  simp [getAccount, deleteAccount, h_ne]

@[simp] theorem accountCode?_empty (addr : Address) :
    accountCode? empty addr = none := rfl

@[simp] theorem accountCodeHash?_empty (addr : Address) :
    accountCodeHash? empty addr = none := rfl

@[simp] theorem accountCode?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountCode? (setAccount state addr account) addr = some account.code := by
  simp [accountCode?]

@[simp] theorem accountCodeHash?_setAccount_same
    (state : WorldState) (addr : Address) (account : Account) :
    accountCodeHash? (setAccount state addr account) addr = some account.codeHash := by
  simp [accountCodeHash?]

theorem accountCode?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountCode? (setAccount state addr account) other = accountCode? state other := by
  simp [accountCode?, getAccount_setAccount_ne, h_ne]

theorem accountCodeHash?_setAccount_ne
    (state : WorldState) {addr other : Address} (account : Account)
    (h_ne : other ≠ addr) :
    accountCodeHash? (setAccount state addr account) other = accountCodeHash? state other := by
  simp [accountCodeHash?, getAccount_setAccount_ne, h_ne]

theorem setAccountCode_of_missing
    {state : WorldState} {addr : Address} (codeHash : Hash256) (code : List Byte)
    (h_missing : getAccount state addr = none) :
    setAccountCode state addr codeHash code = state := by
  simp [setAccountCode, h_missing]

theorem getAccount_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    getAccount (setAccountCode state addr codeHash code) addr =
      some { account with codeHash := codeHash, code := code } := by
  simp [setAccountCode, h_account]

theorem accountCode?_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    accountCode? (setAccountCode state addr codeHash code) addr = some code := by
  simp [accountCode?, getAccount_setAccountCode_same codeHash code h_account]

theorem accountCodeHash?_setAccountCode_same
    {state : WorldState} {addr : Address} {account : Account}
    (codeHash : Hash256) (code : List Byte)
    (h_account : getAccount state addr = some account) :
    accountCodeHash? (setAccountCode state addr codeHash code) addr = some codeHash := by
  simp [accountCodeHash?, getAccount_setAccountCode_same codeHash code h_account]

theorem getAccount_setAccountCode_ne
    (state : WorldState) {addr other : Address} (codeHash : Hash256) (code : List Byte)
    (h_ne : other ≠ addr) :
    getAccount (setAccountCode state addr codeHash code) other = getAccount state other := by
  unfold setAccountCode
  cases h_account : getAccount state addr <;>
    simp [getAccount_setAccount_ne, h_ne]

@[simp] theorem getStorage_setStorage_same
    (state : WorldState) (addr : Address) (key : StorageKey) (value : Word256) :
    getStorage (setStorage state addr key value) addr key = value := by
  simp [getStorage, setStorage]

theorem getStorage_setStorage_addr_ne
    (state : WorldState) {addr other : Address} (key key' : StorageKey) (value : Word256)
    (h_ne : other ≠ addr) :
    getStorage (setStorage state addr key value) other key' =
      getStorage state other key' := by
  simp [getStorage, setStorage, h_ne]

theorem getStorage_setStorage_key_ne
    (state : WorldState) (addr : Address) {key other : StorageKey} (value : Word256)
    (h_ne : other ≠ key) :
    getStorage (setStorage state addr key value) addr other =
      getStorage state addr other := by
  simp [getStorage, setStorage, h_ne]

end WorldState

end EvmAsm.EL
