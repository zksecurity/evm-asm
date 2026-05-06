/-
  EvmAsm.Evm64.Precompile

  Pure precompile-address registry for GH #116.
-/

import EvmAsm.Evm64.Environment

namespace EvmAsm.Evm64

/-- Canonical Ethereum precompiles targeted by the dispatch/accelerator bridge. -/
inductive Precompile where
  | ecrecover
  | sha256
  | ripemd160
  | identity
  | modexp
  | bn254Add
  | bn254Mul
  | bn254Pairing
  | blake2f
  | pointEvaluation
  deriving DecidableEq, Repr

namespace Precompile

/-- Canonical EVM account address for each precompile. -/
def address : Precompile → Address
  | ecrecover => 0x01
  | sha256 => 0x02
  | ripemd160 => 0x03
  | identity => 0x04
  | modexp => 0x05
  | bn254Add => 0x06
  | bn254Mul => 0x07
  | bn254Pairing => 0x08
  | blake2f => 0x09
  | pointEvaluation => 0x0a

/-- Decode a canonical precompile account address. -/
def ofAddress? (addr : Address) : Option Precompile :=
  if addr = (0x01 : Address) then some ecrecover
  else if addr = (0x02 : Address) then some sha256
  else if addr = (0x03 : Address) then some ripemd160
  else if addr = (0x04 : Address) then some identity
  else if addr = (0x05 : Address) then some modexp
  else if addr = (0x06 : Address) then some bn254Add
  else if addr = (0x07 : Address) then some bn254Mul
  else if addr = (0x08 : Address) then some bn254Pairing
  else if addr = (0x09 : Address) then some blake2f
  else if addr = (0x0a : Address) then some pointEvaluation
  else none

/-- Predicate form for CALL-family dispatch. -/
def isPrecompileAddress (addr : Address) : Prop :=
  (ofAddress? addr).isSome

/-- Gas-shape classification for precompile dispatch. Some precompiles need
    richer inputs than a byte length; those are represented as hooks for later
    syscall/executable-spec bridges. -/
inductive GasSchedule where
  | fixed (cost : Nat)
  | wordLinear (base perWord : Nat)
  | pairing (base perPair : Nat)
  | modexp
  | blake2f
  deriving DecidableEq, Repr

/-- Number of 32-byte EVM words needed to cover an input byte length. -/
def inputWords (inputLen : Nat) : Nat :=
  (inputLen + 31) / 32

/-- Number of 192-byte BN254 pairing tuples in an input payload. -/
def pairingPairs (inputLen : Nat) : Nat :=
  inputLen / 192

/-- Gas schedule for canonical precompile entry points. -/
def gasSchedule : Precompile → GasSchedule
  | ecrecover => .fixed 3000
  | sha256 => .wordLinear 60 12
  | ripemd160 => .wordLinear 600 120
  | identity => .wordLinear 15 3
  | modexp => .modexp
  | bn254Add => .fixed 150
  | bn254Mul => .fixed 6000
  | bn254Pairing => .pairing 45000 34000
  | blake2f => .blake2f
  | pointEvaluation => .fixed 50000

/-- Byte-length-only gas cost when the precompile schedule can be determined
    without decoding the input payload. -/
def precompileGasCost? (p : Precompile) (inputLen : Nat) : Option Nat :=
  match gasSchedule p with
  | .fixed cost => some cost
  | .wordLinear base perWord => some (base + perWord * inputWords inputLen)
  | .pairing base perPair => some (base + perPair * pairingPairs inputLen)
  | .modexp => none
  | .blake2f => none

/-- Blake2f gas is parameterized by the rounds field decoded from the payload. -/
def blake2fGas (rounds : Nat) : Nat :=
  rounds

theorem ofAddress?_address (p : Precompile) :
    ofAddress? p.address = some p := by
  cases p <;> native_decide

theorem ofAddress?_zero :
    ofAddress? (0 : Address) = none := by
  native_decide

theorem ofAddress?_eleven :
    ofAddress? (0x0b : Address) = none := by
  native_decide

theorem isPrecompileAddress_address (p : Precompile) :
    isPrecompileAddress p.address := by
  unfold isPrecompileAddress
  rw [ofAddress?_address p]
  simp

theorem isPrecompileAddress_iff_exists {addr : Address} :
    isPrecompileAddress addr ↔ ∃ p, ofAddress? addr = some p := by
  unfold isPrecompileAddress
  cases h_decode : ofAddress? addr with
  | none =>
      simp
  | some p =>
      simp

theorem not_isPrecompileAddress_iff_none {addr : Address} :
    ¬ isPrecompileAddress addr ↔ ofAddress? addr = none := by
  unfold isPrecompileAddress
  cases ofAddress? addr <;> simp

theorem inputWords_zero : inputWords 0 = 0 := rfl

theorem inputWords_thirty_three : inputWords 33 = 2 := rfl

theorem pairingPairs_one : pairingPairs 192 = 1 := rfl

theorem gasSchedule_sha256 :
    gasSchedule sha256 = .wordLinear 60 12 := rfl

theorem precompileGasCost?_identity_64 :
    precompileGasCost? identity 64 = some 21 := rfl

theorem precompileGasCost?_sha256_33 :
    precompileGasCost? sha256 33 = some 84 := rfl

theorem precompileGasCost?_modexp_none (inputLen : Nat) :
    precompileGasCost? modexp inputLen = none := rfl

theorem precompileGasCost?_blake2f_none (inputLen : Nat) :
    precompileGasCost? blake2f inputLen = none := rfl

theorem precompileGasCost?_eq_none_iff (p : Precompile) (inputLen : Nat) :
    precompileGasCost? p inputLen = none ↔ p = modexp ∨ p = blake2f := by
  cases p <;> simp [precompileGasCost?, gasSchedule]

theorem blake2fGas_eq_rounds (rounds : Nat) :
    blake2fGas rounds = rounds := rfl

@[simp] theorem not_isPrecompileAddress_zero :
    ¬ isPrecompileAddress (0 : Address) := by
  unfold isPrecompileAddress
  rw [ofAddress?_zero]
  decide

end Precompile

end EvmAsm.Evm64
