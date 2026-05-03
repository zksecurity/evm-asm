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

@[simp] theorem not_isPrecompileAddress_zero :
    ¬ isPrecompileAddress (0 : Address) := by
  unfold isPrecompileAddress
  rw [ofAddress?_zero]
  decide

end Precompile

end EvmAsm.Evm64
