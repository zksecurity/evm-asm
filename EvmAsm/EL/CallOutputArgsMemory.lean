/-
  EvmAsm.EL.CallOutputArgsMemory

  CALL-family output-memory bridge specialized to stack argument records (GH #114).
-/

import EvmAsm.EL.CallOutputMemory

namespace EvmAsm.EL

namespace CallOutputArgsMemory

abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall
abbrev CallResult := EvmAsm.EL.CallResult
abbrev Byte := EvmAsm.EL.Byte

/-- Byte written by CALL output copying at a caller-memory address.
    Distinctive token: CallOutputArgsMemory.callOutputByteFromArgs #114. -/
def callOutputByteFromArgs (result : CallResult) (args : CallArgs) (addr : Nat) : Byte :=
  CallOutputMemory.callOutputByteAt result args.output addr

def staticCallOutputByteFromArgs
    (result : CallResult) (args : StaticCallArgs) (addr : Nat) : Byte :=
  CallOutputMemory.callOutputByteAt result args.output addr

def delegateCallOutputByteFromArgs
    (result : CallResult) (args : DelegateCallArgs) (addr : Nat) : Byte :=
  CallOutputMemory.callOutputByteAt result args.output addr

theorem callOutputByteFromArgs_eq
    (result : CallResult) (args : CallArgs) (addr : Nat) :
    callOutputByteFromArgs result args addr =
      CallOutputMemory.callOutputByteAt result
        (EvmAsm.EL.CallArgsBridge.callOutputRange args) addr := rfl

theorem staticCallOutputByteFromArgs_eq
    (result : CallResult) (args : StaticCallArgs) (addr : Nat) :
    staticCallOutputByteFromArgs result args addr =
      CallOutputMemory.callOutputByteAt result
        (EvmAsm.EL.CallArgsBridge.staticCallOutputRange args) addr := rfl

theorem delegateCallOutputByteFromArgs_eq
    (result : CallResult) (args : DelegateCallArgs) (addr : Nat) :
    delegateCallOutputByteFromArgs result args addr =
      CallOutputMemory.callOutputByteAt result
        (EvmAsm.EL.CallArgsBridge.delegateCallOutputRange args) addr := rfl

theorem callOutputByteFromArgs_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (args : CallArgs) (addr : Nat) :
    callOutputByteFromArgs
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        args addr = 0 :=
  CallOutputMemory.callOutputByteAt_failure state output gasRemaining args.output addr

theorem staticCallOutputByteFromArgs_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (args : StaticCallArgs) (addr : Nat) :
    staticCallOutputByteFromArgs
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        args addr = 0 :=
  CallOutputMemory.callOutputByteAt_failure state output gasRemaining args.output addr

theorem delegateCallOutputByteFromArgs_failure
    (state : WorldState) (output : List Byte) (gasRemaining : Nat)
    (args : DelegateCallArgs) (addr : Nat) :
    delegateCallOutputByteFromArgs
        { status := .failure, state := state, output := output, gasRemaining := gasRemaining }
        args addr = 0 :=
  CallOutputMemory.callOutputByteAt_failure state output gasRemaining args.output addr

@[simp] theorem callOutputByteFromArgs_zero_size
    (result : CallResult) (args : CallArgs) (addr : Nat)
    (h_size : args.output.size = 0) :
    callOutputByteFromArgs result args addr = 0 := by
  unfold callOutputByteFromArgs
  apply CallOutputMemory.callOutputByteAt_outside
  intro h_addr
  unfold CallOutputMemory.writesOutputAddress CallOutputMemory.outputEnd
    CallOutputMemory.outputStart at h_addr
  rw [h_size] at h_addr
  simp at h_addr
  omega

@[simp] theorem staticCallOutputByteFromArgs_zero_size
    (result : CallResult) (args : StaticCallArgs) (addr : Nat)
    (h_size : args.output.size = 0) :
    staticCallOutputByteFromArgs result args addr = 0 := by
  unfold staticCallOutputByteFromArgs
  apply CallOutputMemory.callOutputByteAt_outside
  intro h_addr
  unfold CallOutputMemory.writesOutputAddress CallOutputMemory.outputEnd
    CallOutputMemory.outputStart at h_addr
  rw [h_size] at h_addr
  simp at h_addr
  omega

@[simp] theorem delegateCallOutputByteFromArgs_zero_size
    (result : CallResult) (args : DelegateCallArgs) (addr : Nat)
    (h_size : args.output.size = 0) :
    delegateCallOutputByteFromArgs result args addr = 0 := by
  unfold delegateCallOutputByteFromArgs
  apply CallOutputMemory.callOutputByteAt_outside
  intro h_addr
  unfold CallOutputMemory.writesOutputAddress CallOutputMemory.outputEnd
    CallOutputMemory.outputStart at h_addr
  rw [h_size] at h_addr
  simp at h_addr
  omega

end CallOutputArgsMemory

end EvmAsm.EL
