/-
  EvmAsm.EL.CallArgsBridge

  Bridge from EVM CALL-family stack arguments to EL message-call frames (GH #114).
-/

import EvmAsm.EL.MessageCall
import EvmAsm.Evm64.CallArgs

namespace EvmAsm.EL

namespace CallArgsBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall

def gasNat (gas : EvmAsm.Evm64.EvmWord) : Nat :=
  gas.toNat

def callInputRange (args : CallArgs) : MemoryRange :=
  args.input

def callOutputRange (args : CallArgs) : MemoryRange :=
  args.output

def staticCallInputRange (args : StaticCallArgs) : MemoryRange :=
  args.input

def staticCallOutputRange (args : StaticCallArgs) : MemoryRange :=
  args.output

def delegateCallInputRange (args : DelegateCallArgs) : MemoryRange :=
  args.input

def delegateCallOutputRange (args : DelegateCallArgs) : MemoryRange :=
  args.output

/-- CALL stack arguments become a value-transferring message-call frame once the
    target word has been decoded to an address and the input bytes are loaded. -/
def callFrame
    (caller callee : Address) (input : List Byte) (isStatic : Bool) (args : CallArgs) :
    CallFrame :=
  CallFrame.forCall caller callee args.value input (gasNat args.gas) isStatic

/-- STATICCALL stack arguments become a static message-call frame. -/
def staticCallFrame
    (caller callee : Address) (input : List Byte) (args : StaticCallArgs) :
    CallFrame :=
  CallFrame.forStaticCall caller callee input (gasNat args.gas)

/-- DELEGATECALL stack arguments inherit the apparent value from the parent
    frame while transferring no new value. -/
def delegateCallFrame
    (caller callee : Address) (apparentValue : Word256) (input : List Byte)
    (isStatic : Bool) (args : DelegateCallArgs) :
    CallFrame :=
  CallFrame.forDelegateCall caller callee apparentValue input (gasNat args.gas) isStatic

theorem callFrameKind
    (caller callee : Address) (input : List Byte) (isStatic : Bool) (args : CallArgs) :
    (callFrame caller callee input isStatic args).kind = .call := rfl

theorem callFrameTransferredValue
    (caller callee : Address) (input : List Byte) (isStatic : Bool) (args : CallArgs) :
    (callFrame caller callee input isStatic args).transferredValue = args.value := rfl

theorem callFrameGas
    (caller callee : Address) (input : List Byte) (isStatic : Bool) (args : CallArgs) :
    (callFrame caller callee input isStatic args).gas = gasNat args.gas := rfl

theorem staticCallFrameKind
    (caller callee : Address) (input : List Byte) (args : StaticCallArgs) :
    (staticCallFrame caller callee input args).kind = .staticcall := rfl

theorem staticCallFrameIsStatic
    (caller callee : Address) (input : List Byte) (args : StaticCallArgs) :
    (staticCallFrame caller callee input args).isStatic = true := rfl

theorem staticCallFrameTransferredValue
    (caller callee : Address) (input : List Byte) (args : StaticCallArgs) :
    (staticCallFrame caller callee input args).transferredValue = 0 := rfl

theorem delegateCallFrameKind
    (caller callee : Address) (apparentValue : Word256) (input : List Byte)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrame caller callee apparentValue input isStatic args).kind = .delegatecall := rfl

theorem delegateCallFrameApparentValue
    (caller callee : Address) (apparentValue : Word256) (input : List Byte)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrame caller callee apparentValue input isStatic args).apparentValue =
      apparentValue := rfl

theorem delegateCallFrameTransferredValue
    (caller callee : Address) (apparentValue : Word256) (input : List Byte)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrame caller callee apparentValue input isStatic args).transferredValue = 0 := rfl

end CallArgsBridge

end EvmAsm.EL
