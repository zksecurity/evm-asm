/-
  EvmAsm.EL.CallInputBridge

  Bridge from CALL-family input stack ranges to memory bytes (GH #114).
-/

import EvmAsm.EL.CallArgsBridge

namespace EvmAsm.EL

namespace CallInputBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange
abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall
abbrev MemoryReader := Nat → Byte

/-- First memory byte consumed as CALL-family input data. -/
def inputStart (range : MemoryRange) : Nat :=
  range.offset.toNat

/-- Number of memory bytes consumed as CALL-family input data. -/
def inputSize (range : MemoryRange) : Nat :=
  range.size.toNat

/-- CALL-family input bytes loaded from a pure memory-reader function.
    Distinctive token: CallInputBridge.inputFromMemory #114. -/
def inputFromMemory (readByte : MemoryReader) (range : MemoryRange) : List Byte :=
  (List.range (inputSize range)).map (fun i => readByte (inputStart range + i))

def callInputFromMemory (readByte : MemoryReader) (args : CallArgs) : List Byte :=
  inputFromMemory readByte (CallArgsBridge.callInputRange args)

def staticCallInputFromMemory (readByte : MemoryReader) (args : StaticCallArgs) : List Byte :=
  inputFromMemory readByte (CallArgsBridge.staticCallInputRange args)

def delegateCallInputFromMemory (readByte : MemoryReader) (args : DelegateCallArgs) : List Byte :=
  inputFromMemory readByte (CallArgsBridge.delegateCallInputRange args)

/-- Build a CALL frame directly from stack args and a pure memory reader.
    Distinctive token: CallInputBridge.callFrameFromMemory #114. -/
def callFrameFromMemory
    (caller callee : Address) (readByte : MemoryReader) (isStatic : Bool)
    (args : CallArgs) : CallFrame :=
  CallArgsBridge.callFrame caller callee (callInputFromMemory readByte args) isStatic args

def staticCallFrameFromMemory
    (caller callee : Address) (readByte : MemoryReader) (args : StaticCallArgs) :
    CallFrame :=
  CallArgsBridge.staticCallFrame caller callee (staticCallInputFromMemory readByte args) args

def delegateCallFrameFromMemory
    (caller callee : Address) (apparentValue : Word256) (readByte : MemoryReader)
    (isStatic : Bool) (args : DelegateCallArgs) : CallFrame :=
  CallArgsBridge.delegateCallFrame caller callee apparentValue
    (delegateCallInputFromMemory readByte args) isStatic args

theorem inputStart_eq (range : MemoryRange) :
    inputStart range = range.offset.toNat := rfl

theorem inputSize_eq (range : MemoryRange) :
    inputSize range = range.size.toNat := rfl

@[simp] theorem inputFromMemory_length (readByte : MemoryReader) (range : MemoryRange) :
    (inputFromMemory readByte range).length = inputSize range := by
  simp [inputFromMemory]

theorem inputFromMemory_get
    {readByte : MemoryReader} {range : MemoryRange} {i : Nat}
    (h : i < inputSize range) :
    (inputFromMemory readByte range)[i]'(by
      simpa [inputFromMemory_length] using h) =
      readByte (inputStart range + i) := by
  simp [inputFromMemory, List.getElem_map, List.getElem_range]

@[simp] theorem inputFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    inputFromMemory readByte { offset := rangeOffset, size := 0 } = [] := rfl

theorem callInputFromMemory_eq
    (readByte : MemoryReader) (args : CallArgs) :
    callInputFromMemory readByte args =
      inputFromMemory readByte args.input := rfl

theorem staticCallInputFromMemory_eq
    (readByte : MemoryReader) (args : StaticCallArgs) :
    staticCallInputFromMemory readByte args =
      inputFromMemory readByte args.input := rfl

theorem delegateCallInputFromMemory_eq
    (readByte : MemoryReader) (args : DelegateCallArgs) :
    delegateCallInputFromMemory readByte args =
      inputFromMemory readByte args.input := rfl

theorem callFrameFromMemoryInput
    (caller callee : Address) (readByte : MemoryReader) (isStatic : Bool)
    (args : CallArgs) :
    (callFrameFromMemory caller callee readByte isStatic args).input =
      callInputFromMemory readByte args := rfl

theorem staticCallFrameFromMemoryInput
    (caller callee : Address) (readByte : MemoryReader) (args : StaticCallArgs) :
    (staticCallFrameFromMemory caller callee readByte args).input =
      staticCallInputFromMemory readByte args := rfl

theorem delegateCallFrameFromMemoryInput
    (caller callee : Address) (apparentValue : Word256) (readByte : MemoryReader)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrameFromMemory caller callee apparentValue readByte isStatic args).input =
      delegateCallInputFromMemory readByte args := rfl

theorem callFrameFromMemoryKind
    (caller callee : Address) (readByte : MemoryReader) (isStatic : Bool)
    (args : CallArgs) :
    (callFrameFromMemory caller callee readByte isStatic args).kind = .call := rfl

theorem staticCallFrameFromMemoryKind
    (caller callee : Address) (readByte : MemoryReader) (args : StaticCallArgs) :
    (staticCallFrameFromMemory caller callee readByte args).kind = .staticcall := rfl

theorem delegateCallFrameFromMemoryKind
    (caller callee : Address) (apparentValue : Word256) (readByte : MemoryReader)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrameFromMemory caller callee apparentValue readByte isStatic args).kind =
      .delegatecall := rfl

theorem staticCallFrameFromMemoryIsStatic
    (caller callee : Address) (readByte : MemoryReader) (args : StaticCallArgs) :
    (staticCallFrameFromMemory caller callee readByte args).isStatic = true := rfl

theorem delegateCallFrameFromMemoryApparentValue
    (caller callee : Address) (apparentValue : Word256) (readByte : MemoryReader)
    (isStatic : Bool) (args : DelegateCallArgs) :
    (delegateCallFrameFromMemory caller callee apparentValue readByte isStatic args).apparentValue =
      apparentValue := rfl

end CallInputBridge

end EvmAsm.EL
