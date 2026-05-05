/-
  EvmAsm.EL.TerminatingDataMemory

  Bridge from RETURN/REVERT stack arguments to returned memory bytes (GH #113).
-/

import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingDataMemory

abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev MemoryReader := Nat → Byte

/-- First memory byte consumed as RETURN/REVERT output data. -/
def dataStart (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).offset.toNat

/-- Number of memory bytes consumed as RETURN/REVERT output data. -/
def dataSize (args : TerminatingArgs) : Nat :=
  (TerminatingArgsBridge.dataRange args).size.toNat

/-- RETURN/REVERT data bytes loaded from a pure memory-reader function. -/
def terminatingDataFromMemory
    (readByte : MemoryReader) (args : TerminatingArgs) : List Byte :=
  (List.range (dataSize args)).map (fun i => readByte (dataStart args + i))

/-- Build the terminating call result directly from stack args and memory.
    Distinctive token: TerminatingDataMemory.resultFromMemory. -/
def resultFromMemory
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) : CallResult :=
  TerminatingArgsBridge.mkResultFromArgs
    kind state (terminatingDataFromMemory readByte args) gasRemaining args

theorem dataStart_eq (args : TerminatingArgs) :
    dataStart args = (TerminatingArgsBridge.dataRange args).offset.toNat := rfl

theorem dataSize_eq (args : TerminatingArgs) :
    dataSize args = (TerminatingArgsBridge.dataRange args).size.toNat := rfl

@[simp] theorem terminatingDataFromMemory_length
    (readByte : MemoryReader) (args : TerminatingArgs) :
    (terminatingDataFromMemory readByte args).length = dataSize args := by
  simp [terminatingDataFromMemory]

theorem terminatingDataFromMemory_get
    {readByte : MemoryReader} {args : TerminatingArgs} {i : Nat}
    (h : i < dataSize args) :
    (terminatingDataFromMemory readByte args)[i]'(by
      simpa [terminatingDataFromMemory_length] using h) =
      readByte (dataStart args + i) := by
  simp [terminatingDataFromMemory, List.getElem_map, List.getElem_range]

@[simp] theorem terminatingDataFromMemory_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.returnArgs rangeOffset 0) = [] := rfl

@[simp] theorem terminatingDataFromMemory_revert_zero_size
    (readByte : MemoryReader) (rangeOffset : EvmAsm.Evm64.EvmWord) :
    terminatingDataFromMemory readByte
        (EvmAsm.Evm64.TerminatingArgs.revertArgs rangeOffset 0) = [] := rfl

theorem resultFromMemory_eq
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    resultFromMemory kind state readByte gasRemaining args =
      TerminatingArgsBridge.mkResultFromArgs
        kind state (terminatingDataFromMemory readByte args) gasRemaining args := rfl

theorem resultFromMemory_status
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemory kind state readByte gasRemaining args).status =
      match kind with
      | .stop => .success
      | .return_ => .success
      | .revert => .revert
      | .invalid => .failure
      | .selfdestruct => .success := by
  exact TerminatingArgsBridge.mkResultFromArgs_status
    kind state (terminatingDataFromMemory readByte args) gasRemaining args

theorem resultFromMemory_output
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemory kind state readByte gasRemaining args).output =
      match kind with
      | .stop => []
      | .return_ => terminatingDataFromMemory readByte args
      | .revert => terminatingDataFromMemory readByte args
      | .invalid => []
      | .selfdestruct => [] := by
  exact TerminatingArgsBridge.mkResultFromArgs_output
    kind state (terminatingDataFromMemory readByte args) gasRemaining args

theorem resultFromMemory_return_output
    (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemory .return_ state readByte gasRemaining args).output =
      terminatingDataFromMemory readByte args := rfl

theorem resultFromMemory_revert_output
    (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemory .revert state readByte gasRemaining args).output =
      terminatingDataFromMemory readByte args := rfl

theorem resultFromMemory_gasRemaining
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (args : TerminatingArgs) :
    (resultFromMemory kind state readByte gasRemaining args).gasRemaining =
      gasRemaining := by
  cases kind <;> rfl

end TerminatingDataMemory

end EvmAsm.EL
