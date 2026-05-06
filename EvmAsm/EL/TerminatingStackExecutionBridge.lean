/-
  EvmAsm.EL.TerminatingStackExecutionBridge

  Pure stack-to-result bridge for terminating opcodes (GH #113).
-/

import EvmAsm.Evm64.TerminatingArgsStackDecode
import EvmAsm.EL.TerminatingDataMemory

namespace EvmAsm.EL

namespace TerminatingStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args
abbrev MemoryReader := TerminatingDataMemory.MemoryReader

/-- Runtime state visible to the pure terminating-opcode stack bridge. -/
structure TerminatingStackState where
  stack : List EvmWord

structure TerminatingStackResult where
  result : CallResult
  stack : List EvmWord

def stackRestAfterTerminating? :
    TerminatingKind -> List EvmWord -> Option (List EvmWord)
  | .stop, stack => some stack
  | .return_, _offset :: _size :: rest => some rest
  | .revert, _offset :: _size :: rest => some rest
  | .invalid, stack => some stack
  | .selfdestruct, _beneficiary :: rest => some rest
  | _, _ => none

def argsFromStack? : TerminatingKind -> List EvmWord -> Option TerminatingArgs
  | .stop, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .return_, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeReturnStack? stack
  | .revert, stack =>
      EvmAsm.Evm64.TerminatingArgsStackDecode.decodeRevertStack? stack
  | .invalid, _ => some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
  | .selfdestruct, stack =>
      (EvmAsm.Evm64.TerminatingArgsStackDecode.decodeSelfdestructStack? stack).map
        (fun _beneficiary => EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)

/--
Run the pure terminating stack effect: decode opcode-specific stack operands,
read RETURN/REVERT data from memory, package the existing EL terminating
result, and expose the remaining stack after consumption.

Distinctive token: TerminatingStackExecutionBridge.runTerminatingStack? #113.
-/
def runTerminatingStack? (kind : TerminatingKind) (state : WorldState)
    (readByte : MemoryReader) (gasRemaining : Nat) :
    TerminatingStackState -> Option TerminatingStackResult
  | stackState =>
      match argsFromStack? kind stackState.stack,
          stackRestAfterTerminating? kind stackState.stack with
      | some args, some rest =>
          some
            { result :=
                TerminatingDataMemory.resultFromMemory
                  kind state readByte gasRemaining args
              stack := rest }
      | _, _ => none

theorem stackRestAfterTerminating?_stop (stack : List EvmWord) :
    stackRestAfterTerminating? .stop stack = some stack := rfl

theorem stackRestAfterTerminating?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .return_ (offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterTerminating?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .revert (offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterTerminating?_invalid (stack : List EvmWord) :
    stackRestAfterTerminating? .invalid stack = some stack := rfl

theorem stackRestAfterTerminating?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    stackRestAfterTerminating? .selfdestruct (beneficiary :: rest) =
      some rest := rfl

theorem argsFromStack?_return
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .return_ (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs offset size) := rfl

theorem argsFromStack?_revert
    (offset size : EvmWord) (rest : List EvmWord) :
    argsFromStack? .revert (offset :: size :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.revertArgs offset size) := rfl

theorem argsFromStack?_selfdestruct
    (beneficiary : EvmWord) (rest : List EvmWord) :
    argsFromStack? .selfdestruct (beneficiary :: rest) =
      some (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0) := rfl

theorem runTerminatingStack?_stop
    (state : WorldState) (readByte : MemoryReader) (gasRemaining : Nat)
    (stack : List EvmWord) :
    runTerminatingStack? .stop state readByte gasRemaining { stack := stack } =
      some
        { result :=
            TerminatingDataMemory.resultFromMemory .stop state readByte gasRemaining
              (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
          stack := stack } := rfl

theorem runTerminatingStack?_return
    (state : WorldState) (readByte : MemoryReader) (gasRemaining : Nat)
    (offset size : EvmWord) (rest : List EvmWord) :
    runTerminatingStack? .return_ state readByte gasRemaining
        { stack := offset :: size :: rest } =
      some
        { result :=
            TerminatingDataMemory.resultFromMemory .return_ state readByte gasRemaining
              (EvmAsm.Evm64.TerminatingArgs.returnArgs offset size)
          stack := rest } := rfl

theorem runTerminatingStack?_revert
    (state : WorldState) (readByte : MemoryReader) (gasRemaining : Nat)
    (offset size : EvmWord) (rest : List EvmWord) :
    runTerminatingStack? .revert state readByte gasRemaining
        { stack := offset :: size :: rest } =
      some
        { result :=
            TerminatingDataMemory.resultFromMemory .revert state readByte gasRemaining
              (EvmAsm.Evm64.TerminatingArgs.revertArgs offset size)
          stack := rest } := rfl

theorem runTerminatingStack?_invalid
    (state : WorldState) (readByte : MemoryReader) (gasRemaining : Nat)
    (stack : List EvmWord) :
    runTerminatingStack? .invalid state readByte gasRemaining { stack := stack } =
      some
        { result :=
            TerminatingDataMemory.resultFromMemory .invalid state readByte gasRemaining
              (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
          stack := stack } := rfl

theorem runTerminatingStack?_selfdestruct
    (state : WorldState) (readByte : MemoryReader) (gasRemaining : Nat)
    (beneficiary : EvmWord) (rest : List EvmWord) :
    runTerminatingStack? .selfdestruct state readByte gasRemaining
        { stack := beneficiary :: rest } =
      some
        { result :=
            TerminatingDataMemory.resultFromMemory
              .selfdestruct state readByte gasRemaining
              (EvmAsm.Evm64.TerminatingArgs.returnArgs 0 0)
          stack := rest } := rfl

theorem runTerminatingStack?_eq_none_iff
    (kind : TerminatingKind) (state : WorldState) (readByte : MemoryReader)
    (gasRemaining : Nat) (stackState : TerminatingStackState) :
    runTerminatingStack? kind state readByte gasRemaining stackState = none ↔
      argsFromStack? kind stackState.stack = none ∨
        stackRestAfterTerminating? kind stackState.stack = none := by
  cases stackState with
  | mk stack =>
      simp [runTerminatingStack?]
      cases h_args : argsFromStack? kind stack with
      | none => simp
      | some args =>
          cases h_rest : stackRestAfterTerminating? kind stack with
          | none => simp
          | some rest => simp

theorem runTerminatingStack?_stack_length
    {kind : TerminatingKind} {state : WorldState} {readByte : MemoryReader}
    {gasRemaining : Nat} {stackState : TerminatingStackState}
    {out : TerminatingStackResult}
    (h_run :
      runTerminatingStack? kind state readByte gasRemaining stackState = some out) :
    out.stack.length + EvmAsm.Evm64.TerminatingArgs.stackArgumentCount kind =
      stackState.stack.length := by
  cases stackState with
  | mk stack =>
      cases kind
      · simp [runTerminatingStack?, argsFromStack?,
          stackRestAfterTerminating?] at h_run
        cases h_run
        simp [EvmAsm.Evm64.TerminatingArgs.stackArgumentCount]
      · cases stack with
        | nil => simp [runTerminatingStack?, argsFromStack?,
            stackRestAfterTerminating?] at h_run
        | cons offset tail =>
            cases tail with
            | nil => simp [runTerminatingStack?, argsFromStack?,
                stackRestAfterTerminating?] at h_run
            | cons size rest =>
                simp [runTerminatingStack?, argsFromStack?,
                  stackRestAfterTerminating?] at h_run
                cases h_run
                simp [EvmAsm.Evm64.TerminatingArgs.stackArgumentCount]
      · cases stack with
        | nil => simp [runTerminatingStack?, argsFromStack?,
            stackRestAfterTerminating?] at h_run
        | cons offset tail =>
            cases tail with
            | nil => simp [runTerminatingStack?, argsFromStack?,
                stackRestAfterTerminating?] at h_run
            | cons size rest =>
                simp [runTerminatingStack?, argsFromStack?,
                  stackRestAfterTerminating?] at h_run
                cases h_run
                simp [EvmAsm.Evm64.TerminatingArgs.stackArgumentCount]
      · simp [runTerminatingStack?, argsFromStack?,
          stackRestAfterTerminating?] at h_run
        cases h_run
        simp [EvmAsm.Evm64.TerminatingArgs.stackArgumentCount]
      · cases stack with
        | nil => simp [runTerminatingStack?, argsFromStack?,
            stackRestAfterTerminating?] at h_run
        | cons beneficiary rest =>
            simp [runTerminatingStack?, argsFromStack?,
              stackRestAfterTerminating?] at h_run
            cases h_run
            simp [EvmAsm.Evm64.TerminatingArgs.stackArgumentCount]

end TerminatingStackExecutionBridge

end EvmAsm.EL
