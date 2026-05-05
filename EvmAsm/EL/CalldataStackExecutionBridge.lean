/-
  EvmAsm.EL.CalldataStackExecutionBridge

  Pure stack-execution bridge for CALLDATALOAD, CALLDATASIZE, and
  CALLDATACOPY (GH #104).
-/

import EvmAsm.Evm64.Calldata.LoadArgsStackDecode
import EvmAsm.Evm64.Calldata.CopyArgsStackDecode
import EvmAsm.Evm64.Calldata.Size
import EvmAsm.Evm64.Calldata.CopyExec

namespace EvmAsm.EL

namespace CalldataStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord

inductive Kind where
  | callDataLoad
  | callDataSize
  | callDataCopy
  deriving DecidableEq, Repr

/-- Caller-visible effects of a calldata opcode at the executable-spec layer.
    `copiedBytes` is nonempty only for CALLDATACOPY and is intentionally kept
    separate from a concrete memory model. -/
structure CalldataVisibleEffects where
  stackWords : List EvmWord
  copiedBytes : List (BitVec 8)
  deriving Repr

structure CalldataStackState where
  data : List (BitVec 8)
  stack : List EvmWord
  deriving Repr

structure CalldataStackResult where
  effects : CalldataVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Kind → Nat
  | .callDataLoad => EvmAsm.Evm64.CallDataLoadArgs.stackArgumentCount
  | .callDataSize => 0
  | .callDataCopy => EvmAsm.Evm64.CallDataCopyArgs.stackArgumentCount

def resultCount : Kind → Nat
  | .callDataLoad => EvmAsm.Evm64.CallDataLoadArgs.resultCount
  | .callDataSize => 1
  | .callDataCopy => EvmAsm.Evm64.CallDataCopyArgs.resultCount

def stackRestAfterCalldata? (kind : Kind) (stack : List EvmWord) :
    Option (List EvmWord) :=
  match kind with
  | .callDataLoad =>
      match stack with
      | _offset :: rest => some rest
      | _ => none
  | .callDataSize => some stack
  | .callDataCopy =>
      match stack with
      | _destOffset :: _dataOffset :: _size :: rest => some rest
      | _ => none

/--
Execute the calldata opcode stack transition using existing pure Evm64
decoders and executable calldata helpers.

Distinctive token: CalldataStackExecutionBridge.runCalldataStack? #104.
-/
def runCalldataStack? (kind : Kind) (state : CalldataStackState) :
    Option CalldataStackResult :=
  match kind with
  | .callDataLoad => do
      let args ←
        EvmAsm.Evm64.CallDataLoadArgsStackDecode.decodeCallDataLoadStack?
          state.stack
      let rest ← stackRestAfterCalldata? .callDataLoad state.stack
      some
        { effects :=
            { stackWords :=
                [EvmAsm.Evm64.CallDataLoadArgs.loadedWordFromArgs state.data args]
              copiedBytes := [] }
          stack := rest }
  | .callDataSize =>
      some
        { effects :=
            { stackWords := [EvmAsm.Evm64.Calldata.callDataSizeOf state.data]
              copiedBytes := [] }
          stack := state.stack }
  | .callDataCopy => do
      let args ←
        EvmAsm.Evm64.CallDataCopyArgsStackDecode.decodeCallDataCopyStack?
          state.stack
      let rest ← stackRestAfterCalldata? .callDataCopy state.stack
      some
        { effects :=
            { stackWords := []
              copiedBytes :=
                EvmAsm.Evm64.CallDataCopyExec.copiedBytesFromArgs state.data args }
          stack := rest }

theorem stackRestAfterCalldata?_load
    (offset : EvmWord) (rest : List EvmWord) :
    stackRestAfterCalldata? .callDataLoad (offset :: rest) = some rest := rfl

theorem stackRestAfterCalldata?_size (stack : List EvmWord) :
    stackRestAfterCalldata? .callDataSize stack = some stack := rfl

theorem stackRestAfterCalldata?_copy
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterCalldata? .callDataCopy
      (destOffset :: dataOffset :: size :: rest) = some rest := rfl

theorem runCalldataStack?_load
    (data : List (BitVec 8)) (offset : EvmWord) (rest : List EvmWord) :
    runCalldataStack? .callDataLoad
      { data := data, stack := offset :: rest } =
      some
        { effects :=
            { stackWords :=
                [EvmAsm.Evm64.CallDataLoadArgs.loadedWordFromArgs data
                  (EvmAsm.Evm64.CallDataLoadArgs.loadArgs offset)]
              copiedBytes := [] }
          stack := rest } := rfl

theorem runCalldataStack?_size
    (data : List (BitVec 8)) (stack : List EvmWord) :
    runCalldataStack? .callDataSize { data := data, stack := stack } =
      some
        { effects :=
            { stackWords := [EvmAsm.Evm64.Calldata.callDataSizeOf data]
              copiedBytes := [] }
          stack := stack } := rfl

theorem runCalldataStack?_copy
    (data : List (BitVec 8))
    (destOffset dataOffset size : EvmWord) (rest : List EvmWord) :
    runCalldataStack? .callDataCopy
      { data := data, stack := destOffset :: dataOffset :: size :: rest } =
      some
        { effects :=
            { stackWords := []
              copiedBytes :=
                EvmAsm.Evm64.CallDataCopyExec.copiedBytesFromArgs data
                  (EvmAsm.Evm64.CallDataCopyArgs.copyArgs
                    destOffset dataOffset size) }
          stack := rest } := rfl

theorem runCalldataStack?_load_underflow (data : List (BitVec 8)) :
    runCalldataStack? .callDataLoad { data := data, stack := [] } = none := rfl

theorem runCalldataStack?_copy_underflow_nil (data : List (BitVec 8)) :
    runCalldataStack? .callDataCopy { data := data, stack := [] } = none := rfl

theorem runCalldataStack?_copy_underflow_one
    (data : List (BitVec 8)) (destOffset : EvmWord) :
    runCalldataStack? .callDataCopy { data := data, stack := [destOffset] } =
      none := rfl

theorem runCalldataStack?_copy_underflow_two
    (data : List (BitVec 8)) (destOffset dataOffset : EvmWord) :
    runCalldataStack? .callDataCopy
      { data := data, stack := [destOffset, dataOffset] } = none := rfl

theorem runCalldataStack?_stack_length
    {kind : Kind} {state : CalldataStackState} {out : CalldataStackResult}
    (h_run : runCalldataStack? kind state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount kind =
      state.stack.length + resultCount kind := by
  cases state with
  | mk data stack =>
      cases kind
      · cases stack with
        | nil =>
            simp [runCalldataStack?,
              EvmAsm.Evm64.CallDataLoadArgsStackDecode.decodeCallDataLoadStack?]
              at h_run
        | cons offset rest =>
            simp [runCalldataStack?, stackRestAfterCalldata?] at h_run
            cases h_run
            simp [argumentCount, resultCount,
              EvmAsm.Evm64.CallDataLoadArgs.stackArgumentCount,
              EvmAsm.Evm64.CallDataLoadArgs.resultCount]
      · simp [runCalldataStack?] at h_run
        cases h_run
        simp [argumentCount, resultCount]
      · cases stack with
        | nil =>
            simp [runCalldataStack?,
              EvmAsm.Evm64.CallDataCopyArgsStackDecode.decodeCallDataCopyStack?]
              at h_run
        | cons destOffset tail =>
            cases tail with
            | nil => simp [runCalldataStack?, stackRestAfterCalldata?] at h_run
            | cons dataOffset tail =>
                cases tail with
                | nil => simp [runCalldataStack?, stackRestAfterCalldata?] at h_run
                | cons size rest =>
                    simp [runCalldataStack?, stackRestAfterCalldata?] at h_run
                    cases h_run
                    simp [argumentCount, resultCount,
                      EvmAsm.Evm64.CallDataCopyArgs.stackArgumentCount,
                      EvmAsm.Evm64.CallDataCopyArgs.resultCount]

end CalldataStackExecutionBridge

end EvmAsm.EL
