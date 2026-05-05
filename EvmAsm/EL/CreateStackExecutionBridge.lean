/-
  EvmAsm.EL.CreateStackExecutionBridge

  Pure stack-to-execution bridge for CREATE and CREATE2 (GH #115).
-/

import EvmAsm.Evm64.CreateArgsStackDecode
import EvmAsm.EL.CreateInitcodeBridge
import EvmAsm.EL.CreateResultBridge

namespace EvmAsm.EL

namespace CreateStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CreateKind := EvmAsm.Evm64.CreateArgs.Kind
abbrev Decoded := EvmAsm.Evm64.CreateArgsStackDecode.Decoded
abbrev MemoryReader := CreateInitcodeBridge.MemoryReader
abbrev Executor := CreateRequest -> CreateResult

/-- Runtime state visible to the pure CREATE stack bridge. -/
structure CreateStackState where
  stack : List EvmWord

def stackRestAfterCreate? (kind : CreateKind) : List EvmWord -> Option (List EvmWord)
  | _value :: _offset :: _size :: rest =>
      match kind with
      | .create => some rest
      | .create2 =>
          match rest with
          | _salt :: rest => some rest
          | _ => none
  | _ => none

def requestFromDecoded
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord) :
    Decoded -> CreateRequest
  | .create args =>
      CreateInitcodeBridge.createRequestFromMemory creator readByte gas args
  | .create2 args =>
      CreateInitcodeBridge.create2RequestFromMemory creator readByte gas args

def requestFromStack? (kind : CreateKind) (creator : Address)
    (readByte : MemoryReader) (gas : EvmWord) (stack : List EvmWord) :
    Option CreateRequest :=
  (EvmAsm.Evm64.CreateArgsStackDecode.decodeCreateStack? kind stack).map
    (requestFromDecoded creator readByte gas)

/--
Run the pure CREATE-family stack effect: decode stack operands, frame the
initcode memory slice into an EL request, run the abstract creation executor,
and push the CREATE result word over the remaining stack.

Distinctive token: CreateStackExecutionBridge.runCreateStack? #115.
-/
def runCreateStack? (kind : CreateKind) (creator : Address)
    (readByte : MemoryReader) (gas : EvmWord) (executor : Executor) :
    CreateStackState -> Option CreateStackState
  | state =>
      match requestFromStack? kind creator readByte gas state.stack,
          stackRestAfterCreate? kind state.stack with
      | some request, some rest =>
          some
            { stack :=
                CreateResultBridge.createResultStackWord (executor request) :: rest }
      | _, _ => none

theorem stackRestAfterCreate?_create
    (value offset size : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create (value :: offset :: size :: rest) =
      some rest := rfl

theorem stackRestAfterCreate?_create2
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    stackRestAfterCreate? .create2 (value :: offset :: size :: salt :: rest) =
      some rest := rfl

@[simp] theorem stackRestAfterCreate?_nil (kind : CreateKind) :
    stackRestAfterCreate? kind [] = none := rfl

@[simp] theorem stackRestAfterCreate?_singleton
    (kind : CreateKind) (value : EvmWord) :
    stackRestAfterCreate? kind [value] = none := rfl

theorem requestFromStack?_create
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (value offset size : EvmWord) (rest : List EvmWord) :
    requestFromStack? .create creator readByte gas
        (value :: offset :: size :: rest) =
      some
        (CreateInitcodeBridge.createRequestFromMemory creator readByte gas
          (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate value offset size)) := rfl

theorem requestFromStack?_create2
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (value offset size salt : EvmWord) (rest : List EvmWord) :
    requestFromStack? .create2 creator readByte gas
        (value :: offset :: size :: salt :: rest) =
      some
        (CreateInitcodeBridge.create2RequestFromMemory creator readByte gas
          (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate2 value offset size salt)) := rfl

theorem runCreateStack?_create
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (executor : Executor) (value offset size : EvmWord) (rest : List EvmWord) :
    runCreateStack? .create creator readByte gas executor
        { stack := value :: offset :: size :: rest } =
      some
        { stack :=
            CreateResultBridge.createResultStackWord
              (executor
                (CreateInitcodeBridge.createRequestFromMemory creator readByte gas
                  (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate value offset size))) ::
              rest } := rfl

theorem runCreateStack?_create2
    (creator : Address) (readByte : MemoryReader) (gas : EvmWord)
    (executor : Executor) (value offset size salt : EvmWord) (rest : List EvmWord) :
    runCreateStack? .create2 creator readByte gas executor
        { stack := value :: offset :: size :: salt :: rest } =
      some
        { stack :=
            CreateResultBridge.createResultStackWord
              (executor
                (CreateInitcodeBridge.create2RequestFromMemory creator readByte gas
                  (EvmAsm.Evm64.CreateArgsStackDecode.mkCreate2
                    value offset size salt))) ::
              rest } := rfl

theorem runCreateStack?_stack_length
    {kind : CreateKind} {creator : Address} {readByte : MemoryReader}
    {gas : EvmWord} {executor : Executor} {state out : CreateStackState}
    (h_run : runCreateStack? kind creator readByte gas executor state = some out) :
    out.stack.length + EvmAsm.Evm64.CreateArgs.argumentCount kind =
      state.stack.length + EvmAsm.Evm64.CreateArgs.resultCount kind := by
  cases state with
  | mk stack =>
      cases kind
      · cases stack with
        | nil => simp [runCreateStack?] at h_run
        | cons value tail =>
            cases tail with
            | nil => simp [runCreateStack?, stackRestAfterCreate?] at h_run
            | cons offset tail =>
                cases tail with
                | nil => simp [runCreateStack?, stackRestAfterCreate?] at h_run
                | cons size rest =>
                    simp [runCreateStack?, requestFromStack?, stackRestAfterCreate?] at h_run
                    cases h_run
                    simp [EvmAsm.Evm64.CreateArgs.argumentCount,
                      EvmAsm.Evm64.CreateArgs.resultCount]
      · cases stack with
        | nil => simp [runCreateStack?] at h_run
        | cons value tail =>
            cases tail with
            | nil => simp [runCreateStack?, stackRestAfterCreate?] at h_run
            | cons offset tail =>
                cases tail with
                | nil => simp [runCreateStack?, stackRestAfterCreate?] at h_run
                | cons size tail =>
                    cases tail with
                    | nil => simp [runCreateStack?, stackRestAfterCreate?] at h_run
                    | cons salt rest =>
                        simp [runCreateStack?, requestFromStack?,
                          stackRestAfterCreate?] at h_run
                        cases h_run
                        simp [EvmAsm.Evm64.CreateArgs.argumentCount,
                          EvmAsm.Evm64.CreateArgs.resultCount]

end CreateStackExecutionBridge

end EvmAsm.EL
