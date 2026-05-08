/-
  EvmAsm.Evm64.SDiv.StackExecutionBridge

  Pure stack-execution bridge for SDIV (GH #90).
-/

import EvmAsm.Evm64.SDiv.ArgsStackDecode

namespace EvmAsm.Evm64
namespace SDivStackExecutionBridge

/-- Caller-visible stack effects of SDIV at the executable-spec layer. -/
structure SDivVisibleEffects where
  stackWords : List EvmWord
  deriving Repr

structure SDivStackState where
  stack : List EvmWord
  deriving Repr

structure SDivStackResult where
  effects : SDivVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := SDivArgs.stackArgumentCount

def resultCount : Nat := SDivArgs.resultCount

def stackRestAfterSDiv? : List EvmWord → Option (List EvmWord)
  | _dividend :: _divisor :: rest => some rest
  | _ => none

/-- Execute the SDIV stack transition using the pure argument decoder. -/
def runSDivStack? (state : SDivStackState) : Option SDivStackResult := do
  let args ← SDivArgsStackDecode.decodeSDivStack? state.stack
  let rest ← stackRestAfterSDiv? state.stack
  some
    { effects := { stackWords := [SDivArgs.sdivResultFromArgs args] }
      stack := rest }

theorem stackRestAfterSDiv?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    stackRestAfterSDiv? (dividend :: divisor :: rest) = some rest := rfl

theorem runSDivStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    runSDivStack? { stack := dividend :: divisor :: rest } =
      some
        { effects :=
            { stackWords := [SDivArgs.sdivResultFromArgs
                (SDivArgs.sdivArgs dividend divisor)] }
          stack := rest } := rfl

theorem runSDivStack?_underflow_nil :
    runSDivStack? { stack := [] } = none := rfl

theorem runSDivStack?_underflow_one (dividend : EvmWord) :
    runSDivStack? { stack := [dividend] } = none := rfl

theorem stackRestAfterSDiv?_none_of_empty :
    stackRestAfterSDiv? [] = none := rfl

theorem stackRestAfterSDiv?_none_of_one
    (dividend : EvmWord) :
    stackRestAfterSDiv? [dividend] = none := rfl

theorem runSDivStack?_head?
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (runSDivStack? { stack := dividend :: divisor :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (SDivArgs.sdivResultFromArgs
        (SDivArgs.sdivArgs dividend divisor))) := rfl

theorem runSDivStack?_zero_divisor
    (dividend : EvmWord) (rest : List EvmWord) :
    runSDivStack? { stack := dividend :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_zero_divisor]

theorem runSDivStack?_intMin_neg_one
    (rest : List EvmWord) :
    runSDivStack? { stack := BitVec.intMin 256 :: (-1 : EvmWord) :: rest } =
      some { effects := { stackWords := [BitVec.intMin 256] }, stack := rest } := by
  rw [runSDivStack?_cons]
  rw [SDivArgs.sdivResultFromArgs_intMin_neg_one]

end SDivStackExecutionBridge
end EvmAsm.Evm64
