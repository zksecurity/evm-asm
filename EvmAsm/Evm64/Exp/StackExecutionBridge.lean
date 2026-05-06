/-
  EvmAsm.Evm64.Exp.StackExecutionBridge

  Pure stack-execution bridge for EXP (GH #92).
-/

import EvmAsm.Evm64.Exp.ArgsStackDecode

namespace EvmAsm.Evm64

namespace ExpStackExecutionBridge

/-- Caller-visible effects of EXP at the executable-spec layer. -/
structure ExpVisibleEffects where
  stackWords : List EvmWord
  dynamicGas : Nat
  totalGas : Nat
  deriving Repr

structure ExpStackState where
  stack : List EvmWord
  deriving Repr

structure ExpStackResult where
  effects : ExpVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := ExpArgs.stackArgumentCount

def resultCount : Nat := ExpArgs.resultCount

def stackRestAfterExp? : List EvmWord → Option (List EvmWord)
  | _base :: _exponent :: rest => some rest
  | _ => none

/--
Execute the EXP stack transition using the pure EXP argument decoder and
the existing word-level EXP result/gas bridge.

Distinctive token: ExpStackExecutionBridge.runExpStack? #92.
-/
def runExpStack? (state : ExpStackState) : Option ExpStackResult := do
  let args ← ExpArgsStackDecode.decodeExpStack? state.stack
  let rest ← stackRestAfterExp? state.stack
  some
    { effects :=
        { stackWords := [ExpArgs.expResultFromArgs args]
          dynamicGas := ExpArgs.expDynamicCostFromArgs args
          totalGas := ExpArgs.expTotalGasFromArgs args }
      stack := rest }

theorem stackRestAfterExp?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    stackRestAfterExp? (base :: exponent :: rest) = some rest := rfl

theorem runExpStack?_cons
    (base exponent : EvmWord) (rest : List EvmWord) :
    runExpStack? { stack := base :: exponent :: rest } =
      some
        { effects :=
            { stackWords := [ExpArgs.expResultFromArgs
                (ExpArgs.expArgs base exponent)]
              dynamicGas := ExpArgs.expDynamicCostFromArgs
                (ExpArgs.expArgs base exponent)
              totalGas := ExpArgs.expTotalGasFromArgs
                (ExpArgs.expArgs base exponent) }
          stack := rest } := rfl

theorem runExpStack?_underflow_nil :
    runExpStack? { stack := [] } = none := rfl

theorem runExpStack?_underflow_one (base : EvmWord) :
    runExpStack? { stack := [base] } = none := rfl

theorem runExpStack?_stack_length
    {state : ExpStackState} {out : ExpStackResult}
    (h_run : runExpStack? state = some out) :
    out.stack.length + out.effects.stackWords.length + argumentCount =
      state.stack.length + resultCount := by
  cases state with
  | mk stack =>
      cases stack with
      | nil =>
          simp [runExpStack?, ExpArgsStackDecode.decodeExpStack?] at h_run
      | cons base tail =>
          cases tail with
          | nil => simp [runExpStack?, stackRestAfterExp?] at h_run
          | cons exponent rest =>
              simp [runExpStack?, stackRestAfterExp?] at h_run
              cases h_run
              simp [argumentCount, resultCount, ExpArgs.stackArgumentCount,
                ExpArgs.resultCount]

theorem runExpStack?_head?
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (ExpArgs.expResultFromArgs
        (ExpArgs.expArgs base exponent))) := rfl

theorem runExpStack?_gas
    (base exponent : EvmWord) (rest : List EvmWord) :
    (runExpStack? { stack := base :: exponent :: rest }).map
      (fun out => (out.effects.dynamicGas, out.effects.totalGas)) =
      some
        ( ExpArgs.expDynamicCostFromArgs (ExpArgs.expArgs base exponent)
        , ExpArgs.expTotalGasFromArgs (ExpArgs.expArgs base exponent)) := rfl

end ExpStackExecutionBridge

end EvmAsm.Evm64
