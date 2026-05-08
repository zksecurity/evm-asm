/-
  EvmAsm.Evm64.SMod.StackExecutionBridge

  Pure stack-execution bridge for SMOD (GH #90).
-/

import EvmAsm.Evm64.SMod.ArgsStackDecode

namespace EvmAsm.Evm64
namespace SModStackExecutionBridge

/-- Caller-visible stack effects of SMOD at the executable-spec layer. -/
structure SModVisibleEffects where
  stackWords : List EvmWord
  deriving Repr

structure SModStackState where
  stack : List EvmWord
  deriving Repr

structure SModStackResult where
  effects : SModVisibleEffects
  stack : List EvmWord
  deriving Repr

def argumentCount : Nat := SModArgs.stackArgumentCount

def resultCount : Nat := SModArgs.resultCount

def stackRestAfterSMod? : List EvmWord → Option (List EvmWord)
  | _dividend :: _divisor :: rest => some rest
  | _ => none

/-- Execute the SMOD stack transition using the pure argument decoder. -/
def runSModStack? (state : SModStackState) : Option SModStackResult := do
  let args ← SModArgsStackDecode.decodeSModStack? state.stack
  let rest ← stackRestAfterSMod? state.stack
  some
    { effects := { stackWords := [SModArgs.smodResultFromArgs args] }
      stack := rest }

theorem stackRestAfterSMod?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    stackRestAfterSMod? (dividend :: divisor :: rest) = some rest := rfl

theorem runSModStack?_cons
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    runSModStack? { stack := dividend :: divisor :: rest } =
      some
        { effects :=
            { stackWords := [SModArgs.smodResultFromArgs
                (SModArgs.smodArgs dividend divisor)] }
          stack := rest } := rfl

theorem runSModStack?_underflow_nil :
    runSModStack? { stack := [] } = none := rfl

theorem runSModStack?_underflow_one (dividend : EvmWord) :
    runSModStack? { stack := [dividend] } = none := rfl

theorem stackRestAfterSMod?_none_of_empty :
    stackRestAfterSMod? [] = none := rfl

theorem stackRestAfterSMod?_none_of_one
    (dividend : EvmWord) :
    stackRestAfterSMod? [dividend] = none := rfl

theorem runSModStack?_head?
    (dividend divisor : EvmWord) (rest : List EvmWord) :
    (runSModStack? { stack := dividend :: divisor :: rest }).map
      (fun out => out.effects.stackWords.head?) =
      some (some (SModArgs.smodResultFromArgs
        (SModArgs.smodArgs dividend divisor))) := rfl

theorem runSModStack?_zero_divisor
    (dividend : EvmWord) (rest : List EvmWord) :
    runSModStack? { stack := dividend :: 0 :: rest } =
      some { effects := { stackWords := [0] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_zero_divisor]

theorem runSModStack?_neg_pos_sign
    (rest : List EvmWord) :
    runSModStack? { stack := (-3 : EvmWord) :: 2 :: rest } =
      some { effects := { stackWords := [(-1 : EvmWord)] }, stack := rest } := by
  rw [runSModStack?_cons]
  rw [SModArgs.smodResultFromArgs_neg_pos_sign]

end SModStackExecutionBridge
end EvmAsm.Evm64
