/-
  EvmAsm.Evm64.Exp.Args

  Pure stack-argument bridge for EXP (GH #92).
-/

import EvmAsm.Evm64.EvmWordArith.Exp
import EvmAsm.Evm64.Exp.Gas

namespace EvmAsm.Evm64
namespace ExpArgs

/-- EXP stack arguments: base and exponent. -/
structure Args where
  base : EvmWord
  exponent : EvmWord
  deriving Repr

/-- EXP pops two stack words: base and exponent. -/
def stackArgumentCount : Nat := 2

/-- EXP pushes one result word. -/
def resultCount : Nat := 1

/-- Convenience builder for EXP stack arguments. -/
def expArgs (base exponent : EvmWord) : Args :=
  { base := base, exponent := exponent }

/-- EXP result computed from decoded stack arguments.
    Distinctive token: ExpArgs.expResultFromArgs. -/
def expResultFromArgs (args : Args) : EvmWord :=
  EvmWord.exp args.base args.exponent

/-- Dynamic gas for EXP computed from decoded stack arguments. -/
def expDynamicCostFromArgs (args : Args) : Nat :=
  ExpGas.expDynamicCostFromExponent args.exponent

/-- Total EXP gas computed from decoded stack arguments. -/
def expTotalGasFromArgs (args : Args) : Nat :=
  ExpGas.expTotalGasFromExponent args.exponent

/-- Stack after the EXP result replaces the two operands. -/
def stackAfterExp (args : Args) (rest : List EvmWord) : List EvmWord :=
  expResultFromArgs args :: rest

theorem stackArgumentCount_eq_two : stackArgumentCount = 2 := rfl

theorem resultCount_eq_one : resultCount = 1 := rfl

theorem expArgs_base (base exponent : EvmWord) :
    (expArgs base exponent).base = base := rfl

theorem expArgs_exponent (base exponent : EvmWord) :
    (expArgs base exponent).exponent = exponent := rfl

theorem expResultFromArgs_eq (args : Args) :
    expResultFromArgs args = EvmWord.exp args.base args.exponent := rfl

theorem expDynamicCostFromArgs_eq (args : Args) :
    expDynamicCostFromArgs args =
      ExpGas.expDynamicCostFromExponent args.exponent := rfl

theorem expTotalGasFromArgs_eq (args : Args) :
    expTotalGasFromArgs args =
      ExpGas.expTotalGasFromExponent args.exponent := rfl

theorem stackAfterExp_eq (args : Args) (rest : List EvmWord) :
    stackAfterExp args rest = expResultFromArgs args :: rest := rfl

theorem stackAfterExp_head (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).head? = some (expResultFromArgs args) := rfl

theorem stackAfterExp_tail (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).tail = rest := rfl

@[simp] theorem stackAfterExp_length (args : Args) (rest : List EvmWord) :
    (stackAfterExp args rest).length = rest.length + 1 := by
  simp [stackAfterExp]

theorem expResultFromArgs_zero_zero :
    expResultFromArgs (expArgs 0 0) = 1 := by
  exact EvmWord.exp_zero_zero

theorem expResultFromArgs_zero_right (base : EvmWord) :
    expResultFromArgs (expArgs base 0) = 1 := by
  exact EvmWord.exp_zero_right base

theorem expResultFromArgs_one_right (base : EvmWord) :
    expResultFromArgs (expArgs base 1) = base := by
  exact EvmWord.exp_one_right base

theorem expResultFromArgs_two_256 :
    expResultFromArgs (expArgs 2 256) = 0 := by
  exact EvmWord.exp_two_256

@[simp] theorem expDynamicCostFromArgs_zero_exponent (base : EvmWord) :
    expDynamicCostFromArgs (expArgs base 0) = 0 := by
  exact ExpGas.expDynamicCostFromExponent_zero

theorem expTotalGasFromArgs_zero_exponent (base : EvmWord) :
    expTotalGasFromArgs (expArgs base 0) = 10 := by
  exact ExpGas.expTotalGasFromExponent_zero

end ExpArgs
end EvmAsm.Evm64
