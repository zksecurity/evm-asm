/-
  EvmAsm.EL.Conformance.ExpGas

  Lean-side conformance vectors for EXP exponent-byte gas accounting
  (GH #125, exercising the GH #92 executable helper).
-/

import EvmAsm.EL.Conformance
import EvmAsm.Evm64.Exp.Gas

namespace EvmAsm.EL
namespace Conformance
namespace ExpGas

abbrev EvmWord := EvmAsm.Evm64.EvmWord

/-- Input shape for an EXP gas executable-helper conformance vector. -/
structure ExpGasInput where
  exponent : EvmWord
  deriving Repr

def runExpGas (input : ExpGasInput) : Nat :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent input.exponent

/-- EXP with zero exponent charges only the static/base EXP gas.
    Distinctive token: expGasZeroExponentVector. -/
def expGasZeroExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-zero-exponent"
    input := { exponent := 0 }
    expected := .value 10 }

/-- A one-byte nonzero exponent adds one 50-gas exponent-byte charge. -/
def expGasOneByteExponentVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-one-byte-exponent"
    input := { exponent := 1 }
    expected := .value 60 }

/-- Exponent 256 is the first two-byte threshold and charges 10 + 2 * 50. -/
def expGasTwoByteThresholdVector : TestVector ExpGasInput Nat :=
  { id := "exp-gas-two-byte-threshold"
    input := { exponent := 256 }
    expected := .value 110 }

theorem runExpGas_zero :
    runExpGas { exponent := (0 : EvmWord) } = 10 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_zero

theorem runExpGas_one :
    runExpGas { exponent := (1 : EvmWord) } = 60 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_of_pos_lt_256
    (by decide) (by decide)

theorem runExpGas_256 :
    runExpGas { exponent := (256 : EvmWord) } = 110 :=
  EvmAsm.Evm64.ExpGas.expTotalGasFromExponent_256

theorem expGasZeroExponentVector_passed :
    checkVector runExpGas expGasZeroExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-zero-exponent"
    { exponent := (0 : EvmWord) }
    10
    runExpGas_zero

theorem expGasOneByteExponentVector_passed :
    checkVector runExpGas expGasOneByteExponentVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-one-byte-exponent"
    { exponent := (1 : EvmWord) }
    60
    runExpGas_one

theorem expGasTwoByteThresholdVector_passed :
    checkVector runExpGas expGasTwoByteThresholdVector = .passed :=
  checkVector_value_passed runExpGas
    "exp-gas-two-byte-threshold"
    { exponent := (256 : EvmWord) }
    110
    runExpGas_256

/-- Compact checked-vector batch for EXP gas executable helpers.
    Distinctive token: expGasConformanceVectors. -/
def expGasConformanceVectors : List CheckResult :=
  [ checkVector runExpGas expGasZeroExponentVector
  , checkVector runExpGas expGasOneByteExponentVector
  , checkVector runExpGas expGasTwoByteThresholdVector
  ]

theorem expGasConformanceVectors_passed :
    expGasConformanceVectors = [.passed, .passed, .passed] := by
  simp [expGasConformanceVectors, expGasZeroExponentVector_passed,
    expGasOneByteExponentVector_passed, expGasTwoByteThresholdVector_passed]

end ExpGas
end Conformance
end EvmAsm.EL
