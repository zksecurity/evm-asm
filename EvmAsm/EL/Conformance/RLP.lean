/-
  EvmAsm.EL.Conformance.RLP

  Compact Lean-side conformance vectors for the executable RLP decoder
  (GH #125 / GH #120).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.RLP.Decode

namespace EvmAsm.EL
namespace Conformance
namespace RLP

abbrev Byte := EvmAsm.EL.RLP.Byte
abbrev RLPItem := EvmAsm.EL.RLP.RLPItem

/-- Input shape for an RLP decode executable-helper conformance vector. -/
structure DecodeInput where
  bytes : List Byte
  deriving Repr

/-- Decode exactly one RLP item and reject leftover bytes. -/
def runDecodeFully (input : DecodeInput) : Option RLPItem :=
  match EvmAsm.EL.RLP.decode input.bytes with
  | some (item, []) => some item
  | _ => none

/-- Nested list decode vector, covering recursive item decoding.
    Distinctive token: rlpNestedListDecodeVector. -/
def rlpNestedListDecodeVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-nested-list-decode"
    input := { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    expected := .value (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) }

/-- Non-canonical singleton byte string must be rejected; `0x01` should be
    encoded directly as the single byte `0x01`, not as `0x81 0x01`. -/
def rlpNoncanonicalSingletonVector : TestVector DecodeInput RLPItem :=
  { id := "rlp-noncanonical-singleton"
    input := { bytes := [(0x81 : Byte), 0x01] }
    expected := .error "noncanonical-singleton" }

theorem runDecodeFully_nestedList :
    runDecodeFully { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] } =
      some (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]]) := rfl

theorem runDecodeFully_reject_noncanonical_singleton :
    runDecodeFully { bytes := [(0x81 : Byte), 0x01] } = none := rfl

theorem rlpNestedListDecodeVector_passed :
    checkVector? runDecodeFully rlpNestedListDecodeVector = .passed :=
  checkVector?_some_passed runDecodeFully
    "rlp-nested-list-decode"
    { bytes := [(0xc3 : Byte), 0x01, 0x02, 0x03] }
    (.list [.bytes [0x01], .bytes [0x02], .bytes [0x03]])
    runDecodeFully_nestedList

theorem rlpNoncanonicalSingletonVector_errored :
    checkVector? runDecodeFully rlpNoncanonicalSingletonVector =
      .errored "rlp-noncanonical-singleton" "noncanonical-singleton" :=
  checkVector?_none_error runDecodeFully
    "rlp-noncanonical-singleton"
    "noncanonical-singleton"
    { bytes := [(0x81 : Byte), 0x01] }
    runDecodeFully_reject_noncanonical_singleton

/-- Compact checked-vector batch for RLP executable decoding.
    Distinctive token: RLP.rlpConformanceVectors #125 #120. -/
def rlpConformanceVectors : List CheckResult :=
  [ checkVector? runDecodeFully rlpNestedListDecodeVector
  , checkVector? runDecodeFully rlpNoncanonicalSingletonVector
  ]

theorem rlpConformanceVectors_passed :
    rlpConformanceVectors =
      [.passed, .errored "rlp-noncanonical-singleton" "noncanonical-singleton"] := by
  simp [rlpConformanceVectors, rlpNestedListDecodeVector_passed,
    rlpNoncanonicalSingletonVector_errored]

end RLP
end Conformance
end EvmAsm.EL
