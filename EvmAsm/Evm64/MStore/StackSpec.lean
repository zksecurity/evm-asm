/-
  EvmAsm.Evm64.MStore.StackSpec

  Stack-level bridge helpers for MSTORE.  Direct MSTORE analogs of the
  `MLoad/StackSpec.lean` lemmas: lift triples over `mstoreStackCode`
  to triples over `evm_mstore_code`.
-/

import EvmAsm.Evm64.MStore.Spec

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Sub-monotonicity: `mstoreStackCode` is contained in `evm_mstore_code` (they
    are in fact equal by `mstoreStackCode_eq_evm_mstore_code`).  Direct MSTORE
    analog of `evm_mload_code_stack_sub` (PR #3102, evm-asm-rw24y).

    Distinctive token: evm_mstore_code_stack_sub #53. -/
theorem evm_mstore_code_stack_sub
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg) (base : Word) :
    ∀ a i,
      (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) a = some i →
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) a = some i := by
  rw [mstoreStackCode_eq_evm_mstore_code
    offReg valReg byteReg accReg addrReg memBaseReg base]
  intro _ _ h; exact h

/-- Transport a `cpsTripleWithin` over `mstoreStackCode` to one over
    `evm_mstore_code`.  Subsequent slices use this to land
    `evm_mstore_stack_spec_within` (evm-asm-ln8t5 / GH #53 follow-up) by
    composing the existing `mstore_combined_*_stack_spec_within` lemmas
    (over `mstoreStackCode`) with concrete byte-window write triples.

    Direct MSTORE analog of `cpsTripleWithin_evm_mload_of_stack`
    (PR #3102, evm-asm-rw24y).

    Distinctive token: cpsTripleWithin_evm_mstore_of_stack #53. -/
theorem cpsTripleWithin_evm_mstore_of_stack
    {n : Nat} {P Q : Assertion}
    (offReg valReg byteReg accReg addrReg memBaseReg : Reg)
    (base pcEnd : Word)
    (h :
      cpsTripleWithin n base pcEnd
        (mstoreStackCode offReg byteReg accReg addrReg memBaseReg base) P Q) :
    cpsTripleWithin n base pcEnd
      (evm_mstore_code offReg valReg byteReg accReg addrReg memBaseReg base) P Q :=
  cpsTripleWithin_extend_code
    (h := h)
    (hmono := evm_mstore_code_stack_sub
      offReg valReg byteReg accReg addrReg memBaseReg base)

end EvmAsm.Evm64
