/-
  EvmAsm.Evm64.Accelerators.Coverage

  Checked coverage table for the 19 functions declared by
  `zkvm_accelerators.h`. This mirrors the human-facing audit table in
  `docs/zkvm-accelerators-interface.md` while keeping the selector count,
  selector uniqueness, and accelerator range checked by Lean.
-/

import EvmAsm.Evm64.Accelerators.SyscallIds

namespace EvmAsm
namespace Accelerators

open SyscallId

/-- EVM-facing surface that uses a zkVM accelerator. -/
inductive AcceleratorSurface where
  | opcode (name : String)
  | precompile (address : Nat) (name : String)
  | nonPrecompile (name : String)
  deriving DecidableEq, Repr

/-- One row of the zkVM accelerator coverage table. -/
structure AcceleratorCoverage where
  cSymbol : String
  selector : Nat
  surface : AcceleratorSurface
  deriving DecidableEq, Repr

/-- The 19 `zkvm_accelerators.h` functions and the selector assigned to each. -/
def acceleratorCoverageTable : List AcceleratorCoverage :=
  [{ cSymbol := "zkvm_keccak256",
     selector := keccak256,
     surface := .opcode "KECCAK256" },
   { cSymbol := "zkvm_secp256k1_verify",
     selector := secp256k1_verify,
     surface := .nonPrecompile "secp256k1 signature verify" },
   { cSymbol := "zkvm_secp256k1_ecrecover",
     selector := secp256k1_ecrecover,
     surface := .precompile 0x01 "ECRECOVER" },
   { cSymbol := "zkvm_sha256",
     selector := sha256,
     surface := .precompile 0x02 "SHA256" },
   { cSymbol := "zkvm_ripemd160",
     selector := ripemd160,
     surface := .precompile 0x03 "RIPEMD160" },
   { cSymbol := "zkvm_modexp",
     selector := modexp,
     surface := .precompile 0x05 "MODEXP" },
   { cSymbol := "zkvm_bn254_g1_add",
     selector := bn254_g1_add,
     surface := .precompile 0x06 "BN254 G1 ADD" },
   { cSymbol := "zkvm_bn254_g1_mul",
     selector := bn254_g1_mul,
     surface := .precompile 0x07 "BN254 G1 MUL" },
   { cSymbol := "zkvm_bn254_pairing",
     selector := bn254_pairing,
     surface := .precompile 0x08 "BN254 PAIRING" },
   { cSymbol := "zkvm_blake2f",
     selector := blake2f,
     surface := .precompile 0x09 "BLAKE2F" },
   { cSymbol := "zkvm_kzg_point_eval",
     selector := kzg_point_eval,
     surface := .precompile 0x0a "KZG POINT EVAL" },
   { cSymbol := "zkvm_bls12_g1_add",
     selector := bls12_g1_add,
     surface := .precompile 0x0b "BLS12 G1 ADD" },
   { cSymbol := "zkvm_bls12_g1_msm",
     selector := bls12_g1_msm,
     surface := .precompile 0x0c "BLS12 G1 MSM" },
   { cSymbol := "zkvm_bls12_g2_add",
     selector := bls12_g2_add,
     surface := .precompile 0x0d "BLS12 G2 ADD" },
   { cSymbol := "zkvm_bls12_g2_msm",
     selector := bls12_g2_msm,
     surface := .precompile 0x0e "BLS12 G2 MSM" },
   { cSymbol := "zkvm_bls12_pairing",
     selector := bls12_pairing,
     surface := .precompile 0x0f "BLS12 PAIRING" },
   { cSymbol := "zkvm_bls12_map_fp_to_g1",
     selector := bls12_map_fp_to_g1,
     surface := .precompile 0x10 "BLS12 MAP FP TO G1" },
   { cSymbol := "zkvm_bls12_map_fp2_to_g2",
     selector := bls12_map_fp2_to_g2,
     surface := .precompile 0x11 "BLS12 MAP FP2 TO G2" },
   { cSymbol := "zkvm_secp256r1_verify",
     selector := secp256r1_verify,
     surface := .precompile 0x100 "secp256r1 verify" }]

/-- The checked coverage table has one row per accelerator C function. -/
theorem acceleratorCoverageTable_length :
    acceleratorCoverageTable.length = 19 := by
  decide

/-- Selectors projected from the coverage table. -/
def acceleratorCoverageSelectors : List Nat :=
  acceleratorCoverageTable.map (fun row => row.selector)

/-- The coverage-table selectors match the canonical selector list. -/
theorem acceleratorCoverageSelectors_eq :
    acceleratorCoverageSelectors =
      [keccak256, secp256k1_verify,
       secp256k1_ecrecover, sha256, ripemd160, modexp,
       bn254_g1_add, bn254_g1_mul, bn254_pairing,
       blake2f, kzg_point_eval,
       bls12_g1_add, bls12_g1_msm, bls12_g2_add, bls12_g2_msm,
       bls12_pairing, bls12_map_fp_to_g1, bls12_map_fp2_to_g2,
       secp256r1_verify] := by
  decide

/-- The coverage table does not assign the same selector twice. -/
theorem acceleratorCoverageSelectors_nodup :
    acceleratorCoverageSelectors.Nodup := by
  rw [acceleratorCoverageSelectors_eq]
  decide

/-- Every selector in the coverage table is in the reserved accelerator range. -/
theorem acceleratorCoverageSelectors_in_range :
    ∀ id ∈ acceleratorCoverageSelectors, 0x100 ≤ id ∧ id < 0x113 := by
  rw [acceleratorCoverageSelectors_eq]
  decide

/-- C symbols projected from the coverage table. -/
def acceleratorCoverageSymbols : List String :=
  acceleratorCoverageTable.map (fun row => row.cSymbol)

/-- The coverage table lists each `zkvm_accelerators.h` C symbol once. -/
theorem acceleratorCoverageSymbols_nodup :
    acceleratorCoverageSymbols.Nodup := by
  decide

/-- Ethereum precompile addresses covered by accelerator-backed rows.

This excludes the non-precompile KECCAK256 and secp256k1 verification
accelerators and also excludes IDENTITY (`0x04`), which is pure memory copy
and has no accelerator C symbol. -/
def acceleratorPrecompileAddresses : List Nat :=
  acceleratorCoverageTable.filterMap fun row =>
    match row.surface with
    | .precompile address _ => some address
    | _ => none

/-- The accelerator-backed precompile address set mirrors `zkvm_accelerators.h`.

Address `0x04` is intentionally absent because IDENTITY has no accelerator. -/
theorem acceleratorPrecompileAddresses_eq :
    acceleratorPrecompileAddresses =
      [0x01, 0x02, 0x03, 0x05, 0x06, 0x07, 0x08, 0x09,
       0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x100] := by
  decide

/-- No precompile address is assigned to more than one accelerator row. -/
theorem acceleratorPrecompileAddresses_nodup :
    acceleratorPrecompileAddresses.Nodup := by
  rw [acceleratorPrecompileAddresses_eq]
  decide

/-- IDENTITY (`0x04`) is not accelerator-backed. -/
theorem identity_not_mem_acceleratorPrecompileAddresses :
    0x04 ∉ acceleratorPrecompileAddresses := by
  rw [acceleratorPrecompileAddresses_eq]
  decide

end Accelerators
end EvmAsm
