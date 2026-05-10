/-
  EvmAsm.Evm64.SDiv.Compose.Base

  Shared composition infrastructure for SDIV: `sdivCode` (the union of
  all sub-block `CodeReq`s), subsumption helpers tying sub-block codes
  back to `sdivCode`, and shared length lemmas.

  Skeleton placeholder for GH #90 (beads slice evm-asm-kyp6). Concrete
  definitions will be added once `evm_sdiv` is laid out (slice
  evm-asm-01uh) and the per-block specs from `LimbSpec.lean` start
  composing.
-/

import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Byte offset of the saved-`ra` prologue inside `evm_sdiv_wrapper`. -/
def saveRaOff : Nat := 0

/-- Byte offset of the dividend sign probe inside `evm_sdiv_wrapper`. -/
def dividendSignOff : Nat := 4

/-- Byte offset of the divisor sign probe inside `evm_sdiv_wrapper`. -/
def divisorSignOff : Nat := 12

/-- Byte offset of the in-place dividend absolute-value block. -/
def dividendAbsOff : Nat := 20

/-- Byte offset of the in-place divisor absolute-value block. -/
def divisorAbsOff : Nat := 104

/-- Byte offset of the sign-xor instruction selecting result negation. -/
def signXorOff : Nat := 188

/-- Byte offset of the near call into `evm_div_callable`. -/
def divCallOff : Nat := 192

/-- Byte offset of the in-place quotient sign-fixup block. -/
def resultSignFixOff : Nat := 196

/-- Byte offset of the saved-`ra` return instruction. -/
def savedRaRetOff : Nat := 280

/-- Byte offset at the end of the SDIV wrapper. The appended unsigned
    divider callable starts here. -/
def wrapperEndOff : Nat := 284

/-- Bundled byte offsets for the concrete SDIV wrapper layout. -/
theorem sdiv_wrapper_block_byte_offsets :
    saveRaOff = 0 ∧
    dividendSignOff = 4 ∧
    divisorSignOff = 12 ∧
    dividendAbsOff = 20 ∧
    divisorAbsOff = 104 ∧
    signXorOff = 188 ∧
    divCallOff = 192 ∧
    resultSignFixOff = 196 ∧
    savedRaRetOff = 280 ∧
    wrapperEndOff = 284 := by
  native_decide

/-- Full SDIV code region handle: wrapper followed by `evm_div_callable`. -/
abbrev sdivCode (base : Word) : CodeReq :=
  CodeReq.ofProg base EvmAsm.Evm64.evm_sdiv

/-- Code handle for the saved-`ra` prologue block. -/
abbrev saveRaCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + saveRaOff) (EvmAsm.Evm64.evm_sdiv_save_ra_block .x18)

/-- Code handle for the dividend sign-bit probe. -/
abbrev dividendSignCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + dividendSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_sdivDividendTopLimbOff)

/-- Code handle for the divisor sign-bit probe. -/
abbrev divisorSignCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divisorSignOff)
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_sdivDivisorTopLimbOff)

/-- Code handle for the in-place dividend absolute-value block. -/
abbrev dividendAbsCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + dividendAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24)

/-- Code handle for the in-place divisor absolute-value block. -/
abbrev divisorAbsCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divisorAbsOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56)

/-- Code handle for the sign-xor instruction selecting result negation. -/
abbrev signXorCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + signXorOff) (EvmAsm.Rv64.XOR' .x8 .x8 .x9)

/-- Code handle for the near call into `evm_div_callable`. -/
abbrev divCallCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + divCallOff)
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_sdivCallOff)

/-- Code handle for the in-place quotient sign-fixup block. -/
abbrev resultSignFixCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + resultSignFixOff)
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      32 40 48 56)

/-- Code handle for the saved-`ra` return instruction. -/
abbrev savedRaRetCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + savedRaRetOff)
    (EvmAsm.Evm64.evm_sdiv_saved_ra_ret_block .x18)

/-- Code handle for the appended unsigned divider callable. -/
abbrev divCallableCode (base : Word) : CodeReq :=
  CodeReq.ofProg (base + wrapperEndOff) EvmAsm.Evm64.evm_div_callable

end EvmAsm.Evm64.SDiv.Compose
