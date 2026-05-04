/-
  EvmAsm.Evm64.Env.Spec

  Per-limb cpsTripleWithin spec for the simple environment opcode load.

  Slice 5a-pre of GH #103 (parent `evm-asm-3jso`, this slice
  `evm-asm-ndsm`). The 9-instruction `evm_env_load` program decomposes
  into one `ADDI x12 x12 -32` allocator plus four `LD/SD` limb pairs
  (`env_one_limb`). This file lifts the 2-instruction limb pair to a
  reusable `cpsTripleWithin` spec so the eventual 5a low-level spec
  reuses it four times via `runBlock`, paralleling the structure of
  `EvmAsm/Evm64/Calldata/SizeSpec.lean`.

  Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
-/

import EvmAsm.Evm64.Env.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.RunBlock
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Evm64.Stack

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64
namespace Env

open EvmAsm.Rv64

/-- Code requirement for one `LD/SD` limb pair at byte address `base`.
    Matches the shape produced by the `env_one_limb` skeleton in
    `Env/Program.lean`. -/
abbrev env_one_limb_code
    (envBaseReg tmpReg : Reg) (loadOff storeOff : Nat) (base : Word) : CodeReq :=
  CodeReq.ofProg base
    (LD tmpReg envBaseReg (BitVec.ofNat 12 loadOff) ;;
     SD .x12 tmpReg (BitVec.ofNat 12 storeOff))

/-- Per-limb spec for `env_one_limb`: load a 64-bit limb from the
    environment block at `envAddr + loadOff` into `tmpReg`, then store
    it back at `nsp + storeOff` (above the new EVM SP `nsp`).

    Both offsets are required to be small (< 2048) so the 12-bit
    immediate sign-extends to itself.

    The spec exposes `nsp` directly (i.e. caller has already pre-bumped
    `x12`) and frames the source `envAddr` cell through unchanged.  -/
theorem env_one_limb_spec_within
    (envBaseReg tmpReg : Reg) (htmp_ne_x0 : tmpReg ≠ .x0)
    (envAddr nsp memVal dOld tempOld : Word)
    (loadOff storeOff : Nat)
    (h_load : loadOff < 2048) (h_store : storeOff < 2048)
    (base : Word) :
    cpsTripleWithin 2 base (base + 8)
      (env_one_limb_code envBaseReg tmpReg loadOff storeOff base)
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ tempOld) **
       (.x12 ↦ᵣ nsp) **
       ((envAddr + BitVec.ofNat 64 loadOff) ↦ₘ memVal) **
       ((nsp + BitVec.ofNat 64 storeOff) ↦ₘ dOld))
      ((envBaseReg ↦ᵣ envAddr) ** (tmpReg ↦ᵣ memVal) **
       (.x12 ↦ᵣ nsp) **
       ((envAddr + BitVec.ofNat 64 loadOff) ↦ₘ memVal) **
       ((nsp + BitVec.ofNat 64 storeOff) ↦ₘ memVal)) := by
  -- Normalise the 12-bit sign-extension so it matches the 64-bit
  -- offsets used by the `↦ₘ` cells.
  have h_load_se :
      signExtend12 (BitVec.ofNat 12 loadOff) = BitVec.ofNat 64 loadOff :=
    signExtend12_ofNat_small h_load
  have h_store_se :
      signExtend12 (BitVec.ofNat 12 storeOff) = BitVec.ofNat 64 storeOff :=
    signExtend12_ofNat_small h_store
  -- LD tmpReg envBaseReg loadOff : load the limb.
  have hLD := ld_spec_gen_within tmpReg envBaseReg envAddr tempOld memVal
                (BitVec.ofNat 12 loadOff) base htmp_ne_x0
  rw [h_load_se] at hLD
  -- SD x12 tmpReg storeOff : write the limb to the new stack slot.
  have hSD := sd_spec_gen_within .x12 tmpReg nsp memVal dOld
                (BitVec.ofNat 12 storeOff) (base + 4)
  rw [h_store_se] at hSD
  runBlock hLD hSD

end Env
end EvmAsm.Evm64
