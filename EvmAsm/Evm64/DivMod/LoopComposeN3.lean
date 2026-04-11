/-
  EvmAsm.Evm64.DivMod.LoopComposeN3

  Two-iteration loop composition for n=3: composes j=1 (loop-back) with
  j=0 (loop-exit) to produce a cpsTriple from base+448 to base+904.

  For n=3, the loop runs 2 iterations. The j=1 iteration modifies u[1]..u[4]
  and stores q[1]. The j=0 iteration reads u[0]..u[4] (where u[1]..u[4]
  are the updated values from j=1) and stores q[0].
-/

import EvmAsm.Evm64.DivMod.LoopIterN3

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- ============================================================================
-- Address equality lemmas for j=1 output → j=0 input transition
--
-- j=1 postcondition uses u_base(1) = sp + signExtend12(4056) - 8
-- j=0 precondition uses u_base(0) = sp + signExtend12(4056)
-- The overlap: u_base(1) + offset_k = u_base(0) + offset_{k-1}
-- ============================================================================

/-- j=1 un0 at u_base(1)+0 = j=0 u1 at u_base(0)-8 -/
theorem u_j1_0_eq_j0_4088 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 0 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 := by
  simp only [
    show signExtend12 (0 : BitVec 12) = (0 : Word) from by decide,
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un1 at u_base(1)-8 = j=0 u2 at u_base(0)-16 -/
theorem u_j1_4088_eq_j0_4080 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4088 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4088 : BitVec 12) = (18446744073709551608 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un2 at u_base(1)-16 = j=0 u3 at u_base(0)-24 -/
theorem u_j1_4080_eq_j0_4072 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4080 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4080 : BitVec 12) = (18446744073709551600 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

/-- j=1 un3 at u_base(1)-24 = j=0 u_top at u_base(0)-32 -/
theorem u_j1_4072_eq_j0_4064 (sp : Word) :
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4072 =
    (sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) + signExtend12 4064 := by
  simp only [
    show signExtend12 (4056 : BitVec 12) = (18446744073709551576 : Word) from by decide,
    show signExtend12 (4072 : BitVec 12) = (18446744073709551592 : Word) from by decide,
    show signExtend12 (4064 : BitVec 12) = (18446744073709551584 : Word) from by decide,
    show (3 : BitVec 6).toNat = 3 from by decide,
    show (0 : Word) <<< 3 = (0 : Word) from by decide,
    show (1 : Word) <<< 3 = (8 : Word) from by decide]
  bv_omega

end EvmAsm.Evm64
