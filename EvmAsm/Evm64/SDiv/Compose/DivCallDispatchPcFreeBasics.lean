/-
  EvmAsm.Evm64.SDiv.Compose.DivCallDispatchPcFreeBasics

  Core PC-free instances for DIV dispatcher assertions used by SDIV div-call
  sidecar proofs.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix

namespace EvmAsm.Evm64.SDiv.Compose

theorem divModStackDispatchPre_pcFree
    {sp : Word} {a b : EvmWord}
    {v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    (EvmAsm.Evm64.divModStackDispatchPre sp a b
      v1 v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0).pcFree := by
  rw [EvmAsm.Evm64.divModStackDispatchPre_unfold,
    EvmAsm.Evm64.divScratchValuesCall_unfold]
  pcFree

instance pcFreeInst_divModStackDispatchPre
    (sp : Word) (a b : EvmWord)
    (v1 v2 v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word) :
    EvmAsm.Rv64.Assertion.PCFree
      (EvmAsm.Evm64.divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) :=
  ⟨divModStackDispatchPre_pcFree⟩

theorem divStackDispatchPostNoX1_pcFree {sp : Word} {a b : EvmWord} :
    (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b).pcFree := by
  rw [EvmAsm.Evm64.divStackDispatchPostNoX1_unfold,
    EvmAsm.Evm64.divScratchOwnCall_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  pcFree

instance pcFreeInst_divStackDispatchPostNoX1
    (sp : Word) (a b : EvmWord) :
    EvmAsm.Rv64.Assertion.PCFree (EvmAsm.Evm64.divStackDispatchPostNoX1 sp a b) :=
  ⟨divStackDispatchPostNoX1_pcFree⟩

end EvmAsm.Evm64.SDiv.Compose
