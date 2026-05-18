# D2/D3-A and D5 Counterexample

Status: preserved historical note for the deleted
`EvmAsm/Evm64/EvmWordArith/Div128NoWrapDischarge.lean` scaffolding.

## Summary

The abandoned D5 route tried to prove:

```lean
isSkipBorrowN4Call a b -> Div128PhaseNoWrapInv uHi uLo vTop
```

That implication is false for the runtime-reachable addback input class. The
counterexample is:

```text
a3 = 2^64 - 2
b3 = 1
b2 = 2^64 - 2
```

On this input, the skip-borrow condition can hold, but the Phase 1 no-wrap
conjunct inside `Div128PhaseNoWrapInv` fails. Equivalently, the corrected
`rhat'` can be at least `2^32`; the deleted D2/D3-A lemma
`n4RhatPrime_lt_pow32_of_skip_borrow` claimed the opposite.

## Consequence

Do not resurrect the D5 proof route or any closure attempt that depends on
deriving `Div128PhaseNoWrapInv` from skip-borrow alone. The one-correction
`div128Quot` path does not preserve Knuth's classical two-correction
`rhat' < B` invariant.

The call-skip path was closed by bypassing `Div128PhaseNoWrapInv` and using
`n4CallSkipSemanticHolds_of_call_trial` with
`div128Quot_call_skip_ge_val256_div_v2`.

The call-addback-BEQ path remains Phase 2a work: fix or reformulate the
addback loop semantics, then prove the addback correction bridge directly.
