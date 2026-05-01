# DivMod `base + NNN` Literal Audit (issue #301, slice 2)

This audit tabulates the remaining 3-/4-digit `base + NNN` literals across
`EvmAsm/Evm64/DivMod/` and maps each one to either an existing block offset
in `EvmAsm/Evm64/DivMod/Compose/Offsets.lean` or a sub-block offset that
deserves a new named constant. It feeds the migration work in slice 3
(`evm-asm-7rk`) and the followups under issue #301.

It does **not** itself rename any literal; it is a reference doc.

## Methodology

```
grep -rhoE 'base \+ [0-9]{3,4}' EvmAsm/Evm64/DivMod \
  | sort | uniq -c | sort -rn
```

There are 56 distinct literal values and ~960 total occurrences as of this
audit (slice 1 — `divCallRetOff = 516`, ~496 of those occurrences — is being
landed in PR #1503 in parallel; subtract that to get the slice-2/3 scope).

## By Block

The columns are: literal, block (block-name + sub-offset), distinct/used.
`✓` = already named in `Compose/Offsets.lean`. `→` = new sub-block offset
that slice-3 should name. The "phaseA-block-offset" already lives at zero
so anything in phaseA is just `phaseAOff`.

### Block boundaries (for cross-reference)

| Offset | Block         | Length |
|-------:|---------------|-------:|
|      0 | phaseAOff     |    32  |
|     32 | phaseBOff     |    84  |
|    116 | clzOff        |    96  |
|    212 | phaseC2Off    |    16  |
|    228 | normBOff      |    84  |
|    312 | normAOff      |    84  |
|    396 | copyAUOff     |    36  |
|    432 | loopSetupOff  |    16  |
|    448 | loopBodyOff   |   460  |
|    908 | denormOff     |   100  |
|   1008 | epilogueOff   |    40  |
|   1048 | zeroPathOff   |    20  |
|   1068 | nopOff        |     4  |
|   1072 | div128Off     |   196  |

### phaseB block (0 literals — reclassified)

The 7 occurrences of `base + 100` originally listed here live in
`LimbSpec/Div128Step1v2.lean`. **They are NOT phaseB offsets.** That file
is the `divK_div128_step1_v2` subroutine, whose `base` argument is the
locally-rebased subroutine base — callers in `Compose/Div128.lean` and
`Compose/ModDiv128.lean` invoke it with `(base + 1112)` (= `div128Off + 40`).
So `base + 100` inside Div128Step1v2.lean is the 25-instruction
SUBROUTINE block-exit PC (block length = 100), not a global `phaseBOff + 68`.

Migrating it to `base + phaseBOff + 68` breaks the caller bridge — e.g.
`Compose/Div128.lean:455` does `rw [show (base+1112)+100 = base+1212 from by
bv_addr]`, which fails when the callee post-PC is `phaseBOff + 68` instead
of a literal `100`.

**Recommendation:** leave `base + 100` as-is in Div128Step1v2.lean — it is
a subroutine-local block length, not a DivMod-global offset. (See beads
`evm-asm-v9q6` for the failed migration attempt and `evm-asm-by3m` for this
audit fix.)

### clz block (1 literal remaining — reclassified; 6 migrated by #1625)

The literals `base + {120, 136, 152, 168, 184, 200}` were migrated to
`clzOff + k` form in PR #1625. The remaining occurrences of `base + 124`
all live in `LimbSpec/Div128Step2v4.lean`, which is a rebased subroutine
(its `base` argument is `divK_div128_step2_v4`'s local base, not the global
DivMod base). `base + 124` there is a 31-instruction block-exit PC (block
length = 124), **not** `clzOff + 8`.

**Recommendation:** leave `base + 124` as-is in Div128Step2v4.lean — same
reasoning as the phaseB block above. The original clz table is preserved
below as a historical reference but only rows 1–7 minus 124 were valid
migrations.

| literal   | meaning           | status |
|-----------|-------------------|--------|
| base + 120 | clzOff + 4       | migrated #1625 |
| base + 124 | (subroutine-local in Div128Step2v4.lean) | leave as-is |
| base + 136 | clzOff + 20      | migrated #1625 |
| base + 152 | clzOff + 36      | migrated #1625 |
| base + 168 | clzOff + 52      | migrated #1625 |
| base + 184 | clzOff + 68      | migrated #1625 |
| base + 200 | clzOff + 84      | migrated #1625 |

These were CLZ inner-step PCs (one constant per CLZ unrolled stage).

### phaseC2 block (1 literal, 20 uses)

| literal    | meaning           | recommendation |
|------------|-------------------|----------------|
| base + 224 | phaseC2Off + 12   | rewrite as `phaseC2Off + 12` |

### normB block (3 literals, 28 uses)

| literal    | meaning           |
|------------|-------------------|
| base + 252 | normBOff + 24     |
| base + 276 | normBOff + 48     |
| base + 300 | normBOff + 72     |

Per-limb normalisation steps. **Recommendation:** rewrite as `normBOff + 4*k`
or introduce a single `normBLimbStride := 24` if it makes the four limbs
read more uniformly.

### normA block (5 literals, 42 uses)

| literal    | meaning           |
|------------|-------------------|
| base + 324 | normAOff + 12     |
| base + 344 | normAOff + 32     |
| base + 364 | normAOff + 52     |
| base + 384 | normAOff + 72     |
| base + 392 | normAOff + 80     |

Mirror of normB (per-limb stride 20 instead of 24). **Recommendation:** same
as normB — rewrite as `normAOff + k`.

### loopSetup block (1 literal, 20 uses)

| literal    | meaning           | recommendation |
|------------|-------------------|----------------|
| base + 444 | loopSetupOff + 12 | rewrite as `loopSetupOff + 12` |

### loopBody block (22 literals, 655 uses) — **biggest offender**

The loop body itself is 460 bytes (115 instructions) and is internally
structured as:

| sub-block            | start (in body) | length | files                              |
|----------------------|----------------:|-------:|------------------------------------|
| trial-divide entry   |               0 |  ~52   | LoopBody.lean, TrialMax.lean       |
| div128 call site     |              52 |  ~16   | LoopBody/TrialCall.lean            |
| div128 call-return   |              68 |  —     | (just a PC; this is `516` = slice 1's `divCallRetOff`) |
| mulsub correction    |              88 |   ~88  | LoopBody/MulsubCorrection*.lean    |
| correction skip path |             176 |   ~88  | LoopBody/CorrectionSkip.lean       |
| correction addback   |             264 |  ~168  | LoopBody/CorrectionAddback*.lean   |
| store result limb    |             432 |   ~28  | LoopBody/StoreLoop.lean            |

| literal    | meaning             | proposed name (slice 3)            |
|------------|---------------------|------------------------------------|
| base + 448 | loopBodyOff + 0     | (already `loopBodyOff`)            |
| base + 452 | loopBodyOff + 4     | within trial-divide entry          |
| base + 500 | loopBodyOff + 52    | `trialCallOff   = loopBodyOff + 52`|
| base + 504 | loopBodyOff + 56    | within trial-call                  |
| base + 512 | loopBodyOff + 64    | `trialJalOff    = loopBodyOff + 64`|
| base + 516 | loopBodyOff + 68    | **`divCallRetOff`** (slice 1, PR #1503) |
| base + 536 | loopBodyOff + 88    | `mulsubOff      = loopBodyOff + 88`|
| base + 580 | loopBodyOff + 132   | within mulsub                      |
| base + 624 | loopBodyOff + 176   | `correctionSkipOff = loopBodyOff + 176` |
| base + 668 | loopBodyOff + 220   | within correction-skip             |
| base + 712 | loopBodyOff + 264   | `correctionAddbackOff = loopBodyOff + 264` |
| base + 728 | loopBodyOff + 280   | within correction-addback          |
| base + 732 | loopBodyOff + 284   | within correction-addback          |
| base + 736 | loopBodyOff + 288   | within correction-addback          |
| base + 768 | loopBodyOff + 320   | within correction-addback          |
| base + 800 | loopBodyOff + 352   | within correction-addback          |
| base + 832 | loopBodyOff + 384   | within correction-addback          |
| base + 864 | loopBodyOff + 416   | within correction-addback          |
| base + 880 | loopBodyOff + 432   | `storeLoopOff   = loopBodyOff + 432` |
| base + 884 | loopBodyOff + 436   | within store-loop                  |
| base + 900 | loopBodyOff + 452   | within store-loop                  |
| base + 904 | loopBodyOff + 456   | end of loop body                   |

**Proposed new top-level offsets in `Compose/Offsets.lean`:**
```
trialCallOff           := 500   -- = loopBodyOff + 52
divCallRetOff          := 516   -- = loopBodyOff + 68    (slice 1)
mulsubOff              := 536   -- = loopBodyOff + 88
correctionSkipOff      := 624   -- = loopBodyOff + 176
correctionAddbackOff   := 712   -- = loopBodyOff + 264
storeLoopOff           := 880   -- = loopBodyOff + 432
```
Each gets a `drift_check_*` example anchoring it to the corresponding
sub-block length (sub-block lengths come from the existing
`divK_loopBody_*` definitions). Within-sub-block offsets remain as
`<sub-block-off> + k` and don't need names — the rule of thumb established
by the existing `Offsets.lean` is "name boundaries, not interior steps."

### denorm block (7 literals, 85 uses)

| literal    | meaning           |
|------------|-------------------|
| base + 912 | denormOff + 4     |
| base + 916 | denormOff + 8     |
| base + 920 | denormOff + 12    |
| base + 924 | denormOff + 16    |
| base + 948 | denormOff + 40    |
| base + 972 | denormOff + 64    |
| base + 996 | denormOff + 88    |

Internal denorm steps; **Recommendation:** rewrite as `denormOff + k`
(no new named offsets needed).

### epilogue block (1 literal, 8 uses)

| literal    | meaning           | recommendation |
|------------|-------------------|----------------|
| base + 1024| epilogueOff + 16  | rewrite as `epilogueOff + 16` |

### div128 subroutine block (8 literals, 45 uses)

| literal    | meaning           |
|------------|-------------------|
| base + 1112 | div128Off + 40   |
| base + 1172 | div128Off + 100  |
| base + 1192 | div128Off + 120  |
| base + 1212 | div128Off + 140  |
| base + 1232 | div128Off + 160  |
| base + 1260 | div128Off + 188  |
| base + 1300 | div128Off + 228  |
| base + 1356 | div128Off + 284  |

The last two (1300, 1356) sit *past* `div128Off + 196` (which is the end of
the original `divK_div128`). They live in `Compose/Div128.lean` and
`Compose/Div128V4.lean` — those are the v2 / v4 "extended" div128 paths
which append more code after the canonical 196-byte div128. Slice 3 should
verify whether the v2/v4 extensions deserve their own `div128V2Off` /
`div128V4Off` named constants, or whether `div128Off + k` is enough.

**Recommendation for the rest:** rewrite as `div128Off + k` (mechanical).

## Summary recommendations for slice 3

1. **Add 5 new sub-block offsets** to `Compose/Offsets.lean`:
   `trialCallOff`, `mulsubOff`, `correctionSkipOff`,
   `correctionAddbackOff`, `storeLoopOff`. Each gets a `drift_check_*` tied
   to the corresponding `divK_loopBody_*` sub-block length. (`divCallRetOff`
   is being added by slice 1 / PR #1503 — coordinate so the constant ends up
   in the same `Offsets.lean` block.)

2. **Mechanical migration** of the remaining 50 literals to `<blockOff> + k`
   form using the audit table above. Reasonable PR-sized chunks:
   - clz + phaseC2 + normB + normA + loopSetup + epilogue (mostly Compose/
     and CLZ.lean files): one PR.
   - loopBody/* migrations leveraging the new sub-block offsets: one PR per
     sub-block (mulsub, correction-skip, correction-addback, store-loop)
     to keep diffs reviewable.
   - denorm + div128 internal: one PR.

3. **Investigate v2/v4 div128 extensions** (`base + 1300`, `base + 1356`):
   decide whether to introduce `div128V2Off` / `div128V4Off`. This may be a
   separate followup task.

4. **Acceptance for issue #301:** zero `base + N` literals where N is a
   3-/4-digit numeric outside `Compose/Offsets.lean`. Small intra-block
   sub-offsets like `+4`, `+8`, `+12` remain as-is per the existing
   convention.
