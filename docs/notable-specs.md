# Notable Specs Index

A curated index of notable proven specifications across the EvmAsm codebase, with
permalinks to the exact theorem statements at a pinned commit. Use this page to
find a spec without grepping; refresh the permalinks when files move.

> **Permalinks pinned to commit `05b3babdd085aa629765d38f3d19126ef40007eb` on
> 2026-05-01.** Refresh whenever a major surface lands (e.g. each closure of a
> #61-class umbrella issue) or quarterly, whichever comes first. To refresh,
> re-run `git rev-parse origin/main` and `grep -n` for each declaration name,
> then update the line numbers below.

This index is split by area. Slice 1 (this PR) lands the page skeleton plus the
DivMod stack-spec surface. Subsequent slices will populate the remaining
sections.

---

## DivMod stack-spec surface

The path-specific stack-level Hoare triples for `DIV` and `MOD` and their
dispatcher-surface aliases. These are the consumer-facing entry points for
downstream verifiers — when proving a higher-level property, prefer the alias
over the underlying `_word_uni` / `_dispatch_uni` theorem so a future bound
relaxation propagates automatically.

### Dispatcher aliases

Defined in
[`EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean).

| Alias | Underlying theorem | Meaning |
|---|---|---|
| [`evm_div_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L18) | `evm_div_bzero_stack_spec_within` | DIV with divisor = 0 returns 0 (within bound 13). |
| [`evm_div_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L19) | `evm_div_n1_stack_spec_within_word_uni` | DIV with 1-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L20) | `evm_div_n2_stack_spec_within_word_uni` | DIV with 2-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L21) | `evm_div_n3_stack_spec_within_word_uni` | DIV with 3-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_div_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L22) | `evm_div_n4_stack_spec_within_dispatch_uni` | DIV with 4-limb divisor: stack-level result equals `EvmWord.div`. |
| [`evm_mod_stack_spec_within_bzero`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L24) | `evm_mod_bzero_stack_spec_within` | MOD with divisor = 0 returns 0 (within bound 13). |
| [`evm_mod_stack_spec_within_n1Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L25) | `evm_mod_n1_stack_spec_within_word_uni` | MOD with 1-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n2Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L26) | `evm_mod_n2_stack_spec_within_word_uni` | MOD with 2-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n3Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L27) | `evm_mod_n3_stack_spec_within_word_uni` | MOD with 3-limb divisor: stack-level result equals `EvmWord.mod`. |
| [`evm_mod_stack_spec_within_n4Full`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L28) | `evm_mod_n4_stack_spec_within_dispatch_uni` | MOD with 4-limb divisor: stack-level result equals `EvmWord.mod`. |

### Underlying proof-bearing theorems

| Theorem | Defined at |
|---|---|
| `evm_div_bzero_stack_spec_within` | [`Spec/Base.lean:904`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Base.lean#L904) |
| `evm_div_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:46`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L46) |
| `evm_div_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:87`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L87) |
| `evm_div_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:127`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L127) |
| `evm_div_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:166`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L166) |
| `evm_mod_bzero_stack_spec_within` | [`Spec/Base.lean:961`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Base.lean#L961) |
| `evm_mod_n1_stack_spec_within_word_uni` | [`Spec/Unified.lean:195`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L195) |
| `evm_mod_n2_stack_spec_within_word_uni` | [`Spec/Unified.lean:236`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L236) |
| `evm_mod_n3_stack_spec_within_word_uni` | [`Spec/Unified.lean:276`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L276) |
| `evm_mod_n4_stack_spec_within_dispatch_uni` | [`Spec/Unified.lean:315`](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/Unified.lean#L315) |

### Dispatcher registries

The `evm_div_stack_spec_within` and `evm_mod_stack_spec_within` registries
([Dispatcher.lean#L65](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L65),
[#L73](https://github.com/Verified-zkEVM/evm-asm/blob/05b3babdd085aa629765d38f3d19126ef40007eb/EvmAsm/Evm64/DivMod/Spec/StackDispatcher.lean#L73))
list every branch and the per-branch step bound. All non-`bzero` branches are
lifted to a single `unifiedDivBound`.

---

## Other Evm64 opcode stack specs

_TODO (slice 2): index `evm_add` / `evm_sub` / `evm_mul` / `evm_shl` / `evm_shr`
/ `evm_sar` / comparator / `evm_push_n` stack specs._

## EvmWord arithmetic correctness

_TODO (slice 2): index `EvmWord.div_correct`, `EvmWord.mod_correct`, etc._

## EL / RLP

_TODO (slice 3): index RLP encode/decode round-trip and per-phase decode specs._

## Rv64 infrastructure

_TODO (slice 3): index `ByteOps` LBU/SB specs, calling-convention helpers
(`callNear_spec`, `cc_prologue_spec`, `nonleaf_function_spec`, etc.)._

## Maintenance

- See parent backlog: `evm-asm-prwe` / GH issue tracking forthcoming.
- Trigger: refresh when a `#61`-class umbrella closes or quarterly,
  whichever comes first.

### Refresh procedure (5 steps)

1. **Survey the spec surface.** Grep for the canonical entry-point names so
   nothing has been added or renamed since the last refresh:

   ```bash
   rg -n '@\[stack_spec_' EvmAsm/
   rg -n 'theorem evm_[a-z_]*_stack_spec' EvmAsm/
   rg -n 'theorem EvmWord\.[a-z_]*_correct' EvmAsm/
   ```

   Add an entry to the appropriate section for any name not already listed;
   delete entries whose underlying theorem is gone.

2. **Capture `file:line` for every entry.** For each theorem name, locate
   its current declaration site:

   ```bash
   grep -n '<theorem-name>' EvmAsm/<path>.lean
   ```

   Record the `path:line` pair — both the alias line and (if separate) the
   underlying proof-bearing theorem line.

3. **Mint commit-pinned permalinks.** Capture the current upstream sha and
   build URLs against it:

   ```bash
   SHA=$(git rev-parse origin/main)
   gh browse <path>:<line> --commit "$SHA" --no-browser
   # or directly:
   echo "https://github.com/Verified-zkEVM/evm-asm/blob/$SHA/<path>#L<line>"
   ```

   Replace each existing permalink in the table cells with the freshly
   minted one.

4. **Update the top-of-page pin.** Replace the `Permalinks pinned to commit
   <sha> on <date>` blockquote near the top with the new sha and today's
   date.

5. **Verify with `lake build`.** Run `lake build` from the repo root to
   confirm every referenced declaration still elaborates under the pinned
   sha. Any rename or relocation discovered here loops back to step 1.
