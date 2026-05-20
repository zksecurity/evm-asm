/-
  EvmAsm.Codegen.Dispatch

  Declarative registry shape for the M5b runtime fetch/decode/dispatch
  loop. Each opcode is one `OpcodeHandlerSpec` entry; the helpers
  below render the dispatcher prologue, the 256-entry jump table, and
  the handler subroutines from a `List OpcodeHandlerSpec`.

  Adding a new opcode to the dispatcher = adding one entry to the
  registry. The dispatcher scaffolding (loop body, exit path, invalid
  fallback) stays here so `Programs.lean` only declares opcode-
  specific data.

  Per CODEGEN.md §Tricky bits #9 the loop scaffold is raw asm; only
  verified opcode bodies (rendered via `emitProgram`) sit inside the
  handler subroutines.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Tail emitted after each handler's verified body.

    `advanceAndRet width` is the standard subroutine return: advance
    the EVM PC (`x10`) by the opcode's byte width, then `ret` back to
    the dispatcher loop. `custom asm` is for handlers that don't
    return to the dispatcher (e.g. STOP → `j .exit_label`). -/
inductive HandlerTail where
  | advanceAndRet (width : Nat)
  | custom (asm : String)

/-- Spec for one opcode handler in the M5b dispatch registry. -/
structure OpcodeHandlerSpec where
  /-- Subroutine label (e.g. `"h_ADD"`). Must be unique across the
      registry; rendered as a label in the emitted asm and as a
      target in the 256-entry jump table. -/
  label   : String
  /-- Opcode bytes this handler covers. Bytes not claimed by any
      spec route to `h_invalid` via the jump table fill. -/
  opcodes : List Nat
  /-- Raw asm emitted *between* the label and the verified body.
      Used to save dispatcher-state registers that the verified body
      may clobber. For example, `evm_mul` / `evm_signextend` /
      `evm_byte` / `evm_shr` use `x10` as a scratch accumulator —
      our dispatcher expects `x10` to be the preserved EVM code
      pointer, so those handlers carry `preBody := "  mv x9, x10"`
      and a tail that restores via `mv x10, x9` before advancing.
      Empty string means "no save needed". -/
  preBody : String := ""
  /-- Verified RV64 body, rendered verbatim via `emitProgram`.
      May be empty (e.g. STOP has no work to do before exiting). -/
  body    : Program
  /-- Tail emitted after the body. -/
  tail    : HandlerTail

namespace OpcodeHandlerSpec

/-- Render a handler tail as raw asm. -/
def emitTail : HandlerTail → String
  | .advanceAndRet width => s!"  addi x10, x10, {width}\n  ret"
  | .custom asm          => asm

/-- Render the handler as a labeled subroutine. Empty bodies (STOP,
    INVALID-style entries) skip the body line entirely to avoid a
    blank line after the label. `preBody` is inserted between the
    label and the body (used for clobber-saving). -/
def emitSubroutine (h : OpcodeHandlerSpec) : String :=
  let preLine  := if h.preBody.isEmpty then "" else h.preBody ++ "\n"
  let bodyText := emitProgram h.body
  let bodyLine := if bodyText.isEmpty then "" else bodyText ++ "\n"
  s!"{h.label}:\n" ++ preLine ++ bodyLine ++ emitTail h.tail

end OpcodeHandlerSpec

/-- The label that opcode byte `b` should dispatch to. Bytes not
    claimed by any spec route to `h_invalid`. -/
def jumpTargetLabel (registry : List OpcodeHandlerSpec) (b : Nat) : String :=
  match registry.find? (fun h => h.opcodes.contains b) with
  | some h => h.label
  | none   => "h_invalid"

/-- Render the 256-entry jump table inside the `.data` section.
    Does *not* emit its own `.section .data` directive — the caller
    (`emitDispatcherDataSection`) opens the section once at the top. -/
def emitJumpTable (registry : List OpcodeHandlerSpec) : String :=
  let entries :=
    (List.range 256).map (fun b => s!"  .dword {jumpTargetLabel registry b}")
  ".balign 8\n" ++
  "opcode_handlers:\n" ++
  String.intercalate "\n" entries

/-- Dispatcher prologue: init EVM pointers (`x10` = code, `x12` =
    stack top, `x13` = EVM memory base) and enter the main
    fetch/decode/dispatch loop. Each iteration loads the opcode byte
    at `[x10]`, indexes the jump table, `jalr`s to the handler, then
    jumps back to `.dispatch_loop`.

    `x13` is added in M7 for the memory opcodes (MLOAD, MSTORE,
    MSTORE8). Handlers that don't touch memory ignore it; the verified
    bodies that do use it take `memBaseReg` as a Lean argument and our
    M7 handler entries pass `.x13`. -/
def emitDispatcherPrologue : String :=
  "  la x10, evm_code\n" ++
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory\n" ++
  ".dispatch_loop:\n" ++
  "  lbu x5, 0(x10)\n" ++
  "  la x6, opcode_handlers\n" ++
  "  slli x5, x5, 3\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  "  j .dispatch_loop"

/-- Dispatcher epilogue: handler subroutines (each ends with `ret` or
    `j .exit_label`), the `h_invalid` fallback, and `.exit_label`
    which runs `exitBody` (e.g. `evmAddEpilogue`) and falls through
    to the halt stub appended by `emitBuildUnit`. -/
def emitDispatcherEpilogue
    (registry : List OpcodeHandlerSpec) (exitBody : Program) : String :=
  String.intercalate "\n" (registry.map OpcodeHandlerSpec.emitSubroutine) ++ "\n" ++
  "h_invalid:\n" ++
  "  j .exit_label\n" ++
  ".exit_label:\n" ++
  emitProgram exitBody

/-- `.data` section layout (starts at `0xa0000000` per
    `Driver.lean`'s `-Tdata=...`):

    ```
    evm_code:         <bytecode> (~50 B)
    .balign 32
    evm_stack_low:    .zero 256             (256-byte EVM stack scratch)
    evm_stack_top:
    .balign 32
    evm_memory:       .zero 0x8000          (32 KiB EVM memory, M7 onward)
    .balign 8
    opcode_handlers:  256 × .dword (jump table, 2 KiB)
    ```

    Total: ~50 + 256 + 32768 + 2048 ≈ 35 KiB, well under the 64 KiB
    cap before `OUTPUT_ADDR = 0xa0010000`. Going beyond 32 KiB of
    EVM memory would risk overrunning OUTPUT_ADDR.

    The EVM stack region grows downward from `evm_stack_top`; safe at
    the worst-case M5b depth of 2 (= 64 bytes). The EVM memory region
    grows upward from `evm_memory` indexed by `memBaseReg + offset`. -/
def emitDispatcherDataSection
    (bytecodeBytes : String) (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "evm_code:\n" ++
  s!"  .byte {bytecodeBytes}\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++   -- 32 KiB EVM memory (M7 onward)
  emitJumpTable registry

/-! ## Runtime-bytecode dispatcher (M8.5)

    Variant of the dispatcher that reads its bytecode at runtime
    from ziskemu's `-i <file>` input region instead of baking it
    into `.data`. Lets a single ELF run any bytecode — the test
    harness packs each per-case bytecode into an input file and
    re-uses the same ELF.

    Reads bytecode at `INPUT_ADDR + INPUT_DATA_OFFSET = 0x40000010`
    (see `EvmAsm/Codegen/Programs.lean` for the symbolic constants).
    All other dispatcher state (stack scratch, evm_memory, jump
    table) is identical to the `.data`-baked variant — only the
    prologue's `la x10, evm_code` swaps to `li x10, 0x40000010`
    and the `.data` section drops the `evm_code:` block. -/

/-- Runtime-bytecode dispatcher prologue. Same fetch/decode/dispatch
    loop as `emitDispatcherPrologue`; differs only in how `x10` is
    initialised — pointed at the input region instead of an
    in-`.data` label. The hex literal `0x40000010` matches
    `INPUT_ADDR + INPUT_DATA_OFFSET` in `Programs.lean`. -/
def emitRuntimeDispatcherPrologue : String :=
  "  li x10, 0x40000010\n" ++   -- INPUT_ADDR + INPUT_DATA_OFFSET
  "  la x12, evm_stack_top\n" ++
  "  la x13, evm_memory\n" ++
  ".dispatch_loop:\n" ++
  "  lbu x5, 0(x10)\n" ++
  "  la x6, opcode_handlers\n" ++
  "  slli x5, x5, 3\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x7, 0(x6)\n" ++
  "  jalr x1, x7, 0\n" ++
  "  j .dispatch_loop"

/-- Runtime-bytecode `.data` section. Drops the `evm_code:` block
    (no baked bytecode); everything else matches the `.data`-baked
    variant. Same 32 KiB budget concerns. -/
def emitRuntimeDispatcherDataSection
    (registry : List OpcodeHandlerSpec) : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++   -- 32 KiB EVM memory (M7 onward)
  emitJumpTable registry

/-- Build a runtime-bytecode `BuildUnit` for `registry` + `exitBody`.
    The emitted ELF doesn't carry any bytecode — the test harness
    supplies it at runtime via `ziskemu -i <file>` (8-byte LE length
    prefix + raw bytes; see M4's input-region convention). -/
def buildRuntimeDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program) : BuildUnit := {
  body        := []
  prologueAsm := emitRuntimeDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitRuntimeDispatcherDataSection registry
}

/-- Build a `BuildUnit` that runs the dispatcher over `bytecodeBytes`
    using `registry`. `exitBody` is the verified `Program` invoked
    at `.exit_label` to surface the result (usually `evmAddEpilogue`). -/
def buildDispatchUnit
    (registry : List OpcodeHandlerSpec)
    (exitBody : Program)
    (bytecodeBytes : String) : BuildUnit := {
  body        := []
  prologueAsm := emitDispatcherPrologue
  epilogueAsm := emitDispatcherEpilogue registry exitBody
  dataAsm     := emitDispatcherDataSection bytecodeBytes registry
}

end EvmAsm.Codegen
