/-
  EvmAsm.Codegen.Driver

  `IO` glue: write the emitted `.s` to disk and (optionally) shell out to a
  RISC-V binutils to produce an ELF.

  Toolchain discovery: binaries are usually named `riscv64-unknown-elf-{as,ld}`
  (the `riscv-software-src/riscv` brew tap, most Linux packages) but
  Homebrew's lightweight `riscv64-elf-binutils` formula installs them as
  `riscv64-elf-{as,ld}` instead. We probe both, with env-var overrides
  (`RISCV_AS`, `RISCV_LD`) for anything exotic.

  Toolchain absence is surfaced as a normal IO error by the CLI; CI hosts
  without binutils should pass `--asm-only`.
-/

namespace EvmAsm.Codegen.Driver

/-- Candidate names for the cross-as binary, in priority order. -/
def asCandidates : List String := ["riscv64-unknown-elf-as", "riscv64-elf-as"]

/-- Candidate names for the cross-ld binary, in priority order. -/
def ldCandidates : List String := ["riscv64-unknown-elf-ld", "riscv64-elf-ld"]

/-- Run a subprocess; throw an IO error containing stderr on non-zero exit. -/
def runOrFail (prog : String) (args : Array String) : IO Unit := do
  let res ← IO.Process.output { cmd := prog, args }
  if res.exitCode ≠ 0 then
    let argStr := " ".intercalate args.toList
    throw <| IO.userError
      s!"{prog} {argStr} failed (exit {res.exitCode}):\n{res.stderr}"

/-- Return the first candidate that resolves on `PATH`, or `none`. -/
def firstAvailable : List String → IO (Option String)
  | []      => return none
  | c :: cs => do
      let out ← IO.Process.output { cmd := "which", args := #[c] }
      if out.exitCode == 0 then return some c else firstAvailable cs

/-- Resolve a tool: env-var override first, then probe candidates on `PATH`,
    then fall back to the first candidate name so the resulting error message
    still mentions a real binary. -/
def resolveTool (envVar : String) (candidates : List String) : IO String := do
  match ← IO.getEnv envVar with
  | some v => return v
  | none =>
      match ← firstAvailable candidates with
      | some t => return t
      | none =>
          match candidates with
          | t :: _ => return t
          | []     => throw <| IO.userError s!"no candidates configured for {envVar}"

/-- Ensure the parent directory of `p` exists (no-op if it already does). -/
def ensureParentDir (p : System.FilePath) : IO Unit :=
  match p.parent with
  | some parent => IO.FS.createDirAll parent
  | none        => pure ()

/-- Write `text` to `asmPath`, creating parent directories as needed. -/
def writeAsmFile (asmPath : System.FilePath) (text : String) : IO Unit := do
  ensureParentDir asmPath
  IO.FS.writeFile asmPath text

/-- Assemble + link an emitted `.s` to a `.elf`, with `.o` as the intermediate.
    Returns the produced `(objPath, elfPath)`.

    Memory layout: `.text` at `0x80000000` (Zisk's default entry point),
    `.data` at `0xa0000000` (Zisk requires writable sections to live in RAM
    at `0xa0000000-0xc0000000`; placing `.data` adjacent to `.text` makes
    the loader refuse the ELF with "writable data section ... outside RAM
    bounds"). -/
def assembleAndLink (asmPath : System.FilePath) :
    IO (System.FilePath × System.FilePath) := do
  let asProgram ← resolveTool "RISCV_AS" asCandidates
  let ldProgram ← resolveTool "RISCV_LD" ldCandidates
  let objPath := asmPath.withExtension "o"
  let elfPath := asmPath.withExtension "elf"
  runOrFail asProgram
    #["-march=rv64imac", "-mno-relax", "-o", objPath.toString, asmPath.toString]
  runOrFail ldProgram
    #["-Ttext=0x80000000", "-Tdata=0xa0000000",
      "-nostdlib", "--no-relax",
      "-o", elfPath.toString, objPath.toString]
  return (objPath, elfPath)

end EvmAsm.Codegen.Driver
