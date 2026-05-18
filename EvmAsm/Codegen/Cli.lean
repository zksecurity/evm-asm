/-
  EvmAsm.Codegen.Cli

  Argument parsing and top-level `main` for `lake exe codegen`.

  Usage:
    codegen --program <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]

  Writes `<basename>.s` and, unless `--asm-only`, also `<basename>.o` and
  `<basename>.elf` produced by `Driver.assembleAndLink`.
-/

import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs
import EvmAsm.Codegen.Driver

namespace EvmAsm.Codegen.Cli

open EvmAsm.Codegen
open EvmAsm.Codegen.Driver

structure Options where
  program  : String        := ""
  halt     : HaltConv      := .linux93
  outBase  : System.FilePath := "gen-out/out"
  asmOnly  : Bool          := false
  deriving Repr

def usage : String :=
  let progs := ", ".intercalate knownProgramNames
  "usage: codegen --program <name> [--halt sp1|linux93] [-o <basename>] [--asm-only]\n" ++
  s!"known programs: {progs}"

def parseArgs : List String → Options → Except String Options
  | [], opts =>
      if opts.program.isEmpty then .error "missing --program"
      else .ok opts
  | "--program" :: v :: rest, opts =>
      parseArgs rest { opts with program := v }
  | "--halt" :: v :: rest, opts =>
      match HaltConv.ofString? v with
      | some hc => parseArgs rest { opts with halt := hc }
      | none    => .error s!"unknown --halt value: {v} (use sp1 | linux93)"
  | "-o" :: v :: rest, opts
  | "--out" :: v :: rest, opts =>
      parseArgs rest { opts with outBase := v }
  | "--asm-only" :: rest, opts =>
      parseArgs rest { opts with asmOnly := true }
  | "--help" :: _, _ | "-h" :: _, _ =>
      .error "help"
  | bad :: _, _ =>
      .error s!"unknown argument or missing value: {bad}"

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error msg => do
      if msg ≠ "help" then IO.eprintln s!"codegen: {msg}"
      IO.eprintln usage
      return (if msg = "help" then 0 else 1)
  | .ok opts => do
      match lookupProgram opts.program with
      | none => do
          IO.eprintln s!"codegen: unknown program: {opts.program}"
          IO.eprintln usage
          return 1
      | some unit => do
          let text := emitBuildUnit opts.halt unit
          let asmPath : System.FilePath := opts.outBase.toString ++ ".s"
          writeAsmFile asmPath text
          IO.println s!"wrote {asmPath}"
          if opts.asmOnly then
            return 0
          try
            let (objPath, elfPath) ← assembleAndLink asmPath
            IO.println s!"wrote {objPath}"
            IO.println s!"wrote {elfPath}"
            return (0 : UInt32)
          catch e =>
            IO.eprintln s!"codegen: {e}"
            IO.eprintln "codegen: hint: install the riscv64 cross toolchain (e.g. `brew install riscv64-elf-binutils`) or pass --asm-only"
            return (1 : UInt32)

end EvmAsm.Codegen.Cli
