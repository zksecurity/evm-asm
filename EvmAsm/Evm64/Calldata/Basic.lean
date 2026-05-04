/-
  EvmAsm.Evm64.Calldata.Basic

  Pure calldata helpers for CALLDATALOAD/CALLDATACOPY work (GH #104 slice 1).
  CALLDATALOAD reads 32 bytes starting at a byte offset, interprets them as a
  big-endian 256-bit word, and pads reads past the calldata length with zero.
-/

import EvmAsm.Evm64.Basic

namespace EvmAsm.Evm64
namespace Calldata

/-- Read one calldata byte, returning zero past the end of the buffer. -/
def callDataByte (data : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  if h : idx < data.length then data[idx] else 0

/-- Fold one big-endian byte into an accumulator. -/
def appendByte (acc : Nat) (b : BitVec 8) : Nat :=
  acc * 256 + b.toNat

/-- Natural-number assembly of the 32-byte CALLDATALOAD window. This is the
    executable mathematical target; `callDataLoadWord` reduces it modulo
    `2^256` through `BitVec.ofNat 256`. -/
def callDataLoadNat (data : List (BitVec 8)) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => appendByte acc (callDataByte data (offset + i)))
    0

/-- CALLDATALOAD result word: 32 bytes from calldata, big-endian, zero-padded. -/
def callDataLoadWord (data : List (BitVec 8)) (offset : Nat) : EvmWord :=
  BitVec.ofNat 256 (callDataLoadNat data offset)

theorem callDataByte_of_lt {data : List (BitVec 8)} {idx : Nat}
    (h : idx < data.length) :
    callDataByte data idx = data[idx] := by
  simp [callDataByte, h]

theorem callDataByte_of_ge {data : List (BitVec 8)} {idx : Nat}
    (h : data.length ≤ idx) :
    callDataByte data idx = 0 := by
  simp [callDataByte, show ¬idx < data.length from by omega]

@[simp] theorem callDataByte_nil (idx : Nat) :
    callDataByte [] idx = 0 := by
  exact callDataByte_of_ge (data := []) (idx := idx) (by simp)

@[simp] theorem appendByte_zero :
    appendByte 0 0 = 0 := rfl

theorem callDataLoadNat_nil (offset : Nat) :
    callDataLoadNat [] offset = 0 := by
  have hmul : ∀ xs : List Nat, List.foldl (fun acc (_ : Nat) => acc * 256) 0 xs = 0 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih => simpa [List.foldl_cons] using ih
  simpa [callDataLoadNat, appendByte] using hmul (List.range 32)

theorem callDataLoadWord_nil (offset : Nat) :
    callDataLoadWord [] offset = 0 := by
  rw [callDataLoadWord, callDataLoadNat_nil]
  rfl

/-! ### CALLDATACOPY pure helper

`callDataCopyBytes data dataOffset size` is the byte sequence that
CALLDATACOPY writes into EVM memory: `size` bytes drawn from `data`
starting at `dataOffset`, zero-padding past the end of the calldata
buffer. This is the executable mathematical target consumed by the
CALLDATACOPY RISC-V program (evm-asm-r3sk / GH #104 slice 5);
defining it here keeps the pure helper colocated with `callDataByte`,
`callDataLoadWord`, and the rest of the pure calldata surface and
unblocks the CALLDATACOPY program slice from the pure-helper side.
-/

/-- The byte sequence written by CALLDATACOPY:
    `size` bytes from `data` starting at `dataOffset`, with
    out-of-bounds reads producing zero. Length is `size` by
    construction (see `callDataCopyBytes_length`). -/
def callDataCopyBytes
    (data : List (BitVec 8)) (dataOffset size : Nat) : List (BitVec 8) :=
  (List.range size).map (fun i => callDataByte data (dataOffset + i))

@[simp] theorem callDataCopyBytes_length
    (data : List (BitVec 8)) (dataOffset size : Nat) :
    (callDataCopyBytes data dataOffset size).length = size := by
  simp [callDataCopyBytes]

@[simp] theorem callDataCopyBytes_zero
    (data : List (BitVec 8)) (dataOffset : Nat) :
    callDataCopyBytes data dataOffset 0 = [] := by
  simp [callDataCopyBytes]

/-- Indexing into the copied byte buffer recovers a `callDataByte` read
    at the corresponding source offset. Useful for stepping through the
    CALLDATACOPY loop spec one byte at a time. -/
theorem callDataCopyBytes_get
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = callDataByte data (dataOffset + i) := by
  simp [callDataCopyBytes, List.getElem_map, List.getElem_range]

/-- Specialization of `callDataCopyBytes_get` to indices known to lie
    inside the source buffer: the result is the literal calldata byte. -/
theorem callDataCopyBytes_get_of_in_bounds
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) (hsrc : dataOffset + i < data.length) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = data[dataOffset + i] := by
  rw [callDataCopyBytes_get h, callDataByte_of_lt hsrc]

/-- Specialization of `callDataCopyBytes_get` to indices past the source
    buffer: the result is the zero-padding byte. -/
theorem callDataCopyBytes_get_of_out_of_bounds
    {data : List (BitVec 8)} {dataOffset size : Nat} {i : Nat}
    (h : i < size) (hsrc : data.length ≤ dataOffset + i) :
    (callDataCopyBytes data dataOffset size)[i]'(by
      simpa [callDataCopyBytes_length] using h)
      = 0 := by
  rw [callDataCopyBytes_get h, callDataByte_of_ge hsrc]

@[simp] theorem callDataCopyBytes_nil (dataOffset size : Nat) :
    callDataCopyBytes [] dataOffset size = List.replicate size 0 := by
  apply List.ext_getElem
  · simp [callDataCopyBytes_length]
  · intro i h₁ h₂
    have hi : i < size := by simpa [callDataCopyBytes_length] using h₁
    rw [callDataCopyBytes_get hi, callDataByte_nil, List.getElem_replicate]

end Calldata
end EvmAsm.Evm64
