/-
  RiscVMacroAsm.SyscallSpecs

  CPS specifications for the HALT and WRITE macro instructions,
  proved by composing generalized per-instruction specs via structural rules
  (cpsTriple_seq, cpsTriple_seq_halt, frame embedding).
-/

import RiscVMacroAsm.Basic
import RiscVMacroAsm.Instructions
import RiscVMacroAsm.SepLogic
import RiscVMacroAsm.Execution
import RiscVMacroAsm.CPSSpec
import RiscVMacroAsm.ControlFlow
import Std.Tactic.BVDecide

namespace RiscVMacroAsm

-- ============================================================================
-- Section 1: Memory Buffer Assertion
-- ============================================================================

/-- Memory buffer: consecutive words at addr, addr+4, addr+8, ... -/
def memBufferIs : Addr → List Word → Assertion
  | _, [] => empAssertion
  | addr, w :: ws => (addr ↦ₘ w) ** memBufferIs (addr + 4) ws

theorem pcFree_memBufferIs (addr : Addr) (words : List Word) :
    (memBufferIs addr words).pcFree := by
  induction words generalizing addr with
  | nil => exact pcFree_emp
  | cons w ws ih => exact pcFree_sepConj (pcFree_memIs addr w) (ih (addr + 4))

/-- If memBufferIs holds, then readWords returns those words. -/
theorem readWords_of_holdsFor_memBufferIs {addr : Addr} {words : List Word}
    {s : MachineState}
    (h : (memBufferIs addr words).holdsFor s) :
    s.readWords addr words.length = words := by
  induction words generalizing addr with
  | nil => rfl
  | cons w ws ih =>
    simp only [memBufferIs] at h
    have hmem : s.getMem addr = w :=
      (holdsFor_memIs addr w s).mp (holdsFor_sepConj_elim_left h)
    have hrest := holdsFor_sepConj_elim_right h
    simp only [List.length_cons, MachineState.readWords]
    rw [hmem, ih hrest]

-- ============================================================================
-- Section 1b: readBytes ↔ memBufferIs Infrastructure
-- ============================================================================

/-- If memBufferIs holds, then getMem at each word offset returns the corresponding word. -/
theorem getMem_of_holdsFor_memBufferIs {addr : Addr} {words : List Word}
    {s : MachineState}
    (h : (memBufferIs addr words).holdsFor s) (k : Nat) (hk : k < words.length) :
    s.getMem (addr + BitVec.ofNat 32 (4 * k)) = words[k]'hk := by
  induction words generalizing addr k with
  | nil => simp at hk
  | cons w ws ih =>
    simp only [memBufferIs] at h
    cases k with
    | zero =>
      simp only [Nat.mul_zero, List.getElem_cons_zero]
      have : addr + BitVec.ofNat 32 0 = addr := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [this]; exact (holdsFor_memIs addr w s).mp (holdsFor_sepConj_elim_left h)
    | succ k' =>
      have hk' : k' < ws.length := by simp [List.length_cons] at hk; omega
      simp only [List.getElem_cons_succ]
      have : addr + BitVec.ofNat 32 (4 * (k' + 1)) = addr + 4 + BitVec.ofNat 32 (4 * k') := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [this]; exact ih (holdsFor_sepConj_elim_right h) k' hk'

/-- readBytes of 4 bytes at an aligned address equals the 4 extractBytes of the word. -/
theorem readBytes_4_of_getMem {addr : Addr} {w : Word} {s : MachineState}
    (hmem : s.getMem addr = w) (halign : addr &&& 3#32 = 0#32) :
    s.readBytes addr 4 = [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3] := by
  simp only [MachineState.readBytes, MachineState.getByte, alignToWord, byteOffset]
  have h0 : (addr &&& ~~~3#32) = addr := by bv_decide
  have h1 : ((addr + 1) &&& ~~~3#32) = addr := by bv_decide
  have h2 : ((addr + 1 + 1) &&& ~~~3#32) = addr := by bv_decide
  have h3 : ((addr + 1 + 1 + 1) &&& ~~~3#32) = addr := by bv_decide
  rw [h0, h1, h2, h3, hmem]
  have h0o : (addr &&& 3#32).toNat = 0 := by rw [halign]; rfl
  have h1a : ((addr + 1) &&& 3#32) = 1#32 := by bv_decide
  have h1o : ((addr + 1) &&& 3#32).toNat = 1 := by rw [h1a]; rfl
  have h2a : ((addr + 1 + 1) &&& 3#32) = 2#32 := by bv_decide
  have h2o : ((addr + 1 + 1) &&& 3#32).toNat = 2 := by rw [h2a]; rfl
  have h3a : ((addr + 1 + 1 + 1) &&& 3#32) = 3#32 := by bv_decide
  have h3o : ((addr + 1 + 1 + 1) &&& 3#32).toNat = 3 := by rw [h3a]; rfl
  rw [h0o, h1o, h2o, h3o]

/-- Adding 4 to an aligned address preserves alignment. -/
theorem aligned_add_4 {addr : Addr} (halign : addr &&& 3#32 = 0#32) :
    (addr + 4) &&& 3#32 = 0#32 := by bv_decide

/-- readBytes splits into prefix and suffix. -/
theorem readBytes_append (s : MachineState) (addr : Addr) (m n : Nat) :
    s.readBytes addr (m + n) = s.readBytes addr m ++ s.readBytes (addr + BitVec.ofNat 32 m) n := by
  induction m generalizing addr with
  | zero =>
    simp only [Nat.zero_add, MachineState.readBytes, List.nil_append]
    congr 1; apply BitVec.eq_of_toNat_eq; simp
  | succ k ih =>
    simp only [Nat.succ_add, MachineState.readBytes, List.cons_append]; congr 1
    rw [ih (addr + 1)]; congr 1; congr 1
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- readBytes of a word-aligned buffer equals flatMap extractByte of the words. -/
theorem readBytes_of_words {addr : Addr} {words : List Word} {s : MachineState}
    (hmem : ∀ (k : Nat) (hk : k < words.length), s.getMem (addr + BitVec.ofNat 32 (4 * k)) = words[k]'hk)
    (halign : addr &&& 3#32 = 0#32) :
    s.readBytes addr (4 * words.length) =
      words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3]) := by
  induction words generalizing addr with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_cons]
    rw [show 4 * (ws.length + 1) = 4 + 4 * ws.length from by omega]
    rw [readBytes_append]
    congr 1
    · have h0 := hmem 0 (Nat.zero_lt_succ _)
      simp only [Nat.mul_zero, List.getElem_cons_zero] at h0
      have : addr + BitVec.ofNat 32 0 = addr := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [this] at h0
      exact readBytes_4_of_getMem h0 halign
    · rw [show (BitVec.ofNat 32 4 : BitVec 32) = (4 : BitVec 32) from rfl]
      have hmem' : ∀ (k : Nat) (hk : k < ws.length),
          s.getMem (addr + 4 + BitVec.ofNat 32 (4 * k)) = ws[k]'hk := by
        intro k hk
        have := hmem (k + 1) (by simp [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at this
        have haddr_eq : addr + 4 + BitVec.ofNat 32 (4 * k) = addr + BitVec.ofNat 32 (4 * (k + 1)) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [haddr_eq]; exact this
      exact ih hmem' (aligned_add_4 halign)

/-- Taking n elements from a longer readBytes gives readBytes n. -/
theorem readBytes_take (s : MachineState) (addr : Addr) (n m : Nat) (h : n ≤ m) :
    (s.readBytes addr m).take n = s.readBytes addr n := by
  induction n generalizing addr m with
  | zero => simp [MachineState.readBytes]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      simp only [MachineState.readBytes, List.take_succ_cons]; congr 1
      exact ih (addr + 1) m' (by omega)

-- ============================================================================
-- Section 1c: Separation Logic Rearrangement Helpers
-- ============================================================================

/-- Swap elements 1 and 2 of a right-associative chain: A ** B ** C → B ** A ** C. -/
private theorem swap12_assertion (A B C : Assertion) :
    ∀ h, (A ** B ** C) h → (B ** A ** C) h :=
  fun h hab =>
    sepConj_mono_right (fun h' hca => (sepConj_comm C A h').mp hca) h
      ((sepConj_assoc B C A h).mp ((sepConj_comm A (B ** C) h).mp hab))

/-- Pull element from position 5 to position 1: A ** B ** C ** D ** E ** F → E ** A ** B ** C ** D ** F. -/
private theorem pullFifth (A B C D E F : Assertion) :
    ∀ h, (A ** B ** C ** D ** E ** F) h → (E ** A ** B ** C ** D ** F) h :=
  fun h hab =>
    swap12_assertion A E (B ** C ** D ** F) h
    (sepConj_mono_right (fun h' => swap12_assertion B E (C ** D ** F) h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion C E (D ** F) h'') h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => sepConj_mono_right (fun h''' => swap12_assertion D E F h''') h'') h') h hab)))

/-- Push element from position 1 to position 5: E ** A ** B ** C ** D ** F → A ** B ** C ** D ** E ** F. -/
private theorem pushFifth (A B C D E F : Assertion) :
    ∀ h, (E ** A ** B ** C ** D ** F) h → (A ** B ** C ** D ** E ** F) h :=
  fun h hab =>
    sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => sepConj_mono_right (fun h''' => swap12_assertion E D F h''') h'') h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion E C (D ** F) h'') h') h
    (sepConj_mono_right (fun h' => swap12_assertion E B (C ** D ** F) h') h
    (swap12_assertion E A (B ** C ** D ** F) h hab)))

/-- Pull 5th element to front at holdsFor level (within (P ** R)). -/
theorem holdsFor_pullFifth {A B C D E F R : Assertion} {s : MachineState}
    (h : ((A ** B ** C ** D ** E ** F) ** R).holdsFor s) :
    ((E ** A ** B ** C ** D ** F) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pullFifth A B C D E F h1 hh1, hh2⟩

/-- Push element from front back to 5th position at holdsFor level (within (P ** R)). -/
theorem holdsFor_pushFifth {A B C D E F R : Assertion} {s : MachineState}
    (h : ((E ** A ** B ** C ** D ** F) ** R).holdsFor s) :
    ((A ** B ** C ** D ** E ** F) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pushFifth A B C D E F h1 hh1, hh2⟩

-- ============================================================================
-- Section 2: appendPublicValues Infrastructure
-- ============================================================================

namespace PartialState

/-- appendPublicValues preserves compatibility for partial states
    that don't own publicValues. -/
theorem CompatibleWith_appendPublicValues {h : PartialState} {s : MachineState}
    {bytes : List (BitVec 8)}
    (hcompat : h.CompatibleWith s) (hnone : h.publicValues = none) :
    h.CompatibleWith (s.appendPublicValues bytes) := by
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => by rw [MachineState.getReg_appendPublicValues]; exact hr r v hv,
         fun a v hv => by rw [MachineState.getMem_appendPublicValues]; exact hm a v hv,
         fun v hv => by rw [MachineState.pc_appendPublicValues]; exact hpc v hv,
         fun v hv => by rw [hnone] at hv; exact absurd hv (by simp),
         fun v hv => by rw [MachineState.privateInput_appendPublicValues]; exact hpi v hv⟩

end PartialState

/-- If (publicValuesIs oldPV ** R).holdsFor s, then
    (publicValuesIs (oldPV ++ words) ** R).holdsFor (s.appendPublicValues words).
    R is automatically publicValues-free by disjointness with publicValuesIs. -/
theorem holdsFor_sepConj_publicValuesIs_appendPublicValues
    {oldPV bytes : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (hPR : ((publicValuesIs oldPV) ** R).holdsFor s) :
    ((publicValuesIs (oldPV ++ bytes)) ** R).holdsFor (s.appendPublicValues bytes) := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [publicValuesIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own publicValues (from disjointness)
  have hpv2 : h2.publicValues = none := by
    rcases hdisj.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPublicValues (oldPV ++ bytes)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, Or.inr hpv2, hdisj.2.2.2.2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPublicValues (oldPV ++ bytes) compatible with s.appendPublicValues bytes
  have hc1' : (PartialState.singletonPublicValues (oldPV ++ bytes)).CompatibleWith
      (s.appendPublicValues bytes) := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPublicValues] at hr,
            fun a w ha => by simp [PartialState.singletonPublicValues] at ha,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw,
            fun w hw => ?_,
            fun w hw => by simp [PartialState.singletonPublicValues] at hw⟩
    simp only [PartialState.singletonPublicValues] at hw
    rw [Option.some.injEq] at hw; subst hw
    rw [MachineState.publicValues_appendPublicValues]
    exact congrArg (· ++ bytes)
      ((PartialState.CompatibleWith_singletonPublicValues oldPV s).mp hc1)
  -- h2 compatible with s.appendPublicValues bytes
  have hc2' : h2.CompatibleWith (s.appendPublicValues bytes) :=
    PartialState.CompatibleWith_appendPublicValues hc2 hpv2
  exact ⟨(PartialState.singletonPublicValues (oldPV ++ bytes)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPublicValues (oldPV ++ bytes), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Section 2b: dropPrivateInput Infrastructure
-- ============================================================================

namespace PartialState

/-- Dropping bytes from privateInput preserves compatibility for partial states
    that don't own privateInput. -/
theorem CompatibleWith_dropPrivateInput {h : PartialState} {s : MachineState}
    {n : Nat}
    (hcompat : h.CompatibleWith s) (hnone : h.privateInput = none) :
    h.CompatibleWith { s with privateInput := s.privateInput.drop n } := by
  obtain ⟨hr, hm, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => hr r v hv,
         fun a v hv => hm a v hv,
         fun v hv => hpc v hv,
         fun v hv => hpv v hv,
         fun v hv => by rw [hnone] at hv; exact absurd hv (by simp)⟩

end PartialState

/-- If (privateInputIs allBytes ** R).holdsFor s, then
    (privateInputIs (allBytes.drop n) ** R).holdsFor {s with privateInput := s.privateInput.drop n}.
    R is automatically privateInput-free by disjointness with privateInputIs. -/
theorem holdsFor_sepConj_privateInputIs_drop
    {allBytes : List (BitVec 8)} {n : Nat} {R : Assertion} {s : MachineState}
    (hPR : ((privateInputIs allBytes) ** R).holdsFor s) :
    ((privateInputIs (allBytes.drop n)) ** R).holdsFor
      { s with privateInput := s.privateInput.drop n } := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [privateInputIs] at hh1; subst hh1; rw [← hunion] at hcompat
  -- h2 doesn't own privateInput (from disjointness)
  have hpi2 : h2.privateInput = none := by
    rcases hdisj.2.2.2.2 with h | h
    · simp [PartialState.singletonPrivateInput] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPrivateInput (allBytes.drop n)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, Or.inr hpi2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPrivateInput (allBytes.drop n) compatible with modified state
  have hc1' : (PartialState.singletonPrivateInput (allBytes.drop n)).CompatibleWith
      { s with privateInput := s.privateInput.drop n } := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPrivateInput] at hr,
            fun a w ha => by simp [PartialState.singletonPrivateInput] at ha,
            fun w hw => by simp [PartialState.singletonPrivateInput] at hw,
            fun w hw => by simp [PartialState.singletonPrivateInput] at hw,
            fun w hw => ?_⟩
    simp only [PartialState.singletonPrivateInput] at hw
    rw [Option.some.injEq] at hw; subst hw
    show s.privateInput.drop n = allBytes.drop n
    congr 1
    exact (PartialState.CompatibleWith_singletonPrivateInput allBytes s).mp hc1
  -- h2 compatible with modified state
  have hc2' : h2.CompatibleWith { s with privateInput := s.privateInput.drop n } :=
    PartialState.CompatibleWith_dropPrivateInput hc2 hpi2
  exact ⟨(PartialState.singletonPrivateInput (allBytes.drop n)).union h2,
         (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
         PartialState.singletonPrivateInput (allBytes.drop n), h2, hdisj', rfl, rfl, hh2⟩

-- ============================================================================
-- Section 2c: writeBytesAsWords Memory Update Infrastructure
-- ============================================================================

namespace PartialState

/-- writeBytesAsWords preserves compatibility for partial states
    that don't own the target memory addresses. -/
theorem CompatibleWith_writeBytesAsWords {h : PartialState} {s : MachineState}
    {base : Addr} {bytes : List (BitVec 8)}
    (hcompat : h.CompatibleWith s)
    (hnone : ∀ (k : Nat), k < (bytes.length + 3) / 4 → h.mem (base + BitVec.ofNat 32 (4 * k)) = none) :
    h.CompatibleWith (s.writeBytesAsWords base bytes) := by
  match bytes with
  | [] =>
    unfold MachineState.writeBytesAsWords
    exact hcompat
  | b :: bs =>
    unfold MachineState.writeBytesAsWords
    have h0 := hnone 0 (by simp)
    simp at h0
    apply CompatibleWith_writeBytesAsWords (base := base + 4) (bytes := (b :: bs).drop 4)
    · exact CompatibleWith_setMem hcompat h0
    · intro k hk
      have hlen_drop : ((b :: bs).drop 4).length = bs.length + 1 - 4 := by
        simp [List.length_drop]
      have : k + 1 < ((b :: bs).length + 3) / 4 := by
        rw [hlen_drop] at hk
        have : (b :: bs).length = bs.length + 1 := by simp
        rw [this]
        omega
      have hval := hnone (k + 1) this
      have haddr : base + 4 + BitVec.ofNat 32 (4 * k) = base + BitVec.ofNat 32 (4 * (k + 1)) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      rw [haddr]; exact hval
termination_by bytes.length
decreasing_by simp [List.length_drop]; omega

end PartialState

/-- Helper: unfold one step of bytesToWords on 4+ elements. -/
private theorem bytesToWords_cons4 (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    bytesToWords (b0 :: b1 :: b2 :: b3 :: rest) =
    bytesToWordLE [b0, b1, b2, b3] :: bytesToWords rest := by
  simp [bytesToWords]

/-- Helper: unfold one step of writeBytesAsWords on 4+ elements. -/
private theorem writeBytesAsWords_cons4 (s : MachineState) (base : Addr)
    (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    s.writeBytesAsWords base (b0 :: b1 :: b2 :: b3 :: rest) =
    (s.setMem base (bytesToWordLE [b0, b1, b2, b3])).writeBytesAsWords (base + 4) rest := by
  simp [MachineState.writeBytesAsWords]

/-- If (memBufferIs base oldWords ** R).holdsFor s and we write bytes of the same total size,
    then (memBufferIs base (bytesToWords bytes) ** R).holdsFor (s.writeBytesAsWords base bytes). -/
theorem holdsFor_sepConj_memBufferIs_writeBytesAsWords
    {base : Addr} {oldWords : List Word} {bytes : List (BitVec 8)} {R : Assertion}
    {s : MachineState}
    (hlen : bytes.length = 4 * oldWords.length)
    (hPR : ((memBufferIs base oldWords) ** R).holdsFor s) :
    ((memBufferIs base (bytesToWords bytes)) ** R).holdsFor (s.writeBytesAsWords base bytes) := by
  -- Generalize R for the induction to work with different frames
  suffices h : ∀ (oldWords' : List Word) (R' : Assertion) (base' : Addr) (bytes' : List (BitVec 8))
      (s' : MachineState),
      bytes'.length = 4 * oldWords'.length →
      ((memBufferIs base' oldWords') ** R').holdsFor s' →
      ((memBufferIs base' (bytesToWords bytes')) ** R').holdsFor (s'.writeBytesAsWords base' bytes') from
    h oldWords R base bytes s hlen hPR
  intro oldWords'
  induction oldWords' with
  | nil =>
    intro R' base' bytes' s' hlen' hPR'
    have : bytes' = [] := by cases bytes' <;> simp_all
    subst this
    simp [memBufferIs]
    exact hPR'
  | cons w ws ih =>
    intro R' base' bytes' s' hlen' hPR'
    -- bytes has at least 4 elements
    have hlen4 : bytes'.length ≥ 4 := by simp [List.length_cons] at hlen'; omega
    obtain ⟨b0, b1, b2, b3, rest, hbytes, hrest_len⟩ : ∃ b0 b1 b2 b3 rest,
        bytes' = b0 :: b1 :: b2 :: b3 :: rest ∧ rest.length = 4 * ws.length := by
      match bytes', hlen' with
      | b0 :: b1 :: b2 :: b3 :: rest, hlen' =>
        exact ⟨b0, b1, b2, b3, rest, rfl, by simp [List.length_cons] at hlen'; omega⟩
    subst hbytes
    -- Rewrite goal using the unfold lemmas
    rw [bytesToWords_cons4, writeBytesAsWords_cons4]
    -- Goal is now: ((memBufferIs base' (btwLE :: bytesToWords rest)) ** R').holdsFor (setMem.wbaw rest)
    -- which after memBufferIs unfold becomes:
    -- (((base' ↦ₘ btwLE) ** memBufferIs (base'+4) (bytesToWords rest)) ** R').holdsFor ...
    change (((base' ↦ₘ bytesToWordLE [b0, b1, b2, b3]) ** memBufferIs (base' + 4) (bytesToWords rest)) ** R').holdsFor _
    -- hPR' : (((base' ↦ₘ w) ** memBufferIs (base'+4) ws) ** R').holdsFor s'
    change (((base' ↦ₘ w) ** memBufferIs (base' + 4) ws) ** R').holdsFor s' at hPR'
    -- Reassociate: (base' ↦ₘ w) ** (memBufferIs ws ** R')
    have hPR'' := holdsFor_sepConj_assoc.mp hPR'
    -- Update memory at base': (base' ↦ₘ newWord) ** (memBufferIs ws ** R')
    let newWord := bytesToWordLE [b0, b1, b2, b3]
    have h1 : ((base' ↦ₘ newWord) ** (memBufferIs (base' + 4) ws ** R')).holdsFor
        (s'.setMem base' newWord) :=
      holdsFor_sepConj_memIs_setMem hPR''
    -- Reassociate: ((base' ↦ₘ newWord) ** memBufferIs ws) ** R'
    have h1c := holdsFor_sepConj_assoc.mpr h1
    -- pull_second: memBufferIs ws ** ((base' ↦ₘ newWord) ** R')
    have h1d := holdsFor_sepConj_pull_second.mp h1c
    -- Apply IH with R'' = (base' ↦ₘ newWord) ** R'
    have h3 := ih ((base' ↦ₘ newWord) ** R') (base' + 4) rest (s'.setMem base' newWord) hrest_len h1d
    -- h3 : (memBufferIs (base'+4) (bytesToWords rest) ** ((base' ↦ₘ newWord) ** R')).holdsFor ...
    -- pull_second back: ((base' ↦ₘ newWord) ** memBufferIs (base'+4) (bytesToWords rest)) ** R'
    exact holdsFor_sepConj_pull_second.mpr h3

-- ============================================================================
-- Section 3: Generalized Instruction Specs
-- ============================================================================

/-- LW spec for any code memory: loads mem[rs1 + sext(offset)] into rd. -/
theorem lw_spec_gen (code : CodeMem) (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hfetch : code addr = some (Instr.LW rd rs1 offset))
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.LW rd rs1 offset) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v_addr :=
    (holdsFor_regIs rs1 v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  let mem_addr := v_addr + signExtend12 offset
  have hmem_val : st.getMem mem_addr = mem_val :=
    (holdsFor_memIs mem_addr mem_val st).mp
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hinner))
  have hnext : execInstrBr st (Instr.LW rd rs1 offset) =
      (st.setReg rd mem_val).setPC (st.pc + 4) := by
    simp [execInstrBr, mem_addr, hrs1_val, hmem_val]
  have hstep : step code st = some ((st.setReg rd mem_val).setPC (addr + 4)) := by
    have := step_lw _ _ _ _ _ hfetch' (by rw [hrs1_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setReg rd mem_val).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · -- Rearrange to get (rd ↦ᵣ v_old) at front, apply setReg, then reverse
    have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_assoc.mp h1
    have h3 := holdsFor_sepConj_regIs_setReg (v' := mem_val) hrd_ne_x0 h2
    have h4 := holdsFor_sepConj_assoc.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj
        (pcFree_sepConj (pcFree_regIs rs1 v_addr)
          (pcFree_sepConj (pcFree_regIs rd mem_val) (pcFree_memIs _ mem_val)))
        hR)
      (st.setReg rd mem_val) (addr + 4) h5

/-- SLTIU spec for any code memory (rd == rs1 case):
    rd := (v <u sext(imm)) ? 1 : 0 -/
theorem sltiu_spec_gen_same (code : CodeMem) (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0)
    (hfetch : code addr = some (Instr.SLTIU rd rd imm)) :
    cpsTriple code addr (addr + 4) (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word))) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.SLTIU rd rd imm) := by rw [hpc]; exact hfetch
  have hrd_val : st.getReg rd = v :=
    (holdsFor_regIs rd v st).mp (holdsFor_sepConj_elim_left hPR)
  let result := if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word)
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR)
      (st.setReg rd result) (addr + 4)
      (holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR)

/-- XORI spec for any code memory (rd == rs1 case):
    rd := v ^^^ sext(imm) -/
theorem xori_spec_gen_same (code : CodeMem) (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0)
    (hfetch : code addr = some (Instr.XORI rd rd imm)) :
    cpsTriple code addr (addr + 4) (rd ↦ᵣ v)
      (rd ↦ᵣ (v ^^^ signExtend12 imm)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.XORI rd rd imm) := by rw [hpc]; exact hfetch
  have hrd_val : st.getReg rd = v :=
    (holdsFor_regIs rd v st).mp (holdsFor_sepConj_elim_left hPR)
  let result := v ^^^ signExtend12 imm
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR)
      (st.setReg rd result) (addr + 4)
      (holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR)

/-- ADD spec for any code memory (rd = rs1 case):
    rd := rd + rs2 -/
theorem add_spec_gen_rd_eq_rs1 (code : CodeMem) (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2)
    (hfetch : code addr = some (Instr.ADD rd rd rs2)) :
    cpsTriple code addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.ADD rd rd rs2) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  let result := v1 + v2
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hrs2_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (addr + 4) h2

/-- SUB spec for any code memory (rd = rs1 case):
    rd := rd - rs2 -/
theorem sub_spec_gen_rd_eq_rs1 (code : CodeMem) (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2)
    (hfetch : code addr = some (Instr.SUB rd rd rs2)) :
    cpsTriple code addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.SUB rd rd rs2) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  let result := v1 - v2
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hrs2_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (addr + 4) h2

/-- AND spec for any code memory (rd = rs1 case):
    rd := rd &&& rs2 -/
theorem and_spec_gen_rd_eq_rs1 (code : CodeMem) (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2)
    (hfetch : code addr = some (Instr.AND rd rd rs2)) :
    cpsTriple code addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.AND rd rd rs2) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  let result := v1 &&& v2
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hrs2_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (addr + 4) h2

/-- OR spec for any code memory (rd = rs1 case):
    rd := rd ||| rs2 -/
theorem or_spec_gen_rd_eq_rs1 (code : CodeMem) (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2)
    (hfetch : code addr = some (Instr.OR rd rd rs2)) :
    cpsTriple code addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.OR rd rd rs2) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  let result := v1 ||| v2
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hrs2_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (addr + 4) h2

/-- XOR spec for any code memory (rd = rs1 case):
    rd := rd ^^^ rs2 -/
theorem xor_spec_gen_rd_eq_rs1 (code : CodeMem) (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2)
    (hfetch : code addr = some (Instr.XOR rd rd rs2)) :
    cpsTriple code addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.XOR rd rd rs2) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have ⟨hrd_val, hrs2_val⟩ := (holdsFor_sepConj_regIs_regIs hne).mp hinner
  let result := v1 ^^^ v2
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hrs2_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have hPR' := RiscVMacroAsm.holdsFor_sepConj_assoc.1 hPR
    have h1 := holdsFor_sepConj_regIs_setReg (v' := result) (R := (rs2 ↦ᵣ v2) ** R) hrd_ne_x0 hPR'
    have h2 := RiscVMacroAsm.holdsFor_sepConj_assoc.2 h1
    exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rd result) (pcFree_regIs rs2 v2)) hR) (st.setReg rd result) (addr + 4) h2

/-- ADDI spec for any code memory (rd = rs1 case):
    rd := rd + signExtend12(imm) -/
theorem addi_spec_gen_same (code : CodeMem) (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0)
    (hfetch : code addr = some (Instr.ADDI rd rd imm)) :
    cpsTriple code addr (addr + 4) (rd ↦ᵣ v) (rd ↦ᵣ (v + signExtend12 imm)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.ADDI rd rd imm) := by rw [hpc]; exact hfetch
  have hrd_val : st.getReg rd = v :=
    (holdsFor_regIs rd v st).mp (holdsFor_sepConj_elim_left hPR)
  let result := v + signExtend12 imm
  have hstep : step code st = some ((st.setReg rd result).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hrd_val, hpc, result]
  refine ⟨1, (st.setReg rd result).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd result) hR)
      (st.setReg rd result) (addr + 4)
      (holdsFor_sepConj_regIs_setReg (v' := result) hrd_ne_x0 hPR)

/-- LI spec for any code memory (not just a single-instruction loadProgram). -/
theorem li_spec_gen (code : CodeMem) (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hfetch : code addr = some (Instr.LI rd imm)) :
    cpsTriple code addr (addr + 4) (rd ↦ᵣ v_old) (rd ↦ᵣ imm) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.LI rd imm) := by rw [hpc]; exact hfetch
  have hstep : step code st = some ((st.setReg rd imm).setPC (addr + 4)) := by
    rw [step_non_ecall_non_mem code st _ hfetch' (by nofun) (by nofun) (by rfl)]
    simp [execInstrBr, hpc]
  refine ⟨1, (st.setReg rd imm).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (pcFree_regIs rd imm) hR)
      (st.setReg rd imm) (addr + 4)
      (holdsFor_sepConj_regIs_setReg (v' := imm) hrd_ne_x0 hPR)

/-- LI spec for any code memory with regOwn (no v_old needed). -/
theorem li_spec_gen_own (code : CodeMem) (rd : Reg) (imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) (hfetch : code addr = some (Instr.LI rd imm)) :
    cpsTriple code addr (addr + 4) (regOwn rd) (rd ↦ᵣ imm) := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h1, h2, hd, hu, ⟨v_old, hrd1⟩, hR2⟩ := hPR
  exact li_spec_gen code rd v_old imm addr hrd_ne_x0 hfetch R hR s
    ⟨hp, hcompat, h1, h2, hd, hu, hrd1, hR2⟩ hpc

/-- ECALL halt spec: when x5 = 0, ECALL halts. -/
theorem ecall_halt_spec_gen (code : CodeMem) (exitCode : Word) (addr : Addr)
    (hfetch : code addr = some .ECALL) :
    cpsHaltTriple code addr
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR st hPR hpc
  have hinner := holdsFor_sepConj_elim_left hPR
  have hx5 : st.getReg .x5 = 0 :=
    (holdsFor_regIs .x5 (0 : Word) st).mp (holdsFor_sepConj_elim_left hinner)
  have hhalt : step code st = none :=
    step_ecall_halt code st (by rw [hpc]; exact hfetch) hx5
  exact ⟨0, st, rfl, by simp [isHalted, hhalt], hPR⟩

/-- SW rs1 rs2 offset: mem[rs1 + sext(offset)] := rs2 (generalized for any CodeMem) -/
theorem sw_spec_gen (code : CodeMem) (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hfetch : code addr = some (Instr.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR st hPR hpc
  have hfetch' : code st.pc = some (Instr.SW rs1 rs2 offset) := by rw [hpc]; exact hfetch
  have hinner := holdsFor_sepConj_elim_left hPR
  have hrs1_val : st.getReg rs1 = v_addr :=
    (holdsFor_regIs rs1 v_addr st).mp (holdsFor_sepConj_elim_left hinner)
  have hrs2_val : st.getReg rs2 = v_data :=
    (holdsFor_regIs rs2 v_data st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hinner))
  let mem_addr := v_addr + signExtend12 offset
  have hnext : execInstrBr st (Instr.SW rs1 rs2 offset) = (st.setMem mem_addr v_data).setPC (st.pc + 4) := by
    simp [execInstrBr, mem_addr, hrs1_val, hrs2_val]
  have hstep : step code st = some ((st.setMem mem_addr v_data).setPC (addr + 4)) := by
    have := step_sw _ _ _ _ _ hfetch' (by rw [hrs1_val]; exact hvalid)
    rw [this, hnext, hpc]
  refine ⟨1, (st.setMem mem_addr v_data).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hstep, Option.bind]
  · simp [MachineState.setPC]
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIs_setMem (v' := v_data) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj (pcFree_regIs rs1 v_addr) (pcFree_sepConj (pcFree_regIs rs2 v_data) (pcFree_memIs _ v_data))) hR)
      (st.setMem mem_addr v_data) (addr + 4) h5

/-- SW spec with memOwn (no mem_old needed). -/
theorem sw_spec_gen_own (code : CodeMem) (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hfetch : code addr = some (Instr.SW rs1 rs2 offset))
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h_inner, h_R, hdisj, hunion, hInner, hRest⟩ := hPR
  obtain ⟨h1, hr1, hd1, hu1, hv_addr, hrest1⟩ := hInner
  obtain ⟨h2, hr2, hd2, hu2, hv_data, ⟨mem_old, hmem⟩⟩ := hrest1
  exact sw_spec_gen code rs1 rs2 v_addr v_data mem_old offset addr hfetch hvalid R hR s
    ⟨hp, hcompat, h_inner, h_R, hdisj, hunion,
      ⟨h1, hr1, hd1, hu1, hv_addr, ⟨h2, hr2, hd2, hu2, hv_data, hmem⟩⟩, hRest⟩ hpc

-- ============================================================================
-- Section 4: Frame Embedding for cpsTriple
-- ============================================================================

/-- Frame on the right: if cpsTriple P → Q, then cpsTriple (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (code : CodeMem) (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hpc', hQFR'⟩ := h (F ** R) hFR s hPFR' hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hQFR'⟩

/-- Frame on the left: if cpsTriple P → Q, then cpsTriple (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (code : CodeMem) (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple code entry exit_ P Q) :
    cpsTriple code entry exit_ (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have h1 := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hpc', hQFR⟩ := h (F ** R) hFR s h1 hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hQFR⟩

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (code : CodeMem) (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry (P ** F) (Q ** F) := by
  intro R hR s hPFR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have hPFR' := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, s', hstep, hhalt, hQFR'⟩ := h (F ** R) hFR s hPFR' hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_assoc.mpr hQFR'⟩

/-- Frame on the left for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_right (code : CodeMem) (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple code entry P Q) :
    cpsHaltTriple code entry (F ** P) (F ** Q) := by
  intro R hR s hFPR hpc
  have hFR : (F ** R).pcFree := pcFree_sepConj hF hR
  have h1 := holdsFor_sepConj_pull_second.mp hFPR
  obtain ⟨k, s', hstep, hhalt, hQFR⟩ := h (F ** R) hFR s h1 hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_sepConj_pull_second.mpr hQFR⟩

-- ============================================================================
-- Section 5: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem, given fetch proofs for the 3 instructions.
    Uses regOwn (no old values needed). -/
theorem halt_spec_gen (code : CodeMem) (exitCode : Word) (base : Addr)
    (hf0 : code base = some (Instr.LI .x5 0))
    (hf1 : code (base + 4) = some (Instr.LI .x10 exitCode))
    (hf2 : code (base + 8) = some .ECALL) :
    cpsHaltTriple code base
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  -- Step 1: LI x5 0 (base → base+4), frame regOwn .x10
  have s1 : cpsTriple code base (base + 4) (regOwn .x5) (.x5 ↦ᵣ (0 : Word)) :=
    li_spec_gen_own code .x5 0 base (by decide) hf0
  have s1' : cpsTriple code base (base + 4)
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** regOwn .x10) :=
    cpsTriple_frame_left code base (base + 4) _ _ _ (pcFree_regOwn .x10) s1
  -- Step 2: LI x10 exitCode (base+4 → base+8), frame .x5 ↦ᵣ 0
  have h_four_four : base + 4 + 4 = base + 8 := by grind
  have s2 : cpsTriple code (base + 4) (base + 8) (regOwn .x10) (.x10 ↦ᵣ exitCode) := by
    have := li_spec_gen_own code .x10 exitCode (base + 4) (by decide) hf1
    simp only [h_four_four] at this; exact this
  have s2' : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ _ (pcFree_regIs .x5 (0 : Word)) s2
  -- Step 3: ECALL halt (base+8, halts)
  have s3 : cpsHaltTriple code (base + 8)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
    ecall_halt_spec_gen code exitCode (base + 8) hf2
  exact cpsTriple_seq_halt code base (base + 8) _ _ _
    (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1' s2') s3

-- ============================================================================
-- Section 5a: Combined store word spec (LI x6 val ;; SW x7 x6 offset)
-- ============================================================================

/-- Combined spec for "LI x6, val ;; SW x7, x6, offset":
    Stores val at mem[x7_val + sext(offset)], updates x6 to val.
    Proved directly as a 2-step execution. -/
theorem storeWord_spec_gen (code : CodeMem) (val : Word) (offset : BitVec 12)
    (x6_old x7_val mem_old : Word) (addr : Addr)
    (hfetch_li : code addr = some (Instr.LI .x6 val))
    (hfetch_sw : code (addr + 4) = some (Instr.SW .x7 .x6 offset))
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 8)
      ((.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  -- Step 1: LI x6, val (addr → addr+4), frame x7 and mem
  let mem_addr := x7_val + signExtend12 offset
  have s1 : cpsTriple code addr (addr + 4) (.x6 ↦ᵣ x6_old) (.x6 ↦ᵣ val) :=
    li_spec_gen code .x6 x6_old val addr (by decide) hfetch_li
  have s1' : cpsTriple code addr (addr + 4)
      ((.x6 ↦ᵣ x6_old) ** ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old)))
      ((.x6 ↦ᵣ val) ** ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))) :=
    cpsTriple_frame_left code addr (addr + 4) _ _ ((.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))
      (pcFree_sepConj (pcFree_regIs .x7 x7_val) (pcFree_memIs mem_addr mem_old)) s1
  -- Step 2: SW x7, x6, offset (addr+4 → addr+8), frame x6
  have h48 : addr + 4 + 4 = addr + 8 := by grind
  have s2' : cpsTriple code (addr + 4) (addr + 8)
      ((.x7 ↦ᵣ x7_val) ** (.x6 ↦ᵣ val) ** (mem_addr ↦ₘ mem_old))
      ((.x7 ↦ᵣ x7_val) ** (.x6 ↦ᵣ val) ** (mem_addr ↦ₘ val)) := by
    have sw := sw_spec_gen code .x7 .x6 x7_val val mem_old offset (addr + 4) hfetch_sw hvalid
    simp only [h48] at sw; exact sw
  have swap12 : ∀ (A B C : Assertion) h, (A ** B ** C) h → (B ** A ** C) h :=
    fun A B C h hab =>
      sepConj_mono_right (fun h' hca => (sepConj_comm C A h').mp hca) h
        ((sepConj_assoc B C A h).mp
          ((sepConj_comm A (B ** C) h).mp hab))
  have s2'' : cpsTriple code (addr + 4) (addr + 8)
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** (mem_addr ↦ₘ val)) :=
    cpsTriple_consequence code (addr + 4) (addr + 8) _ _ _ _
      (swap12 (.x6 ↦ᵣ val) (.x7 ↦ᵣ x7_val) (mem_addr ↦ₘ mem_old))
      (swap12 (.x7 ↦ᵣ x7_val) (.x6 ↦ᵣ val) (mem_addr ↦ₘ val))
      s2'
  exact cpsTriple_seq code addr (addr + 4) (addr + 8) _ _ _ s1' s2''

/-- Combined LI+SW spec with regOwn and memOwn (no x6_old or mem_old needed). -/
theorem storeWord_spec_gen_own (code : CodeMem) (val : Word) (offset : BitVec 12)
    (x7_val : Word) (addr : Addr)
    (hfetch_li : code addr = some (Instr.LI .x6 val))
    (hfetch_sw : code (addr + 4) = some (Instr.SW .x7 .x6 offset))
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple code addr (addr + 8)
      (regOwn .x6 ** (.x7 ↦ᵣ x7_val) ** memOwn (x7_val + signExtend12 offset))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  intro R hR s hPR hpc
  obtain ⟨hp, hcompat, h_inner, h_R, hdisj, hunion, hInner, hRest⟩ := hPR
  obtain ⟨h1, hr1, hd1, hu1, ⟨x6_old, hx6⟩, hrest1⟩ := hInner
  obtain ⟨h2, hr2, hd2, hu2, hx7, ⟨mem_old, hmem⟩⟩ := hrest1
  exact storeWord_spec_gen code val offset x6_old x7_val mem_old addr
    hfetch_li hfetch_sw hvalid R hR s
    ⟨hp, hcompat, h_inner, h_R, hdisj, hunion,
      ⟨h1, hr1, hd1, hu1, hx6, ⟨h2, hr2, hd2, hu2, hx7, hmem⟩⟩, hRest⟩ hpc

-- ============================================================================
-- Section 5b: ECALL HINT_READ specification
-- ============================================================================

/-- Pull element from position 4 to position 1: A ** B ** C ** D ** E → D ** A ** B ** C ** E. -/
private theorem pullFourth (A B C D E : Assertion) :
    ∀ h, (A ** B ** C ** D ** E) h → (D ** A ** B ** C ** E) h :=
  fun h hab =>
    swap12_assertion A D (B ** C ** E) h
    (sepConj_mono_right (fun h' => swap12_assertion B D (C ** E) h') h
    (sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion C D E h'') h') h hab))

/-- Push element from position 1 to position 4: D ** A ** B ** C ** E → A ** B ** C ** D ** E. -/
private theorem pushFourth (A B C D E : Assertion) :
    ∀ h, (D ** A ** B ** C ** E) h → (A ** B ** C ** D ** E) h :=
  fun h hab =>
    sepConj_mono_right (fun h' => sepConj_mono_right (fun h'' => swap12_assertion D C E h'') h') h
    (sepConj_mono_right (fun h' => swap12_assertion D B (C ** E) h') h
    (swap12_assertion D A (B ** C ** E) h hab))

/-- Pull 4th element to front at holdsFor level. -/
theorem holdsFor_pullFourth {A B C D E R : Assertion} {s : MachineState}
    (h : ((A ** B ** C ** D ** E) ** R).holdsFor s) :
    ((D ** A ** B ** C ** E) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pullFourth A B C D E h1 hh1, hh2⟩

/-- Push element from front back to 4th position at holdsFor level. -/
theorem holdsFor_pushFourth {A B C D E R : Assertion} {s : MachineState}
    (h : ((D ** A ** B ** C ** E) ** R).holdsFor s) :
    ((A ** B ** C ** D ** E) ** R).holdsFor s := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := h
  exact ⟨hp, hcompat, h1, h2, hdisj, hunion, pushFourth A B C D E h1 hh1, hh2⟩

/-- Single ECALL step for HINT_READ (t0 = 0xF1).
    Precondition: x5 = 0xF1, x10 = bufAddr, x11 = nbytes,
                  privateInput = inputBytes, memory buffer at bufAddr = oldWords.
    Postcondition: same registers, privateInput = inputBytes.drop nbytes.toNat,
                   memory buffer = bytesToWords (inputBytes.take nbytes.toNat). -/
theorem ecall_hint_read_spec_gen (code : CodeMem) (bufAddr nbytes : Word)
    (inputBytes : List (BitVec 8)) (oldWords : List Word) (addr : Addr)
    (hfetch : code addr = some .ECALL)
    (hLen : nbytes.toNat ≤ inputBytes.length)
    (hNbytes : nbytes.toNat = 4 * oldWords.length) :
    cpsTriple code addr (addr + 4)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))) := by
  intro R hR st hPR hpc
  -- Extract register values from the 5-part conjunction ** R
  have hP := holdsFor_sepConj_elim_left hPR
  have hx5 : st.getReg .x5 = 0xF1#32 :=
    (holdsFor_regIs .x5 _ st).mp (holdsFor_sepConj_elim_left hP)
  have hx10 : st.getReg .x10 = bufAddr :=
    (holdsFor_regIs .x10 _ st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hP))
  have hx11 : st.getReg .x11 = nbytes :=
    (holdsFor_regIs .x11 _ st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hP)))
  -- Extract privateInputIs value
  have hPI := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hP))
  have hPIval : st.privateInput = inputBytes :=
    (holdsFor_privateInputIs inputBytes st).mp (holdsFor_sepConj_elim_left hPI)
  -- Sufficient input check
  have hsuff : nbytes.toNat ≤ st.privateInput.length := by rw [hPIval]; exact hLen
  have hsuff' : (st.getReg .x11).toNat ≤ st.privateInput.length := by rw [hx11]; exact hsuff
  -- Step computation
  have hfetch' : code st.pc = some .ECALL := by rw [hpc]; exact hfetch
  have hstep := step_ecall_hint_read code st hfetch' hx5 hsuff'
  -- Step computation
  have hNewState : step code st =
      some (({ st with privateInput := st.privateInput.drop nbytes.toNat }.writeBytesAsWords
        bufAddr (st.privateInput.take nbytes.toNat)).setPC (addr + 4)) := by
    rw [hstep, hx11, hx10, hpc]
  -- Build the witness
  have hPI_eq : st.privateInput.take nbytes.toNat = inputBytes.take nbytes.toNat := by
    rw [hPIval]
  refine ⟨1, ({ st with privateInput := st.privateInput.drop nbytes.toNat }.writeBytesAsWords
    bufAddr (inputBytes.take nbytes.toNat)).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hNewState, Option.bind, hPI_eq]
  · simp [MachineState.setPC]
  · -- Reconstruct postcondition via three state modification layers
    -- The state is:
    --   ({ st with privateInput := ... }.writeBytesAsWords bufAddr ...).setPC (addr + 4)
    -- We handle: (1) privateInput drop, (2) writeBytesAsWords, (3) setPC

    -- Step 1: privateInput drop
    -- Pull privateInputIs to front (position 4 → 1)
    have h1 := holdsFor_pullFourth hPR
    -- h1 : ((privateInputIs inputBytes ** x5 ** x10 ** x11 ** memBufferIs) ** R).holdsFor st
    have h1a := holdsFor_sepConj_assoc.mp h1
    -- Apply privateInput drop
    have h2 := holdsFor_sepConj_privateInputIs_drop (n := nbytes.toNat) h1a
    -- Push privateInputIs back to position 4
    have h2a := holdsFor_sepConj_assoc.mpr h2
    have h3 := holdsFor_pushFourth h2a
    -- h3 : ((x5 ** x10 ** x11 ** privateInputIs (drop) ** memBufferIs) ** R).holdsFor s'
    -- where s' = { st with privateInput := st.privateInput.drop n }

    -- Step 2: writeBytesAsWords on memBufferIs
    -- Rearrange: we need memBufferIs at the front for holdsFor_sepConj_memBufferIs_writeBytesAsWords
    -- Structure: ((A ** B ** C ** D ** E) ** R) where E = memBufferIs
    -- Reassociate to get E next to R: ((A ** B ** C ** D) ** (E ** R))
    -- Then swap to get (E ** (A ** B ** C ** D) ** R)... but this requires more complex maneuvers.
    -- Simpler: use pull_second repeatedly to get memBufferIs to front in the inner assertion.

    -- Inner: x5 ** x10 ** x11 ** privateInputIs(drop) ** memBufferIs
    -- We want: memBufferIs ** x5 ** x10 ** x11 ** privateInputIs(drop)
    -- Use comm at the inner level: swap (privateInputIs ** memBufferIs) to (memBufferIs ** privateInputIs)

    -- Actually, since our holdsFor_sepConj_memBufferIs_writeBytesAsWords works with any R,
    -- we just need memBufferIs at the outermost left position in the P ** R decomposition.
    -- Let's reassociate so that the inner part becomes (memBufferIs ** frame) for some frame.

    -- From h3: ((x5 ** x10 ** x11 ** privateInputIs ** memBufferIs) ** R)
    -- We need to get memBufferIs to the left: reassociate inner as
    -- (x5 ** x10 ** x11 ** (privateInputIs ** memBufferIs))
    -- then use comm on the pair: (x5 ** x10 ** x11 ** (memBufferIs ** privateInputIs))
    -- then reassociate the whole thing into (memBufferIs ** frame) ** R' for appropriate frame/R'.

    -- Alternatively: use holdsFor_pullFourth to get
    -- ((memBufferIs ** x5 ** ...) ** R) — but memBufferIs is at position 5 of a 5-element chain.
    -- We need a pull5-from-5 which is just pulling the last element, i.e., comm on the inner's tail's tail's tail.

    -- Let me use a cleaner approach: factor through the inner assertion's last pair.
    -- ((A ** B ** C ** (D ** E)) ** R) using assoc
    -- Then comm inside: ((A ** B ** C ** (E ** D)) ** R)
    -- Then assoc back: ((A ** B ** C ** E ** D) ** R)
    -- Then pullFourth: ((E ** A ** B ** C ** D) ** R)
    -- Then assoc: (E ** ((A ** B ** C ** D) ** R))
    -- Apply writeBytesAsWords
    -- Then reverse

    -- Associating the last pair: from h3, inner is x5 ** x10 ** x11 ** privateInputIs ** memBufferIs
    -- = x5 ** (x10 ** (x11 ** (privateInputIs ** memBufferIs)))
    -- Wrap with R: ((x5 ** x10 ** x11 ** privateInputIs ** memBufferIs) ** R)

    -- Let me just directly manipulate the PartialState witness. Instead of complex rearrangement,
    -- use the fact that the IH of holdsFor_sepConj_memBufferIs_writeBytesAsWords quantifies over R.
    -- So I need to decompose h3 as (memBufferIs ** frame) ** R for some frame.

    -- Actually, let's just use a sequence of pull_second operations:
    -- From h3: ((A ** B ** C ** D ** E) ** R)
    -- pull_second: (B ** C ** D ** E ** (A ** R))... no, pull_second works at holdsFor level
    -- It goes from ((A ** B) ** C) to (B ** (A ** C))

    -- Let me just use four pull_second calls to move memBufferIs to front:
    -- Start: ((x5 ** x10 ** x11 ** pi ** mb) ** R)
    -- = assoc.mp → (x5 ** (x10 ** x11 ** pi ** mb) ** R)... no that's wrong

    -- pull_second.mp: ((A ** B) ** C) → (B ** (A ** C))
    -- On h3: ((x5 ** x10 ** x11 ** pi ** mb) ** R) with A=x5, B=(x10 ** x11 ** pi ** mb), C=R:
    --   → ((x10 ** x11 ** pi ** mb) ** (x5 ** R))
    -- Again with A=x10, B=(x11 ** pi ** mb), C=(x5 ** R):
    --   → ((x11 ** pi ** mb) ** (x10 ** x5 ** R))
    -- Again with A=x11, B=(pi ** mb), C=(x10 ** x5 ** R):
    --   → ((pi ** mb) ** (x11 ** x10 ** x5 ** R))
    -- Again with A=pi, B=mb, C=(x11 ** x10 ** x5 ** R):
    --   → (mb ** (pi ** x11 ** x10 ** x5 ** R))
    -- Now apply writeBytesAsWords on (mb ** frame)
    -- Then reverse: push mb back to end

    have h4 := holdsFor_sepConj_pull_second.mp h3
    have h5 := holdsFor_sepConj_pull_second.mp h4
    have h6 := holdsFor_sepConj_pull_second.mp h5
    have h7 := holdsFor_sepConj_pull_second.mp h6
    -- h7 : (memBufferIs bufAddr oldWords ** (privateInputIs ... ** x11 ** x10 ** x5 ** R))
    --   .holdsFor { st with privateInput := ... }

    -- Apply writeBytesAsWords
    have hblen : (inputBytes.take nbytes.toNat).length = 4 * oldWords.length := by
      rw [List.length_take]; omega
    have h8 := holdsFor_sepConj_memBufferIs_writeBytesAsWords hblen h7

    -- Push memBufferIs back to position 5 (reverse the 4 pull_seconds)
    have h9 := holdsFor_sepConj_pull_second.mpr h8
    have h10 := holdsFor_sepConj_pull_second.mpr h9
    have h11 := holdsFor_sepConj_pull_second.mpr h10
    have h12 := holdsFor_sepConj_pull_second.mpr h11
    -- h12 has the regs/pi/mb in REVERSED order: x5 ** x10 ** x11 ** pi ** mb'
    -- Wait, pull_second.mpr goes from (B ** (A ** C)) to ((A ** B) ** C)
    -- Let's trace: h8 = (mb' ** (pi ** x11 ** x10 ** x5 ** R))
    -- mpr: ((pi ** mb') ** (x11 ** x10 ** x5 ** R))
    -- mpr: ((x11 ** pi ** mb') ** (x10 ** x5 ** R))
    -- mpr: ((x10 ** x11 ** pi ** mb') ** (x5 ** R))
    -- mpr: ((x5 ** x10 ** x11 ** pi ** mb') ** R)
    -- So h12 = ((x5 ** x10 ** x11 ** privateInputIs(drop) ** memBufferIs(bytesToWords)) ** R)

    -- Step 3: setPC
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj
        (pcFree_sepConj (pcFree_regIs .x5 _)
          (pcFree_sepConj (pcFree_regIs .x10 _)
            (pcFree_sepConj (pcFree_regIs .x11 _)
              (pcFree_sepConj (pcFree_privateInputIs _) (pcFree_memBufferIs _ _)))))
        hR) _ _ h12

-- ============================================================================
-- Section 6: ECALL WRITE (public values) specification
-- ============================================================================

/-- Single ECALL step for WRITE to public values (fd = 13).
    Precondition: x5 = 0x02, x10 = 13, x11 = bufPtr, x12 = nbytes,
                  publicValues = oldPV, memory buffer at bufPtr = words.
    Postcondition: same registers, publicValues = oldPV ++ bytes, memory preserved.

    The WRITE syscall reads individual bytes from memory (matching SP1).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem ecall_write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (addr : Addr)
    (hfetch : code addr = some .ECALL)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32) :
    cpsTriple code addr (addr + 4)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  intro R hR st hPR hpc
  -- Extract register values from the 6-part conjunction ** R
  have hP := holdsFor_sepConj_elim_left hPR
  have hx5 : st.getReg .x5 = BitVec.ofNat 32 0x02 :=
    (holdsFor_regIs .x5 _ st).mp (holdsFor_sepConj_elim_left hP)
  have hx10 : st.getReg .x10 = (13 : Word) :=
    (holdsFor_regIs .x10 _ st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hP))
  have hx11 : st.getReg .x11 = bufPtr :=
    (holdsFor_regIs .x11 _ st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hP)))
  have hx12 : st.getReg .x12 = nbytes :=
    (holdsFor_regIs .x12 _ st).mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hP))))
  -- Extract memBufferIs and get getMem facts
  have hMemBuf := holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_right hP)))
  have hMemBuf' := holdsFor_sepConj_elim_right hMemBuf
  have hGetMem : ∀ (k : Nat) (hk : k < words.length),
      st.getMem (bufPtr + BitVec.ofNat 32 (4 * k)) = words[k]'hk :=
    fun k hk => getMem_of_holdsFor_memBufferIs hMemBuf' k hk
  -- Step computation
  have hfetch' : code st.pc = some .ECALL := by rw [hpc]; exact hfetch
  have hstep := step_ecall_write_public code st hfetch' hx5 hx10
  rw [hx11, hx12] at hstep
  -- Compute readBytes = (flatMap extractByte words).take nbytes.toNat
  have hReadFull := readBytes_of_words hGetMem hAligned
  have hReadTake := readBytes_take st bufPtr nbytes.toNat (4 * words.length) hLen
  have hRead : st.readBytes bufPtr nbytes.toNat =
      (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat := by
    rw [← hReadTake, hReadFull]
  -- Build the witness
  let newBytes := (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat
  have hNewState : step code st = some ((st.appendPublicValues newBytes).setPC (st.pc + 4)) := by
    rw [hstep, hRead]
  refine ⟨1, (st.appendPublicValues newBytes).setPC (addr + 4), ?_, ?_, ?_⟩
  · simp [stepN, hNewState, Option.bind, hpc]
  · simp [MachineState.setPC]
  · -- Reconstruct postcondition via pullFifth/appendPublicValues/pushFifth/setPC
    have h1 := holdsFor_pullFifth hPR
    have h2 := holdsFor_sepConj_assoc.mp h1
    have h3 := holdsFor_sepConj_publicValuesIs_appendPublicValues (bytes := newBytes) h2
    have h4 := holdsFor_sepConj_assoc.mpr h3
    have h5 := holdsFor_pushFifth h4
    exact holdsFor_pcFree_setPC
      (pcFree_sepConj
        (pcFree_sepConj (pcFree_regIs .x5 _)
          (pcFree_sepConj (pcFree_regIs .x10 _)
            (pcFree_sepConj (pcFree_regIs .x11 _)
              (pcFree_sepConj (pcFree_regIs .x12 _)
                (pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _))))))
        hR) _ _ h5

-- ============================================================================
-- Section 7: Generalized WRITE spec (for arbitrary CodeMem)
-- ============================================================================

/-- WRITE 13 bufPtr nbytes on arbitrary CodeMem, given fetch proofs for all 5 instructions.
    Uses regOwn (no old register values needed).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem write_public_spec_gen (code : CodeMem) (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32)
    (hf0 : code base = some (Instr.LI .x5 (BitVec.ofNat 32 0x02)))
    (hf1 : code (base + 4) = some (Instr.LI .x10 13))
    (hf2 : code (base + 8) = some (Instr.LI .x11 bufPtr))
    (hf3 : code (base + 12) = some (Instr.LI .x12 nbytes))
    (hf4 : code (base + 16) = some Instr.ECALL) :
    cpsTriple code base (base + 20)
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  -- Address arithmetic
  have h48 : base + 4 + 4 = base + 8 := by grind
  have h812 : base + 8 + 4 = base + 12 := by grind
  have h1216 : base + 12 + 4 = base + 16 := by grind
  have h1620 : base + 16 + 4 = base + 20 := by grind
  -- pcFree helpers
  let pvMB := publicValuesIs oldPV ** memBufferIs bufPtr words
  have hpvMB : pvMB.pcFree := pcFree_sepConj (pcFree_publicValuesIs _) (pcFree_memBufferIs _ _)
  -- Step 1: LI x5 (base → base+4), frame = regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB
  have s1 : cpsTriple code base (base + 4) (regOwn .x5) (.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) :=
    li_spec_gen_own code .x5 _ base (by decide) hf0
  have s1f : cpsTriple code base (base + 4)
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_left code base (base + 4) _ _ _
      (pcFree_sepConj (pcFree_regOwn .x10) (pcFree_sepConj (pcFree_regOwn .x11) (pcFree_sepConj (pcFree_regOwn .x12) hpvMB))) s1
  -- Step 2: LI x10 (base+4 → base+8), frame = .x5 ↦ᵣ 0x02 ** regOwn .x11 ** regOwn .x12 ** pvMB
  have s2core : cpsTriple code (base + 4) (base + 8) (regOwn .x10) (.x10 ↦ᵣ (13 : Word)) := by
    have := li_spec_gen_own code .x10 13 (base + 4) (by decide) hf1
    simp only [h48] at this; exact this
  have s2f : cpsTriple code (base + 4) (base + 8)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** regOwn .x11 ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_right code (base + 4) (base + 8) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_left code (base + 4) (base + 8) _ _ _
        (pcFree_sepConj (pcFree_regOwn .x11) (pcFree_sepConj (pcFree_regOwn .x12) hpvMB)) s2core)
  -- Step 3: LI x11 (base+8 → base+12), frame = .x5 ↦ᵣ 0x02 ** .x10 ↦ᵣ 13 ** regOwn .x12 ** pvMB
  have s3core : cpsTriple code (base + 8) (base + 12) (regOwn .x11) (.x11 ↦ᵣ bufPtr) := by
    have := li_spec_gen_own code .x11 bufPtr (base + 8) (by decide) hf2
    simp only [h812] at this; exact this
  have s3f : cpsTriple code (base + 8) (base + 12)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** regOwn .x11 ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** regOwn .x12 ** pvMB) :=
    cpsTriple_frame_right code (base + 8) (base + 12) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code (base + 8) (base + 12) _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_left code (base + 8) (base + 12) _ _ _
          (pcFree_sepConj (pcFree_regOwn .x12) hpvMB) s3core))
  -- Step 4: LI x12 (base+12 → base+16), frame = .x5 ↦ᵣ 0x02 ** .x10 ↦ᵣ 13 ** .x11 ↦ᵣ bufPtr ** pvMB
  have s4core : cpsTriple code (base + 12) (base + 16) (regOwn .x12) (.x12 ↦ᵣ nbytes) := by
    have := li_spec_gen_own code .x12 nbytes (base + 12) (by decide) hf3
    simp only [h1216] at this; exact this
  have s4f : cpsTriple code (base + 12) (base + 16)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** regOwn .x12 ** pvMB)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) ** pvMB) :=
    cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x5 ↦ᵣ _) (pcFree_regIs .x5 _)
      (cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x10 ↦ᵣ _) (pcFree_regIs .x10 _)
        (cpsTriple_frame_right code (base + 12) (base + 16) _ _ (.x11 ↦ᵣ _) (pcFree_regIs .x11 _)
          (cpsTriple_frame_left code (base + 12) (base + 16) _ _ _ hpvMB s4core)))
  -- Step 5: ECALL (base+16 → base+20)
  have s5 : cpsTriple code (base + 16) (base + 20)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) ** publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) ** (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
    have := ecall_write_public_spec_gen code bufPtr nbytes oldPV words (base + 16) hf4 hLen hAligned
    simp only [h1620] at this; exact this
  -- Compose all steps
  exact cpsTriple_seq code base (base + 16) (base + 20) _ _ _
    (cpsTriple_seq code base (base + 12) (base + 16) _ _ _
      (cpsTriple_seq code base (base + 8) (base + 12) _ _ _
        (cpsTriple_seq code base (base + 4) (base + 8) _ _ _ s1f s2f) s3f) s4f) s5

end RiscVMacroAsm
