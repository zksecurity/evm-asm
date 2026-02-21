/-
  EvmAsm.SyscallSpecs

  CPS specifications for the HALT and WRITE macro instructions,
  proved by composing generalized per-instruction specs via structural rules
  (cpsTriple_seq, cpsTriple_seq_halt, frame embedding).
-/

import EvmAsm.Basic
import EvmAsm.Instructions
import EvmAsm.SepLogic
import EvmAsm.Execution
import EvmAsm.CPSSpec
import EvmAsm.ControlFlow
import Std.Tactic.BVDecide

namespace EvmAsm

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
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => by rw [MachineState.getReg_appendPublicValues]; exact hr r v hv,
         fun a v hv => by rw [MachineState.getMem_appendPublicValues]; exact hm a v hv,
         fun a i hv => by rw [MachineState.code_appendPublicValues]; exact hc a i hv,
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
    rcases hdisj.2.2.2.2.1 with h | h
    · simp [PartialState.singletonPublicValues] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPublicValues (oldPV ++ bytes)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, Or.inr hpv2, hdisj.2.2.2.2.2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPublicValues (oldPV ++ bytes) compatible with s.appendPublicValues bytes
  have hc1' : (PartialState.singletonPublicValues (oldPV ++ bytes)).CompatibleWith
      (s.appendPublicValues bytes) := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPublicValues] at hr,
            fun a w ha => by simp [PartialState.singletonPublicValues] at ha,
            fun a i hi => by simp [PartialState.singletonPublicValues] at hi,
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
  obtain ⟨hr, hm, hc, hpc, hpv, hpi⟩ := hcompat
  exact ⟨fun r v hv => hr r v hv,
         fun a v hv => hm a v hv,
         fun a i hv => hc a i hv,
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
    rcases hdisj.2.2.2.2.2 with h | h
    · simp [PartialState.singletonPrivateInput] at h
    · exact h
  -- Disjointness preserved
  have hdisj' : (PartialState.singletonPrivateInput (allBytes.drop n)).Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2.1, Or.inr hpi2⟩
  -- Split old compatibility
  have ⟨hc1, hc2⟩ := (PartialState.CompatibleWith_union hdisj).mp hcompat
  -- singletonPrivateInput (allBytes.drop n) compatible with modified state
  have hc1' : (PartialState.singletonPrivateInput (allBytes.drop n)).CompatibleWith
      { s with privateInput := s.privateInput.drop n } := by
    refine ⟨fun r w hr => by simp [PartialState.singletonPrivateInput] at hr,
            fun a w ha => by simp [PartialState.singletonPrivateInput] at ha,
            fun a i hi => by simp [PartialState.singletonPrivateInput] at hi,
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
theorem lw_spec_gen (rd rs1 : Reg) (v_addr v_old mem_val : Word)
    (offset : BitVec 12) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ v_old) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ mem_val) ** ((v_addr + signExtend12 offset) ↦ₘ mem_val)) := by
  sorry

/-- SLTIU spec for any code memory (rd == rs1 case):
    rd := (v <u sext(imm)) ? 1 : 0 -/
theorem sltiu_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (rd ↦ᵣ v)
      (rd ↦ᵣ (if BitVec.ult v (signExtend12 imm) then (1 : Word) else (0 : Word))) := by
  sorry

/-- XORI spec for any code memory (rd == rs1 case):
    rd := v ^^^ sext(imm) -/
theorem xori_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (rd ↦ᵣ v)
      (rd ↦ᵣ (v ^^^ signExtend12 imm)) := by
  sorry

/-- SRL spec for any code memory (rd = rs1 case):
    rd := rd >>> (rs2.toNat % 32) -/
theorem srl_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 >>> (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- SLL spec for any code memory (rd = rs1 case):
    rd := rd <<< (rs2.toNat % 32) -/
theorem sll_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 <<< (v2.toNat % 32))) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- ADD spec for any code memory (rd = rs1 case):
    rd := rd + rs2 -/
theorem add_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 + v2)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- SUB spec for any code memory (rd = rs1 case):
    rd := rd - rs2 -/
theorem sub_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 - v2)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- AND spec for any code memory (rd = rs1 case):
    rd := rd &&& rs2 -/
theorem and_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 &&& v2)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- OR spec for any code memory (rd = rs1 case):
    rd := rd ||| rs2 -/
theorem or_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ||| v2)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- XOR spec for any code memory (rd = rs1 case):
    rd := rd ^^^ rs2 -/
theorem xor_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (v1 ^^^ v2)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- SLTU spec for any code memory (rd = rs1 case):
    rd := if rd <u rs2 then 1 else 0 -/
theorem sltu_spec_gen_rd_eq_rs1 (rd rs2 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs2) :
    cpsTriple addr (addr + 4)
      ((rd ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      ((rd ↦ᵣ (if BitVec.ult v1 v2 then (1 : Word) else 0)) ** (rs2 ↦ᵣ v2)) := by
  sorry

/-- ADDI spec for any code memory (rd = rs1 case):
    rd := rd + signExtend12(imm) -/
theorem addi_spec_gen_same (rd : Reg) (v : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (rd ↦ᵣ v) (rd ↦ᵣ (v + signExtend12 imm)) := by
  sorry

/-- LI spec for any code memory (not just a single-instruction loadProgram). -/
theorem li_spec_gen (rd : Reg) (v_old imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (rd ↦ᵣ v_old) (rd ↦ᵣ imm) := by
  sorry

/-- LI spec for any code memory with regOwn (no v_old needed). -/
theorem li_spec_gen_own (rd : Reg) (imm : Word) (addr : Addr)
    (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (regOwn rd) (rd ↦ᵣ imm) := by
  sorry

/-- ECALL halt spec: when x5 = 0, ECALL halts. -/
theorem ecall_halt_spec_gen (exitCode : Word) (addr : Addr) :
    cpsHaltTriple addr
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  sorry

/-- SW rs1 rs2 offset: mem[rs1 + sext(offset)] := rs2 (generalized for any CodeMem) -/
theorem sw_spec_gen (rs1 rs2 : Reg) (v_addr v_data mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  sorry

/-- SW spec with memOwn (no mem_old needed). -/
theorem sw_spec_gen_own (rs1 rs2 : Reg) (v_addr v_data : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memOwn (v_addr + signExtend12 offset))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 offset) ↦ₘ v_data)) := by
  sorry

/-- SW rs1 x0 offset: mem[rs1 + sext(offset)] := 0.
    Specialized version of sw_spec_gen for x0 (always reads as 0).
    Does not require (x0 ↦ᵣ 0) in pre/post. -/
theorem sw_x0_spec_gen (rs1 : Reg) (v_addr mem_old : Word)
    (offset : BitVec 12) (addr : Addr)
    (hvalid : isValidMemAccess (v_addr + signExtend12 offset) = true) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ mem_old))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 offset) ↦ₘ (0 : Word))) := by
  sorry

-- ============================================================================
-- Section 4: Frame Embedding for cpsTriple
-- ============================================================================

/-- Frame on the right: if cpsTriple P → Q, then cpsTriple (P ** F) → (Q ** F). -/
theorem cpsTriple_frame_left (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (P ** F) (Q ** F) := by
  sorry

/-- Frame for cpsBranch: if cpsBranch P → Q_t | Q_f, then cpsBranch (P ** F) → (Q_t ** F) | (Q_f ** F). -/
theorem cpsBranch_frame_left (entry : Addr)
    (P : Assertion) (exit_t : Addr) (Q_t : Assertion)
    (exit_f : Addr) (Q_f : Assertion)
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch entry P exit_t Q_t exit_f Q_f) :
    cpsBranch entry (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  sorry

/-- Frame for cpsNBranch: if cpsNBranch P → exits, then cpsNBranch (P ** F) → exits with F. -/
theorem cpsNBranch_frame_left (entry : Addr)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry P exits) :
    cpsNBranch entry (P ** F) (exits.map fun (a, Q) => (a, Q ** F)) := by
  sorry

/-- Frame for cpsNBranch on the right: if cpsNBranch P → exits, then cpsNBranch (F ** P) → exits with F. -/
theorem cpsNBranch_frame_right (entry : Addr)
    (P : Assertion) (exits : List (Addr × Assertion))
    (F : Assertion) (hF : F.pcFree)
    (h : cpsNBranch entry P exits) :
    cpsNBranch entry (F ** P) (exits.map fun (a, Q) => (a, F ** Q)) := by
  sorry

/-- Frame on the left: if cpsTriple P → Q, then cpsTriple (F ** P) → (F ** Q). -/
theorem cpsTriple_frame_right (entry exit_ : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsTriple entry exit_ P Q) :
    cpsTriple entry exit_ (F ** P) (F ** Q) := by
  sorry

/-- Frame on the right for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_left (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry (P ** F) (Q ** F) := by
  sorry

/-- Frame on the left for cpsHaltTriple. -/
theorem cpsHaltTriple_frame_right (entry : Addr)
    (P Q F : Assertion) (hF : F.pcFree)
    (h : cpsHaltTriple entry P Q) :
    cpsHaltTriple entry (F ** P) (F ** Q) := by
  sorry

-- ============================================================================
-- Section 5: Generalized HALT spec (for arbitrary CodeMem)
-- ============================================================================

/-- HALT exitCode on arbitrary CodeMem, given fetch proofs for the 3 instructions.
    Uses regOwn (no old values needed). -/
theorem halt_spec_gen (exitCode : Word) (base : Addr) :
    cpsHaltTriple base
      (regOwn .x5 ** regOwn .x10)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  sorry

-- ============================================================================
-- Section 5a: Combined store word spec (LI x6 val ;; SW x7 x6 offset)
-- ============================================================================

/-- Combined spec for "LI x6, val ;; SW x7, x6, offset":
    Stores val at mem[x7_val + sext(offset)], updates x6 to val.
    Proved directly as a 2-step execution. -/
theorem storeWord_spec_gen (val : Word) (offset : BitVec 12)
    (x6_old x7_val mem_old : Word) (addr : Addr)
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple addr (addr + 8)
      ((.x6 ↦ᵣ x6_old) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ mem_old))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  sorry

/-- Combined LI+SW spec with regOwn and memOwn (no x6_old or mem_old needed). -/
theorem storeWord_spec_gen_own (val : Word) (offset : BitVec 12)
    (x7_val : Word) (addr : Addr)
    (hvalid : isValidMemAccess (x7_val + signExtend12 offset) = true) :
    cpsTriple addr (addr + 8)
      (regOwn .x6 ** (.x7 ↦ᵣ x7_val) ** memOwn (x7_val + signExtend12 offset))
      ((.x6 ↦ᵣ val) ** (.x7 ↦ᵣ x7_val) ** ((x7_val + signExtend12 offset) ↦ₘ val)) := by
  sorry

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
theorem ecall_hint_read_spec_gen (bufAddr nbytes : Word)
    (inputBytes : List (BitVec 8)) (oldWords : List Word) (addr : Addr)
    (hLen : nbytes.toNat ≤ inputBytes.length)
    (hNbytes : nbytes.toNat = 4 * oldWords.length) :
    cpsTriple addr (addr + 4)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs inputBytes ** memBufferIs bufAddr oldWords)
      ((.x5 ↦ᵣ 0xF1#32) ** (.x10 ↦ᵣ bufAddr) ** (.x11 ↦ᵣ nbytes) **
       privateInputIs (inputBytes.drop nbytes.toNat) **
       memBufferIs bufAddr (bytesToWords (inputBytes.take nbytes.toNat))) := by
  sorry

-- ============================================================================
-- Section 6: ECALL WRITE (public values) specification
-- ============================================================================

/-- Single ECALL step for WRITE to public values (fd = 13).
    Precondition: x5 = 0x02, x10 = 13, x11 = bufPtr, x12 = nbytes,
                  publicValues = oldPV, memory buffer at bufPtr = words.
    Postcondition: same registers, publicValues = oldPV ++ bytes, memory preserved.

    The WRITE syscall reads individual bytes from memory (matching SP1).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem ecall_write_public_spec_gen (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (addr : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32) :
    cpsTriple addr (addr + 4)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  sorry

-- ============================================================================
-- Section 7: Generalized WRITE spec (for arbitrary CodeMem)
-- ============================================================================

/-- WRITE 13 bufPtr nbytes on arbitrary CodeMem, given fetch proofs for all 5 instructions.
    Uses regOwn (no old register values needed).
    The postcondition takes nbytes.toNat bytes from the word buffer's byte representation. -/
theorem write_public_spec_gen (bufPtr nbytes : Word)
    (oldPV : List (BitVec 8)) (words : List Word) (base : Addr)
    (hLen : nbytes.toNat ≤ 4 * words.length)
    (hAligned : bufPtr &&& 3#32 = 0#32) :
    cpsTriple base (base + 20)
      (regOwn .x5 ** regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
       publicValuesIs oldPV ** memBufferIs bufPtr words)
      ((.x5 ↦ᵣ (BitVec.ofNat 32 0x02)) ** (.x10 ↦ᵣ (13 : Word)) **
       (.x11 ↦ᵣ bufPtr) ** (.x12 ↦ᵣ nbytes) **
       publicValuesIs (oldPV ++ (words.flatMap (fun w => [extractByte w 0, extractByte w 1, extractByte w 2, extractByte w 3])).take nbytes.toNat) ** memBufferIs bufPtr words) := by
  sorry

/-- SLTU spec for 3 distinct registers:
    rd := (rs1 < rs2) ? 1 : 0, preserving rs1 and rs2 -/
theorem sltu_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (if BitVec.ult v1 v2 then 1 else 0))) := by
  sorry

/-- OR spec for 3 distinct registers:
    rd := rs1 ||| rs2, preserving rs1 and rs2 -/
theorem or_spec_gen (rd rs1 rs2 : Reg) (v_old v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** (rd ↦ᵣ (v1 ||| v2))) := by
  sorry

-- ============================================================================
-- Section 10: Additional instruction specs for SHR proofs
-- ============================================================================

/-- ANDI spec for any code memory (rd ≠ rs1 case):
    rd := rs1 &&& sext(imm), preserving rs1 -/
theorem andi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 &&& signExtend12 imm))) := by
  sorry

/-- SRLI spec for any code memory (rd == rs1 case):
    rd := rd >>> shamt -/
theorem srli_spec_gen_same (rd : Reg) (v : Word) (shamt : BitVec 5)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) :
    cpsTriple addr (addr + 4) (rd ↦ᵣ v) (rd ↦ᵣ (v >>> shamt.toNat)) := by
  sorry

/-- SLTIU spec for any code memory (rd ≠ rs1 case):
    rd := (rs1 <u sext(imm)) ? 1 : 0, preserving rs1 -/
theorem sltiu_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (if BitVec.ult v1 (signExtend12 imm) then (1 : Word) else (0 : Word)))) := by
  sorry

/-- ADDI spec for any code memory (rd ≠ rs1 case):
    rd := rs1 + sext(imm), preserving rs1 -/
theorem addi_spec_gen (rd rs1 : Reg) (v_old v1 : Word) (imm : BitVec 12)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v_old))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 + signExtend12 imm))) := by
  sorry

/-- SUB spec for any code memory (rd = rs2 case):
    rd := rs1 - rd, preserving rs1 -/
theorem sub_spec_gen_rd_eq_rs2 (rd rs1 : Reg) (v1 v2 : Word)
    (addr : Addr) (hrd_ne_x0 : rd ≠ .x0) (hne : rd ≠ rs1) :
    cpsTriple addr (addr + 4)
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ v2))
      ((rs1 ↦ᵣ v1) ** (rd ↦ᵣ (v1 - v2))) := by
  sorry

/-- BNE spec for any code memory:
    Branch taken (v1 ≠ v2) → PC = addr + sext(offset)
    Branch not taken (v1 = v2) → PC = addr + 4 -/
theorem bne_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝)
      (addr + 4)                   ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝) := by
  sorry

/-- BEQ spec for any code memory:
    Branch taken (v1 = v2) → PC = addr + sext(offset)
    Branch not taken (v1 ≠ v2) → PC = addr + 4 -/
theorem beq_spec_gen (rs1 rs2 : Reg) (offset : BitVec 13) (v1 v2 : Word)
    (addr : Addr) :
    cpsBranch addr
      ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2))
      (addr + signExtend13 offset) ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝)
      (addr + 4)                   ((rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 ≠ v2⌝) := by
  sorry

/-- JAL x0 spec for any code memory: pure PC jump, no register/memory changes.
    Since x0 writes are dropped, JAL x0 just updates PC. -/
theorem jal_x0_spec_gen (offset : BitVec 21) (addr : Addr)
    (P : Assertion) (hP : P.pcFree) :
    cpsTriple addr (addr + signExtend21 offset) P P := by
  sorry

end EvmAsm
