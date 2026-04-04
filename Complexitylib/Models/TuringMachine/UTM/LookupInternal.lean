import Complexitylib.Models.TuringMachine.UTM.Lookup
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# Lookup proof internals

Step-by-step simulation lemmas for `lookupTM`.
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem lu_readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem lu_tape_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start) (hh : t.head ≥ 1) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hns ⊢
    rw [lu_readBackWrite_toΓ_eq hns, Function.update_eq_self]

private theorem lu_tape_read_ne_start_of_wf (t : Tape) (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hns _ hh

-- ════════════════════════════════════════════════════════════════════════
-- Encoding lemmas
-- ════════════════════════════════════════════════════════════════════════

private lemma flatMap_encode_length {α : Type} (l : List α) (f : α → Γ) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Γ.encode_length, ih, List.length_cons]
    omega

private lemma flatMap_Γw_encode_length {α : Type} (l : List α) (f : α → Γw) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Γw.encode_length, ih, List.length_cons]
    omega

private lemma flatMap_Dir3_encode_length {α : Type} (l : List α) (f : α → Dir3) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Dir3.encode_length, ih, List.length_cons]
    omega

private lemma encodeInputPattern_length (k n : ℕ) (q : Fin k) (iH : Γ)
    (wH : Fin n → Γ) (oH : Γ) :
    (TMEncoding.encodeInputPattern k n q iH wH oH).length =
      TMEncoding.inputPatternWidth k n := by
  simp only [TMEncoding.encodeInputPattern, TMEncoding.inputPatternWidth,
    List.length_append, List.length_map, List.length_finRange,
    Γ.encode_length, flatMap_encode_length]

private lemma encodeTransOutput_length (k n : ℕ) (q' : Fin k)
    (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) :
    (TMEncoding.encodeTransOutput k n q' wW oW iD wD oD).length =
      TMEncoding.outputWidth k n := by
  simp only [TMEncoding.encodeTransOutput, TMEncoding.outputWidth,
    List.length_append, List.length_map, List.length_finRange,
    Γw.encode_length, Dir3.encode_length,
    flatMap_Γw_encode_length, flatMap_Dir3_encode_length]

private lemma encodeEntry_eq (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ)
    (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) :
    TMEncoding.encodeEntry k n q iH wH oH q' wW oW iD wD oD =
    TMEncoding.encodeInputPattern k n q iH wH oH ++
    [false] ++
    TMEncoding.encodeTransOutput k n q' wW oW iD wD oD := by
  simp only [TMEncoding.encodeEntry, TMEncoding.encodeInputPattern,
    TMEncoding.encodeTransOutput, List.append_assoc]

private lemma encodeEntry_length (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ)
    (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) :
    (TMEncoding.encodeEntry k n q iH wH oH q' wW oW iD wD oD).length =
      TMEncoding.entryWidth k n := by
  rw [encodeEntry_eq, TMEncoding.entryWidth]
  simp only [List.length_append, List.length_cons, List.length_nil,
    encodeInputPattern_length, encodeTransOutput_length]

-- ════════════════════════════════════════════════════════════════════════
-- Encoding connection helpers
-- ════════════════════════════════════════════════════════════════════════

/-- The header portion of `encodeTM` (everything before the transition table). -/
private noncomputable def encodeTM_header (tm : TM n) : List Bool :=
  let k := @Fintype.card tm.Q tm.finQ
  let e := tm.stateEquiv
  List.replicate k true ++ [false] ++
  List.replicate n true ++ [false] ++
  TMEncoding.encodeStateOneHot tm e tm.qhalt ++ [false] ++
  TMEncoding.encodeStateOneHot tm e tm.qstart ++ [false]

/-- `encodeTM` splits as header ++ transTable. -/
private theorem encodeTM_eq_header_append_table (tm : TM n) :
    TMEncoding.encodeTM tm = encodeTM_header tm ++ TMEncoding.encodeTransTable tm tm.stateEquiv := by
  simp only [TMEncoding.encodeTM, encodeTM_header, List.append_assoc]

/-- The header has length `tableOffset k n`. -/
private theorem encodeTM_header_length (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    (encodeTM_header tm).length = TMEncoding.tableOffset k n := by
  subst hk
  simp only [encodeTM_header, TMEncoding.encodeStateOneHot, TMEncoding.tableOffset,
    TMEncoding.qstartOffset, TMEncoding.qhaltOffset,
    List.length_append, List.length_replicate, List.length_singleton,
    List.length_map, List.length_finRange]

/-- Length of a constant-width flatMap. -/
private theorem flatMap_const_width_length {α : Type} {β : Type}
    (l : List α) (f : α → List β) (w : ℕ)
    (hfw : ∀ a, a ∈ l → (f a).length = w) :
    (l.flatMap f).length = l.length * w := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hfw _ List.mem_cons_self,
        ih (fun a' ha' => hfw a' (List.mem_cons_of_mem _ ha')),
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Bound: idx * w + j < llen * w when idx < llen and j < w. -/
private theorem mul_add_lt_mul_of_lt (idx j llen w : ℕ)
    (hidx : idx < llen) (hj : j < w) :
    idx * w + j < llen * w := by
  have h1 : idx * w + j < idx * w + w := Nat.add_lt_add_left hj _
  have h2 : idx * w + w ≤ llen * w := by
    have : idx + 1 ≤ llen := hidx
    calc idx * w + w = (idx + 1) * w := by simp [Nat.add_mul, Nat.one_mul]
      _ ≤ llen * w := Nat.mul_le_mul_right w this
  omega

/-- Indexing into a constant-width flatMap: if every `f a` has length `w`,
    then `(l.flatMap f)[idx * w + j] = (f l[idx])[j]`. -/
private theorem flatMap_const_width_getElem {α : Type} {β : Type}
    (l : List α) (f : α → List β) (w : ℕ)
    (hfw : ∀ a, a ∈ l → (f a).length = w)
    (idx j : ℕ) (hidx : idx < l.length) (hj : j < w) :
    (l.flatMap f)[idx * w + j]'(by
      rw [flatMap_const_width_length l f w hfw]
      exact mul_add_lt_mul_of_lt idx j l.length w hidx hj) =
    (f l[idx])[j]'(by rw [hfw _ (List.getElem_mem hidx)]; exact hj) := by
  induction l generalizing idx with
  | nil => simp at hidx
  | cons a as ih =>
    match idx with
    | 0 =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem_append_left _
    | idx' + 1 =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hlen_a : (f a).length = w := hfw _ List.mem_cons_self
      have hle : (f a).length ≤ (idx' + 1) * w + j := by
        calc (f a).length = w := hlen_a
          _ ≤ (idx' + 1) * w := Nat.le_mul_of_pos_left w (by omega)
          _ ≤ (idx' + 1) * w + j := Nat.le_add_right _ _
      rw [List.getElem_append_right hle]
      have hfw' := fun a' (ha' : a' ∈ as) => hfw a' (List.mem_cons_of_mem _ ha')
      have hidx' : idx' < as.length := by simp at hidx; omega
      convert ih hfw' idx' hidx' using 1
      congr 1
      show (idx' + 1) * w + j - (f a).length = idx' * w + j
      rw [hlen_a, Nat.add_mul, Nat.one_mul]
      omega

private theorem allΓ_complete (g : Γ) : g ∈ allΓ := by cases g <;> simp [allΓ]

private theorem allΓ_length : allΓ.length = 4 := rfl

private theorem allΓFuncs_complete : ∀ (f : Fin n → Γ), f ∈ allΓFuncs n := by
  induction n with
  | zero => intro f; simp [allΓFuncs]; ext i; exact i.elim0
  | succ n ih =>
    intro f
    simp only [allΓFuncs, List.mem_flatMap, List.mem_map]
    refine ⟨fun i => f ⟨i.val, by omega⟩, ih _, f ⟨n, by omega⟩, allΓ_complete _, ?_⟩
    ext i
    simp only
    split
    · rfl
    · next h =>
        have hiv : i.val = n := Nat.le_antisymm (by omega) (by omega)
        exact congrArg f (Fin.ext hiv.symm)

private theorem Γ_ofBool_injective : Function.Injective Γ.ofBool := by
  intro a b h; cases a <;> cases b <;> simp_all [Γ.ofBool]

private theorem Γ_ofBool_ne_of_ne {a b : Bool} (h : a ≠ b) : Γ.ofBool a ≠ Γ.ofBool b :=
  fun heq => h (Γ_ofBool_injective heq)

private theorem allΓ_nodup : allΓ.Nodup := by decide

private theorem allΓFuncs_nodup (m : ℕ) : (allΓFuncs m).Nodup := by
  induction m with
  | zero => exact List.nodup_singleton _
  | succ m ih =>
    simp only [allΓFuncs]
    rw [List.nodup_flatMap]
    refine ⟨fun f _ => allΓ_nodup.map fun g₁ g₂ heq => ?_,
            ih.pairwise_of_forall_ne fun f₁ _ f₂ _ hne a h1 h2 => ?_⟩
    · have := congr_fun heq ⟨m, by omega⟩
      simp only [dif_neg (show ¬(m < m) from by omega)] at this
      exact this
    · simp only [List.mem_map] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, heq⟩ := h2
      exact hne (funext fun i => by
        have := congr_fun heq ⟨i.val, by omega⟩
        simp only [dif_pos i.isLt] at this
        exact this.symm)

-- ════════════════════════════════════════════════════════════════════════
-- Transition table structure
-- ════════════════════════════════════════════════════════════════════════

/-- The canonical enumeration of all 4-tuples (q, iH, wH, oH). -/
private noncomputable def allTuples (k n : ℕ) : List (Fin k × Γ × (Fin n → Γ) × Γ) :=
  (List.finRange k).flatMap fun q =>
    allΓ.flatMap fun iH =>
      (allΓFuncs n).flatMap fun wH =>
        allΓ.map fun oH =>
          (q, iH, wH, oH)

/-- Every 4-tuple is in the canonical enumeration. -/
private theorem allTuples_mem (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ) :
    (q, iH, wH, oH) ∈ allTuples k n := by
  simp only [allTuples, List.mem_flatMap, List.mem_map]
  exact ⟨q, List.mem_finRange q,
         iH, allΓ_complete iH,
         wH, allΓFuncs_complete wH,
         oH, allΓ_complete oH, rfl⟩

private theorem allTuples_nodup (k n : ℕ) : (allTuples k n).Nodup := by
  simp only [allTuples]
  -- Each level uses nodup_flatMap: inner lists are nodup + pairwise disjoint
  -- Disjointness follows from tuple components being fixed per inner list
  have fst_eq : ∀ (q : Fin k) a,
      a ∈ (allΓ.flatMap fun iH => (allΓFuncs n).flatMap fun wH =>
        allΓ.map fun oH => (q, iH, wH, oH)) → a.1 = q := by
    intro q a ha; simp only [List.mem_flatMap, List.mem_map] at ha
    obtain ⟨_, _, _, _, _, _, rfl⟩ := ha; rfl
  have snd_eq : ∀ (q : Fin k) (iH : Γ) a,
      a ∈ ((allΓFuncs n).flatMap fun wH => allΓ.map fun oH => (q, iH, wH, oH)) →
      a.2.1 = iH := by
    intro q iH a ha; simp only [List.mem_flatMap, List.mem_map] at ha
    obtain ⟨_, _, _, _, rfl⟩ := ha; rfl
  have thd_eq : ∀ (q : Fin k) (iH : Γ) (wH : Fin n → Γ) a,
      a ∈ (allΓ.map fun oH => (q, iH, wH, oH)) → a.2.2.1 = wH := by
    intro q iH wH a ha; simp only [List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; rfl
  -- Level 1 (q): different q → disjoint first components
  rw [List.nodup_flatMap]; refine ⟨fun q _ => ?_,
    (List.nodup_finRange k).pairwise_of_forall_ne fun q₁ _ q₂ _ hne a h1 h2 =>
      hne (by rw [← fst_eq _ a h1, fst_eq _ a h2])⟩
  -- Level 2 (iH): different iH → disjoint second components
  rw [List.nodup_flatMap]; refine ⟨fun iH _ => ?_,
    allΓ_nodup.pairwise_of_forall_ne fun iH₁ _ iH₂ _ hne a h1 h2 =>
      hne (by rw [← snd_eq q _ a h1, snd_eq q _ a h2])⟩
  -- Level 3 (wH): different wH → disjoint third components
  rw [List.nodup_flatMap]
  exact ⟨fun wH _ => allΓ_nodup.map (fun oH₁ oH₂ heq => by
      simp only [Prod.mk.injEq] at heq; exact heq.2.2.2),
    (allΓFuncs_nodup n).pairwise_of_forall_ne fun wH₁ _ wH₂ _ hne a h1 h2 =>
      hne (by rw [← thd_eq q iH _ a h1, thd_eq q iH _ a h2])⟩

/-- The input pattern of an encodeEntry starts with the given encodeInputPattern. -/
private theorem encodeEntry_input_prefix (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ)
    (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3)
    (j : ℕ) (hj : j < TMEncoding.inputPatternWidth k n) :
    (TMEncoding.encodeInputPattern k n q iH wH oH ++ [false] ++
     TMEncoding.encodeTransOutput k n q' wW oW iD wD oD)[j]'(by
      simp only [List.length_append, encodeInputPattern_length,
        List.length_cons, List.length_nil, encodeTransOutput_length,
        TMEncoding.entryWidth]; omega) =
    (TMEncoding.encodeInputPattern k n q iH wH oH)[j]'(by
      rw [encodeInputPattern_length]; exact hj) := by
  rw [List.getElem_append_left (by
    simp only [List.length_append, encodeInputPattern_length, List.length_cons,
      List.length_nil]; omega)]
  exact List.getElem_append_left (by rw [encodeInputPattern_length]; exact hj)

/-- The output bits of an encodeEntry are past the input pattern + separator. -/
private theorem encodeEntry_output_getElem (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ)
    (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3)
    (j : ℕ) (hj : j < (TMEncoding.encodeTransOutput k n q' wW oW iD wD oD).length) :
    (TMEncoding.encodeInputPattern k n q iH wH oH ++ [false] ++
     TMEncoding.encodeTransOutput k n q' wW oW iD wD oD)[TMEncoding.inputPatternWidth k n + 1 + j]'(by
      simp only [List.length_append, encodeInputPattern_length,
        List.length_cons, List.length_nil]; omega) =
    (TMEncoding.encodeTransOutput k n q' wW oW iD wD oD)[j] := by
  rw [List.getElem_append_right (by
    simp only [List.length_append, encodeInputPattern_length, List.length_cons,
      List.length_nil]; omega)]
  congr 1
  have := encodeInputPattern_length k n q iH wH oH
  simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
  omega

/-- `encodeInputPattern` is injective: equal patterns imply equal tuples.
    (All sub-lemmas are packaged inside for modularity.) -/
private theorem encodeInputPattern_injective {k n : ℕ}
    {q₁ q₂ : Fin k} {iH₁ iH₂ : Γ} {wH₁ wH₂ : Fin n → Γ} {oH₁ oH₂ : Γ}
    (heq : TMEncoding.encodeInputPattern k n q₁ iH₁ wH₁ oH₁ =
           TMEncoding.encodeInputPattern k n q₂ iH₂ wH₂ oH₂) :
    q₁ = q₂ ∧ iH₁ = iH₂ ∧ wH₁ = wH₂ ∧ oH₁ = oH₂ := by
  -- Unfold and work with left-associated appends:
  -- ((map(==q) ++ iH.encode) ++ flatMap(wH)) ++ oH.encode
  simp only [TMEncoding.encodeInputPattern] at heq
  -- Step 1: split off oH.encode from the right
  have hlen_prefix : (((List.finRange k).map (· == q₁) ++ iH₁.encode) ++
      (List.finRange n).flatMap (fun i => (wH₁ i).encode)).length =
    (((List.finRange k).map (· == q₂) ++ iH₂.encode) ++
      (List.finRange n).flatMap (fun i => (wH₂ i).encode)).length := by
    simp [List.length_append, flatMap_encode_length, Γ.encode_length]
  have h_prefix := List.append_inj_left heq hlen_prefix
  have h_oH := List.append_inj_right heq hlen_prefix
  have hoH : oH₁ = oH₂ := Γ.encode_injective h_oH
  -- Step 2: split off flatMap(wH)
  have hlen_sq : ((List.finRange k).map (· == q₁) ++ iH₁.encode).length =
      ((List.finRange k).map (· == q₂) ++ iH₂.encode).length := by
    simp [Γ.encode_length]
  have h_sq := List.append_inj_left h_prefix hlen_sq
  have h_wH := List.append_inj_right h_prefix hlen_sq
  -- Step 3: split stateMap from iH
  have hlen_state : ((List.finRange k).map (· == q₁)).length =
      ((List.finRange k).map (· == q₂)).length := by simp
  have h_s := List.append_inj_left h_sq hlen_state
  have h_iH := List.append_inj_right h_sq hlen_state
  -- q₁ = q₂ from one-hot
  have hq : q₁ = q₂ := by
    by_contra hne
    -- map(==q₁) and map(==q₂) are equal (h_s), but differ at position q₁.val
    have h_at := congrArg (fun l => l[q₁.val]?) h_s
    simp only [List.getElem?_map, List.getElem?_eq_getElem (by simp : q₁.val < (List.finRange k).length),
      Option.map_some, Option.some.injEq, List.getElem_finRange, Fin.cast_mk] at h_at
    -- h_at : (⟨q₁.val, _⟩ == q₁) = (⟨q₁.val, _⟩ == q₂)
    have : (⟨q₁.val, q₁.isLt⟩ : Fin k) = q₁ := Fin.ext rfl
    rw [show (⟨q₁.val, (by omega : q₁.val < k)⟩ : Fin k) = q₁ from Fin.ext rfl] at h_at
    rw [beq_self_eq_true] at h_at
    exact hne (beq_iff_eq.mp h_at.symm)
  have hiH : iH₁ = iH₂ := Γ.encode_injective h_iH
  -- wH₁ = wH₂ from flatMap equality
  have hwH : wH₁ = wH₂ := by
    ext ⟨i, hi⟩
    have hfw := fun (a : Fin n) (_ : a ∈ List.finRange n) => Γ.encode_length (wH₁ a)
    have hfw' := fun (a : Fin n) (_ : a ∈ List.finRange n) => Γ.encode_length (wH₂ a)
    have hidx : i < (List.finRange n).length := by simp; exact hi
    -- Extract per-position equality from list equality
    have hbound0 : i * 2 + 0 < (List.flatMap (fun j => (wH₁ j).encode) (List.finRange n)).length := by
      rw [flatMap_const_width_length _ _ 2 hfw]; exact mul_add_lt_mul_of_lt i 0 _ 2 hidx (by omega)
    have hbound1 : i * 2 + 1 < (List.flatMap (fun j => (wH₁ j).encode) (List.finRange n)).length := by
      rw [flatMap_const_width_length _ _ 2 hfw]; exact mul_add_lt_mul_of_lt i 1 _ 2 hidx (by omega)
    have hbound0' : i * 2 + 0 < (List.flatMap (fun j => (wH₂ j).encode) (List.finRange n)).length := by
      rw [flatMap_const_width_length _ _ 2 hfw']; exact mul_add_lt_mul_of_lt i 0 _ 2 hidx (by omega)
    have hbound1' : i * 2 + 1 < (List.flatMap (fun j => (wH₂ j).encode) (List.finRange n)).length := by
      rw [flatMap_const_width_length _ _ 2 hfw']; exact mul_add_lt_mul_of_lt i 1 _ 2 hidx (by omega)
    have h_eq0 : (List.flatMap (fun j => (wH₁ j).encode) (List.finRange n))[i * 2 + 0]'hbound0 =
                 (List.flatMap (fun j => (wH₂ j).encode) (List.finRange n))[i * 2 + 0]'hbound0' := by
      simp only [h_wH]
    have h_eq1 : (List.flatMap (fun j => (wH₁ j).encode) (List.finRange n))[i * 2 + 1]'hbound1 =
                 (List.flatMap (fun j => (wH₂ j).encode) (List.finRange n))[i * 2 + 1]'hbound1' := by
      simp only [h_wH]
    rw [flatMap_const_width_getElem _ _ 2 hfw i 0 hidx (by omega),
        flatMap_const_width_getElem _ _ 2 hfw' i 0 hidx (by omega)] at h_eq0
    rw [flatMap_const_width_getElem _ _ 2 hfw i 1 hidx (by omega),
        flatMap_const_width_getElem _ _ 2 hfw' i 1 hidx (by omega)] at h_eq1
    simp only [List.getElem_finRange] at h_eq0 h_eq1
    apply Γ.encode_injective
    apply List.ext_getElem (by simp [Γ.encode_length])
    intro j hj₁ _
    have : j < 2 := by rw [Γ.encode_length] at hj₁; exact hj₁
    match j, this with
    | 0, _ => convert h_eq0 using 2 <;> simp [Fin.ext_iff]
    | 1, _ => convert h_eq1 using 2 <;> simp [Fin.ext_iff]
  exact ⟨hq, hiH, hwH, hoH⟩

/-- Different 4-tuples produce different input pattern lists. -/
private theorem encodeInputPattern_ne_of_ne {k n : ℕ}
    {q₁ q₂ : Fin k} {iH₁ iH₂ : Γ} {wH₁ wH₂ : Fin n → Γ} {oH₁ oH₂ : Γ}
    (hne : (q₁, iH₁, wH₁, oH₁) ≠ (q₂, iH₂, wH₂, oH₂)) :
    TMEncoding.encodeInputPattern k n q₁ iH₁ wH₁ oH₁ ≠
    TMEncoding.encodeInputPattern k n q₂ iH₂ wH₂ oH₂ := by
  intro heq
  obtain ⟨hq, hi, hw, ho⟩ := encodeInputPattern_injective heq
  exact hne (by rw [hq, hi, hw, ho])

/-- Connect desc tape cell at `tableOffset + p` to transition table bit `p`.
    Key bridging lemma: the desc tape after header stores the transition table bits. -/
private theorem desc_cell_eq_table_bit {n : ℕ} (tm : TM n)
    (desc : List Bool) (t : Tape)
    (hdesc : desc = TMEncoding.encodeTM tm)
    (hdescOnTape : descOnTape desc t)
    (p : ℕ) (hp : p < (TMEncoding.encodeTransTable tm tm.stateEquiv).length) :
    t.cells (TMEncoding.tableOffset (Fintype.card tm.Q) n + p + 1) =
    Γ.ofBool ((TMEncoding.encodeTransTable tm tm.stateEquiv)[p]'hp) := by
  have hoff := encodeTM_header_length tm rfl
  have h_split := encodeTM_eq_header_append_table tm
  have h_idx : TMEncoding.tableOffset (Fintype.card tm.Q) n + p < desc.length := by
    rw [hdesc, h_split, List.length_append, hoff]; omega
  have h_cell := hdescOnTape.2.1 (TMEncoding.tableOffset (Fintype.card tm.Q) n + p) h_idx
  rw [h_cell]
  congr 1
  simp only [hdesc, h_split]
  rw [List.getElem_append_right (by rw [hoff]; omega)]
  congr 1; rw [hoff]; omega

/-- The entry function that maps a 4-tuple to its encoded entry using `tm.δ`. -/
private noncomputable def allTuples_entryFn {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q)) :
    Fin (Fintype.card tm.Q) × Γ × (Fin n → Γ) × Γ → List Bool :=
  fun ⟨q, iH, wH, oH⟩ =>
    let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iH wH oH
    TMEncoding.encodeEntry (Fintype.card tm.Q) n q iH wH oH (e q') wW oW iD wD oD

/-- The transition table equals `allTuples.flatMap (allTuples_entryFn tm e)`. -/
private theorem encodeTransTable_eq_allTuples_flatMap {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q)) :
    TMEncoding.encodeTransTable tm e =
    (allTuples (Fintype.card tm.Q) n).flatMap (allTuples_entryFn tm e) := by
  unfold TMEncoding.encodeTransTable allTuples allTuples_entryFn
  simp only [List.flatMap_assoc, List.flatMap_map]

/-- Every entry produced by `allTuples_entryFn` has width `entryWidth k n`. -/
private theorem allTuples_entryFn_width {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q))
    (t : Fin (Fintype.card tm.Q) × Γ × (Fin n → Γ) × Γ)
    (ht : t ∈ allTuples (Fintype.card tm.Q) n) :
    (allTuples_entryFn tm e t).length = TMEncoding.entryWidth (Fintype.card tm.Q) n := by
  obtain ⟨q, iH, wH, oH⟩ := t
  simp only [allTuples_entryFn]
  generalize tm.δ (e.symm q) iH wH oH = δ_result
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δ_result
  exact encodeEntry_length _ _ _ _ _ _ _ _ _ _ _ _

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: skipHeader simulation
-- ════════════════════════════════════════════════════════════════════════

/-- `Tape.write` preserves the head field. -/
private theorem lu_tape_write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp [Tape.write]; split <;> rfl

/-- Skip `rem` header bits on the desc tape, then one idle step to enter compare.
    From state `skipHeader rem`, after `rem + 1` steps reach state `compare 0`
    with desc head advanced by `rem`, all tapes preserved. -/
private theorem skipHeader_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q) (rem : ℕ) (hrem : rem ≤ TMEncoding.tableOffset k n)
    (hstate : c.state = .skipHeader ⟨rem, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (rem + 1) c c' ∧
      c'.state = .compare ⟨0, by omega⟩ ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + rem ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (∀ i, i ≠ utmDescTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction rem generalizing c with
  | zero =>
    -- skipHeader 0 → compare 0: one idle step preserving all tapes
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    -- Verify the step
    have hstep : ∃ c', (lookupTM (n := n) k).step c = some c' ∧
        c'.state = .compare ⟨0, by omega⟩ ∧
        (∀ i, c'.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c'.input = c.input.move (idleDir c.input.read) ∧
        c'.output = c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) := by
      simp only [TM.step, hne_halt, ↓reduceIte, lookupTM, hstate]
      refine ⟨_, rfl, rfl, fun i => rfl, rfl, rfl⟩
    obtain ⟨c', hstep', hst', hwork', hinp', hout'⟩ := hstep
    refine ⟨c', .step hstep' .zero, hst', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork']; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; omega
    · rw [hwork']; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]
    · intro i hne; rw [hwork']; exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
    · rw [hinp']; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    · rw [hout']; exact lu_tape_idle_preserve _ hout hout_h
    · constructor
      · intro i; rw [hwork']
        by_cases hi : i = utmDescTape
        · subst hi; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; exact hwf.1 _
        · rw [lu_tape_idle_preserve _ (hother i hi).1 (hother i hi).2]; exact hwf.1 _
      · intro i j hj; rw [hwork']
        by_cases hi : i = utmDescTape
        · subst hi; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; exact hwf.2 _ j hj
        · rw [lu_tape_idle_preserve _ (hother i hi).1 (hother i hi).2]; exact hwf.2 _ j hj
  | succ rem ih =>
    -- skipHeader (rem+1) → skipHeader rem: desc moves right, others preserved
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    -- Verify the step
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .skipHeader ⟨rem, by omega⟩ ∧
        (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
        (∀ i, i ≠ utmDescTape → c₁.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c₁.input = c.input.move (idleDir c.input.read) ∧
        c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      simp only [TM.step, hne_halt, ↓reduceIte, lookupTM, hstate]
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · show (c.work utmDescTape).writeAndMove (readBackWrite (c.work utmDescTape).read)
            (if utmDescTape = utmDescTape then Dir3.right
             else idleDir (c.work utmDescTape).read) = _
        simp only [↓reduceIte]
      · intro i hne
        show (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (if i = utmDescTape then Dir3.right else idleDir (c.work i).read) = _
        simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
    obtain ⟨c₁, hstep', hst₁, hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep
    -- Properties of c₁
    have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      rw [hdesc₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    have hc₁_other : ∀ i, i ≠ utmDescTape → c₁.work i = c.work i := by
      intro i hne; rw [hother₁ i hne]
      exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
    have hc₁_inp : c₁.input = c.input := by
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hc₁_out : c₁.output = c.output := by
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    have hc₁_wf : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.1 _
        · rw [hc₁_other i hi]; exact hwf.1 _
      · intro i j hj; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
        · rw [hc₁_other i hi]; exact hwf.2 _ j hj
    -- Apply IH
    obtain ⟨c', hreach', hst', hhead', hcells', hother', hinp', hout', hwf'⟩ :=
      ih c₁ (by omega) hst₁ hc₁_wf
        (by rw [hc₁_inp]; exact hinp) (by rw [hc₁_inp]; exact hinp_h)
        (by rw [hc₁_out]; exact hout) (by rw [hc₁_out]; exact hout_h)
        (by intro j hj; rw [hc₁_desc_cells]; exact hdesc_ns j hj)
        (by omega)
        (by intro i hne; rw [hc₁_other i hne]; exact hother i hne)
    refine ⟨c', .step hstep' hreach', hst', ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · rw [hhead', hc₁_desc_h]; omega
    · rw [hcells', hc₁_desc_cells]
    · intro i hne; rw [hother' i hne, hc₁_other i hne]
    · rw [hinp', hc₁_inp]
    · rw [hout', hc₁_out]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: compare simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Compare loop: all `ipw` bits match.
    From `compare 0` with desc and scratch both positioned at the start of
    a matching input pattern, after `ipw` steps reach `matchRewind` with
    desc advanced past the entire input pattern (positioned at the separator).

    The `hmatch` hypothesis asserts that desc and scratch store identical
    bits at positions `descStart + j` and `scratchStart + j` for all
    `j < ipw`. -/
private theorem compare_match_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (pos : ℕ) (hpos : pos < TMEncoding.inputPatternWidth k n)
    (hstate : c.state = .compare ⟨pos, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    -- The remaining ipw - pos bits all match
    (hmatch : ∀ (j : ℕ), j < TMEncoding.inputPatternWidth k n - pos →
      (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
      (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j)) :
    let ipw := TMEncoding.inputPatternWidth k n
    ∃ c',
      (lookupTM (n := n) k).reachesIn (ipw - pos) c c' ∧
      c'.state = .matchRewind ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + (ipw - pos) ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      -- Scratch advances by ipw - pos - 1 (last step only advances desc)
      (c'.work utmScratchTape).head = (c.work utmScratchTape).head + (ipw - pos - 1) ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro ipw
  -- Generalized loop: induction on diff = ipw - pos, universally quantifying c and pos
  suffices h_loop : ∀ (diff : ℕ) (c : Cfg 4 (lookupTM (n := n) k).Q) (pos : ℕ)
      (hpos : pos < ipw), diff = ipw - pos →
      c.state = .compare ⟨pos, by omega⟩ →
      WorkTapesWF c.work →
      c.input.read ≠ Γ.start → c.input.head ≥ 1 →
      c.output.read ≠ Γ.start → c.output.head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start) →
      (c.work utmDescTape).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start) →
      (c.work utmScratchTape).head ≥ 1 →
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
      (∀ j, j < ipw - pos → (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j)) →
      ∃ c', (lookupTM (n := n) k).reachesIn diff c c' ∧
        c'.state = .matchRewind ∧
        (c'.work utmDescTape).head = (c.work utmDescTape).head + diff ∧
        (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
        (c'.work utmScratchTape).head = (c.work utmScratchTape).head + (diff - 1) ∧
        (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
        c'.input = c.input ∧ c'.output = c.output ∧ WorkTapesWF c'.work from
    h_loop _ c pos hpos rfl hstate hwf hinp hinp_h hout hout_h hdesc_ns hdesc_h
      hscratch_ns hscratch_h hother hmatch
  intro diff; induction diff with
  | zero => intro c pos hpos hdiff; omega
  | succ diff ih =>
    intro c pos hpos hdiff hstate hwf hinp hinp_h hout hout_h hdesc_ns hdesc_h
      hscratch_ns hscratch_h hother hmatch_bits
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
    have hdesc_read := lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hscratch_read := lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
    have hmatch0 : (c.work utmDescTape).read = (c.work utmScratchTape).read := by
      simp only [Tape.read]; exact hmatch_bits 0 (by omega)
    by_cases hlast : pos + 1 < ipw
    · -- Match, more bits: both tapes right, state → compare(pos+1), then IH
      have hstep_eq : (lookupTM (n := n) k).step c = some
          { state := .compare ⟨pos + 1, by omega⟩,
            input := c.input.move (idleDir c.input.read),
            work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (if i = utmDescTape then Dir3.right
               else if i = utmScratchTape then Dir3.right
               else idleDir (c.work i).read),
            output := c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read) } := by
        simp only [TM.step, lookupTM, hstate]
        split_ifs <;> first | rfl | contradiction
      have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
          c₁.state = .compare ⟨pos + 1, by omega⟩ ∧
          (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
            (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
          (c₁.work utmScratchTape = (c.work utmScratchTape).writeAndMove
            (readBackWrite (c.work utmScratchTape).read) Dir3.right) ∧
          (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₁.work i = (c.work i).writeAndMove
            (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
          c₁.input = c.input.move (idleDir c.input.read) ∧
          c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) := by
        refine ⟨_, hstep_eq, rfl, ?_, ?_, ?_, rfl, rfl⟩
        · dsimp only []; simp only [↓reduceIte]
        · dsimp only []; simp only [show ¬(utmScratchTape = utmDescTape) from (by decide), ↓reduceIte]
        · intro i hne_d hne_s; dsimp only []
          simp only [show ¬(i = utmDescTape) from hne_d,
            show ¬(i = utmScratchTape) from hne_s, ↓reduceIte]
      obtain ⟨c₁, hstep', hst₁, hdesc₁, hscratch₁, hother₁, hinp₁, hout₁⟩ := hstep
      -- Properties of c₁
      have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
        rw [hdesc₁, Tape.writeAndMove, Tape.move]
        show (Tape.write _ _).head + 1 = _
        rw [lu_tape_write_head]
      have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
        rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
        split
        · rfl
        · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
      have hc₁_scratch_h : (c₁.work utmScratchTape).head = (c.work utmScratchTape).head + 1 := by
        rw [hscratch₁, Tape.writeAndMove, Tape.move]
        show (Tape.write _ _).head + 1 = _
        rw [lu_tape_write_head]
      have hc₁_scratch_cells : (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells := by
        rw [hscratch₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
        split
        · rfl
        · rw [lu_readBackWrite_toΓ_eq hscratch_read]; exact Function.update_eq_self _ _
      have hc₁_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₁.work i = c.work i := by
        intro i hne_d hne_s; rw [hother₁ i hne_d hne_s]
        exact lu_tape_idle_preserve _ (hother i hne_d hne_s).1 (hother i hne_d hne_s).2
      have hc₁_inp : c₁.input = c.input := by
        rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      have hc₁_out : c₁.output = c.output := by
        rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
      have hc₁_wf : WorkTapesWF c₁.work := by
        constructor
        · intro i
          by_cases hi_d : i = utmDescTape
          · subst hi_d; rw [hc₁_desc_cells]; exact hwf.1 _
          · by_cases hi_s : i = utmScratchTape
            · subst hi_s; rw [hc₁_scratch_cells]; exact hwf.1 _
            · rw [hc₁_other i hi_d hi_s]; exact hwf.1 _
        · intro i j hj
          by_cases hi_d : i = utmDescTape
          · subst hi_d; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
          · by_cases hi_s : i = utmScratchTape
            · subst hi_s; rw [hc₁_scratch_cells]; exact hwf.2 _ j hj
            · rw [hc₁_other i hi_d hi_s]; exact hwf.2 _ j hj
      -- Apply IH
      obtain ⟨c', hreach', hst', hhead', hcells', hshead', hscells', hother', hinp', hout', hwf'⟩ :=
        ih c₁ (pos + 1) (by omega) (by omega) hst₁ hc₁_wf
          (by rw [hc₁_inp]; exact hinp) (by rw [hc₁_inp]; exact hinp_h)
          (by rw [hc₁_out]; exact hout) (by rw [hc₁_out]; exact hout_h)
          (by intro j hj; rw [hc₁_desc_cells]; exact hdesc_ns j hj)
          (by omega)
          (by intro j hj; rw [hc₁_scratch_cells]; exact hscratch_ns j hj)
          (by omega)
          (by intro i hne_d hne_s; rw [hc₁_other i hne_d hne_s]; exact hother i hne_d hne_s)
          (by intro j hj
              rw [hc₁_desc_cells, hc₁_desc_h, hc₁_scratch_cells, hc₁_scratch_h]
              have := hmatch_bits (j + 1) (by omega)
              convert this using 2 <;> omega)
      refine ⟨c', .step hstep' hreach', hst', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf'⟩
      · rw [hhead', hc₁_desc_h]; omega
      · rw [hcells', hc₁_desc_cells]
      · rw [hshead', hc₁_scratch_h]; omega
      · rw [hscells', hc₁_scratch_cells]
      · intro i hne_d hne_s; rw [hother' i hne_d hne_s, hc₁_other i hne_d hne_s]
      · rw [hinp', hc₁_inp]
      · rw [hout', hc₁_out]
    · -- Last bit: full match. desc +1, scratch stays. State → matchRewind.
      -- diff = 0 because pos + 1 ≥ ipw
      have hdiff0 : diff = 0 := by omega
      subst hdiff0
      have hstep' : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
          c₁.state = .matchRewind ∧
          (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
            (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
          (∀ i, i ≠ utmDescTape → c₁.work i = (c.work i).writeAndMove
            (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
          c₁.input = c.input.move (idleDir c.input.read) ∧
          c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) := by
        simp only [TM.step, lookupTM, hstate]
        split_ifs <;> try (first | rfl | contradiction)
        refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
        · dsimp only []; simp only [↓reduceIte]
        · intro i hne; dsimp only []
          simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
      obtain ⟨c₁, hstep₁, hst₁, hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep'
      -- Properties of c₁
      have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
        rw [hdesc₁, Tape.writeAndMove, Tape.move]
        show (Tape.write _ _).head + 1 = _
        rw [lu_tape_write_head]
      have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
        rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
        split
        · rfl
        · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
      have hc₁_other : ∀ i, i ≠ utmDescTape → c₁.work i = c.work i := by
        intro i hne; rw [hother₁ i hne]
        by_cases hi : i = utmScratchTape
        · subst hi; exact lu_tape_idle_preserve _ hscratch_read hscratch_h
        · exact lu_tape_idle_preserve _ (hother i hne hi).1 (hother i hne hi).2
      have hc₁_inp : c₁.input = c.input := by
        rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      have hc₁_out : c₁.output = c.output := by
        rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
      refine ⟨c₁, .step hstep₁ .zero, hst₁, ?_, hc₁_desc_cells, ?_, ?_, ?_, hc₁_inp, hc₁_out, ?_⟩
      · rw [hc₁_desc_h]
      · -- scratch head: 0 + 1 - 1 = 0, so head stays same
        simp only [show 0 + 1 - 1 = 0 from rfl, Nat.add_zero]
        rw [hc₁_other utmScratchTape (by decide)]
      · -- scratch cells preserved
        rw [hc₁_other utmScratchTape (by decide)]
      · intro i hne_d hne_s; exact hc₁_other i hne_d
      · constructor
        · intro i; by_cases hi : i = utmDescTape
          · subst hi; rw [hc₁_desc_cells]; exact hwf.1 _
          · rw [hc₁_other i hi]; exact hwf.1 _
        · intro i j hj; by_cases hi : i = utmDescTape
          · subst hi; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
          · rw [hc₁_other i hi]; exact hwf.2 _ j hj

/-- Compare mismatch: the first mismatch is at position `mismatchPos`.
    From `compare 0` with a mismatch at position `mismatchPos < ipw`,
    after `mismatchPos + 1` steps reach `skipRest (ew - mismatchPos - 1)`.

    The `hmatch_before` hypothesis says bits match for all `j < mismatchPos`.
    The `hmismatch` hypothesis says the bit at `mismatchPos` differs. -/
private theorem compare_mismatch
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (mismatchPos : ℕ) (hmp : mismatchPos < TMEncoding.inputPatternWidth k n)
    (hstate : c.state = .compare ⟨0, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    -- Bits match before the mismatch position
    (hmatch_before : ∀ (j : ℕ), j < mismatchPos →
      (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
      (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j))
    -- The bit at mismatchPos differs
    (hmismatch :
      (c.work utmDescTape).cells ((c.work utmDescTape).head + mismatchPos) ≠
      (c.work utmScratchTape).cells ((c.work utmScratchTape).head + mismatchPos)) :
    have hmp' : mismatchPos < k + 2 + 2 * n + 2 := hmp
    have hew_bound : mismatchPos + 1 ≤ TMEncoding.entryWidth k n := by
      show mismatchPos + 1 ≤ (k + 2 + 2 * n + 2) + 1 + (k + 2 * n + 2 + 2 + 2 * n + 2)
      omega
    ∃ c',
      (lookupTM (n := n) k).reachesIn (mismatchPos + 1) c c' ∧
      c'.state = .skipRest ⟨TMEncoding.entryWidth k n - mismatchPos - 1, by omega⟩ ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + mismatchPos + 1 ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (c'.work utmScratchTape).head = (c.work utmScratchTape).head + mismatchPos ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  -- Generalized loop: induction on mismatchPos, universally quantifying c and pos
  -- We track the current compare position pos
  suffices h_loop : ∀ (mp : ℕ) (c : Cfg 4 (lookupTM (n := n) k).Q) (pos : ℕ)
      (hpos : pos + mp < TMEncoding.inputPatternWidth k n),
      c.state = .compare ⟨pos, by omega⟩ →
      WorkTapesWF c.work →
      c.input.read ≠ Γ.start → c.input.head ≥ 1 →
      c.output.read ≠ Γ.start → c.output.head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start) →
      (c.work utmDescTape).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start) →
      (c.work utmScratchTape).head ≥ 1 →
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
      (∀ j, j < mp → (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j)) →
      (c.work utmDescTape).cells ((c.work utmDescTape).head + mp) ≠
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + mp) →
      ∃ c', (lookupTM (n := n) k).reachesIn (mp + 1) c c' ∧
        c'.state = .skipRest ⟨TMEncoding.entryWidth k n - (pos + mp) - 1, by omega⟩ ∧
        (c'.work utmDescTape).head = (c.work utmDescTape).head + mp + 1 ∧
        (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
        (c'.work utmScratchTape).head = (c.work utmScratchTape).head + mp ∧
        (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
        c'.input = c.input ∧ c'.output = c.output ∧ WorkTapesWF c'.work from by
    obtain ⟨c', hreach, hst, hd, hdc, hs, hsc, ho, hi, hou, hwf'⟩ :=
      h_loop mismatchPos c 0 (by omega) hstate hwf hinp hinp_h hout hout_h hdesc_ns hdesc_h
        hscratch_ns hscratch_h hother hmatch_before hmismatch
    refine ⟨c', hreach, ?_, hd, hdc, hs, hsc, ho, hi, hou, hwf'⟩
    simp only [Nat.zero_add] at hst; exact hst
  intro mp; induction mp with
  | zero =>
    intro c pos hpos hstate hwf hinp hinp_h hout hout_h hdesc_ns hdesc_h
      hscratch_ns hscratch_h hother _ hmismatch
    -- One mismatch step: desc reads ≠ scratch reads
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
    have hdesc_read := lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hscratch_read := lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
    have hmismatch0 : (c.work utmDescTape).read ≠ (c.work utmScratchTape).read := by
      simp only [Tape.read]; exact hmismatch
    -- The mismatch step: desc advances, scratch stays, state → skipRest
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .skipRest ⟨TMEncoding.entryWidth k n - pos - 1, by omega⟩ ∧
        (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
        (∀ i, i ≠ utmDescTape → c₁.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c₁.input = c.input.move (idleDir c.input.read) ∧
        c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      simp only [TM.step, lookupTM, hstate, hmismatch0]
      split_ifs <;> try (first | rfl | contradiction)
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · dsimp only []; simp only [↓reduceIte]
      · intro i hne; dsimp only []
        simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
    obtain ⟨c₁, hstep', hst₁, hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep
    have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      rw [hdesc₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    have hc₁_other : ∀ i, i ≠ utmDescTape → c₁.work i = c.work i := by
      intro i hne; rw [hother₁ i hne]
      by_cases hi : i = utmScratchTape
      · subst hi; exact lu_tape_idle_preserve _ hscratch_read hscratch_h
      · exact lu_tape_idle_preserve _ (hother i hne hi).1 (hother i hne hi).2
    have hc₁_inp : c₁.input = c.input := by
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hc₁_out : c₁.output = c.output := by
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    refine ⟨c₁, .step hstep' .zero, hst₁, ?_, hc₁_desc_cells, ?_, ?_, ?_, hc₁_inp, hc₁_out, ?_⟩
    · rw [hc₁_desc_h]
    · simp only [Nat.add_zero]; rw [hc₁_other utmScratchTape (by decide)]
    · rw [hc₁_other utmScratchTape (by decide)]
    · intro i hne_d hne_s; exact hc₁_other i hne_d
    · constructor
      · intro i; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.1 _
        · rw [hc₁_other i hi]; exact hwf.1 _
      · intro i j hj; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
        · rw [hc₁_other i hi]; exact hwf.2 _ j hj
  | succ mp ih =>
    intro c pos hpos hstate hwf hinp hinp_h hout hout_h hdesc_ns hdesc_h
      hscratch_ns hscratch_h hother hmatch_before hmismatch
    -- One matching step, then IH
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
    have hdesc_read := lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hscratch_read := lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
    have hmatch0 : (c.work utmDescTape).read = (c.work utmScratchTape).read := by
      simp only [Tape.read]; exact hmatch_before 0 (by omega)
    -- Match step: both desc and scratch advance
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .compare ⟨pos + 1, by omega⟩ ∧
        (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
        (c₁.work utmScratchTape = (c.work utmScratchTape).writeAndMove
          (readBackWrite (c.work utmScratchTape).read) Dir3.right) ∧
        (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₁.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c₁.input = c.input.move (idleDir c.input.read) ∧
        c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      have hpos1 : pos + 1 < TMEncoding.inputPatternWidth k n := by omega
      simp only [TM.step, lookupTM, hstate, hmatch0, hpos1]
      split_ifs <;> try (first | rfl | contradiction)
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
      · dsimp only []; simp only [↓reduceIte]; rw [hmatch0]
      · dsimp only []; simp only [show ¬(utmScratchTape = utmDescTape) from (by decide), ↓reduceIte]
      · intro i hne_d hne_s; dsimp only []
        simp only [show ¬(i = utmDescTape) from hne_d,
          show ¬(i = utmScratchTape) from hne_s, ↓reduceIte]
    obtain ⟨c₁, hstep', hst₁, hdesc₁, hscratch₁, hother₁, hinp₁, hout₁⟩ := hstep
    -- Properties of c₁
    have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      rw [hdesc₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    have hc₁_scratch_h : (c₁.work utmScratchTape).head = (c.work utmScratchTape).head + 1 := by
      rw [hscratch₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_scratch_cells : (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells := by
      rw [hscratch₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hscratch_read]; exact Function.update_eq_self _ _
    have hc₁_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₁.work i = c.work i := by
      intro i hne_d hne_s; rw [hother₁ i hne_d hne_s]
      exact lu_tape_idle_preserve _ (hother i hne_d hne_s).1 (hother i hne_d hne_s).2
    have hc₁_inp : c₁.input = c.input := by
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hc₁_out : c₁.output = c.output := by
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    have hc₁_wf : WorkTapesWF c₁.work := by
      constructor
      · intro i
        by_cases hi_d : i = utmDescTape
        · subst hi_d; rw [hc₁_desc_cells]; exact hwf.1 _
        · by_cases hi_s : i = utmScratchTape
          · subst hi_s; rw [hc₁_scratch_cells]; exact hwf.1 _
          · rw [hc₁_other i hi_d hi_s]; exact hwf.1 _
      · intro i j hj
        by_cases hi_d : i = utmDescTape
        · subst hi_d; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
        · by_cases hi_s : i = utmScratchTape
          · subst hi_s; rw [hc₁_scratch_cells]; exact hwf.2 _ j hj
          · rw [hc₁_other i hi_d hi_s]; exact hwf.2 _ j hj
    -- Apply IH
    obtain ⟨c', hreach', hst', hhead', hcells', hshead', hscells', hother', hinp', hout', hwf'⟩ :=
      ih c₁ (pos + 1) (by omega) hst₁ hc₁_wf
        (by rw [hc₁_inp]; exact hinp) (by rw [hc₁_inp]; exact hinp_h)
        (by rw [hc₁_out]; exact hout) (by rw [hc₁_out]; exact hout_h)
        (by intro j hj; rw [hc₁_desc_cells]; exact hdesc_ns j hj)
        (by omega)
        (by intro j hj; rw [hc₁_scratch_cells]; exact hscratch_ns j hj)
        (by omega)
        (by intro i hne_d hne_s; rw [hc₁_other i hne_d hne_s]; exact hother i hne_d hne_s)
        (by intro j hj
            rw [hc₁_desc_cells, hc₁_desc_h, hc₁_scratch_cells, hc₁_scratch_h]
            have := hmatch_before (j + 1) (by omega)
            convert this using 2 <;> omega)
        (by rw [hc₁_desc_cells, hc₁_desc_h, hc₁_scratch_cells, hc₁_scratch_h]
            convert hmismatch using 2 <;> omega)
    refine ⟨c', .step hstep' hreach', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · simp only [show pos + (mp + 1) = pos + 1 + mp from by omega]; exact hst'
    · rw [hhead', hc₁_desc_h]; omega
    · rw [hcells', hc₁_desc_cells]
    · rw [hshead', hc₁_scratch_h]; omega
    · rw [hscells', hc₁_scratch_cells]
    · intro i hne_d hne_s; rw [hother' i hne_d hne_s, hc₁_other i hne_d hne_s]
    · rw [hinp', hc₁_inp]
    · rw [hout', hc₁_out]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3: skipRest simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Skip `rem` remaining bits of the current entry on desc.
    From `skipRest rem`, after `rem + 1` steps reach `rewindScratch` with
    desc advanced by `rem`, all other tapes preserved. -/
private theorem skipRest_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (rem : ℕ) (hrem : rem ≤ TMEncoding.entryWidth k n)
    (hstate : c.state = .skipRest ⟨rem, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (rem + 1) c c' ∧
      c'.state = .rewindScratch ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + rem ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (∀ i, i ≠ utmDescTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  -- Identical structure to skipHeader_loop: induction on rem, desc moves right
  induction rem generalizing c with
  | zero =>
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hstep : ∃ c', (lookupTM (n := n) k).step c = some c' ∧
        c'.state = .rewindScratch ∧
        (∀ i, c'.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c'.input = c.input.move (idleDir c.input.read) ∧
        c'.output = c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) := by
      simp only [TM.step, hne_halt, ↓reduceIte, lookupTM, hstate]
      refine ⟨_, rfl, rfl, fun i => rfl, rfl, rfl⟩
    obtain ⟨c', hstep', hst', hwork', hinp', hout'⟩ := hstep
    refine ⟨c', .step hstep' .zero, hst', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork']; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; omega
    · rw [hwork']; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]
    · intro i hne; rw [hwork']; exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
    · rw [hinp']; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    · rw [hout']; exact lu_tape_idle_preserve _ hout hout_h
    · constructor
      · intro i; rw [hwork']
        by_cases hi : i = utmDescTape
        · subst hi; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; exact hwf.1 _
        · rw [lu_tape_idle_preserve _ (hother i hi).1 (hother i hi).2]; exact hwf.1 _
      · intro i j hj; rw [hwork']
        by_cases hi : i = utmDescTape
        · subst hi; rw [lu_tape_idle_preserve _ hdesc_read hdesc_h]; exact hwf.2 _ j hj
        · rw [lu_tape_idle_preserve _ (hother i hi).1 (hother i hi).2]; exact hwf.2 _ j hj
  | succ rem ih =>
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .skipRest ⟨rem, by omega⟩ ∧
        (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
        (∀ i, i ≠ utmDescTape → c₁.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c₁.input = c.input.move (idleDir c.input.read) ∧
        c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      simp only [TM.step, hne_halt, ↓reduceIte, lookupTM, hstate]
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · show (c.work utmDescTape).writeAndMove (readBackWrite (c.work utmDescTape).read)
            (if utmDescTape = utmDescTape then Dir3.right
             else idleDir (c.work utmDescTape).read) = _
        simp only [↓reduceIte]
      · intro i hne
        show (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (if i = utmDescTape then Dir3.right else idleDir (c.work i).read) = _
        simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
    obtain ⟨c₁, hstep', hst₁, hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep
    have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      rw [hdesc₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    have hc₁_other : ∀ i, i ≠ utmDescTape → c₁.work i = c.work i := by
      intro i hne; rw [hother₁ i hne]
      exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
    have hc₁_inp : c₁.input = c.input := by
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hc₁_out : c₁.output = c.output := by
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    have hc₁_wf : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.1 _
        · rw [hc₁_other i hi]; exact hwf.1 _
      · intro i j hj; by_cases hi : i = utmDescTape
        · subst hi; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
        · rw [hc₁_other i hi]; exact hwf.2 _ j hj
    obtain ⟨c', hreach', hst', hhead', hcells', hother', hinp', hout', hwf'⟩ :=
      ih c₁ (by omega) hst₁ hc₁_wf
        (by rw [hc₁_inp]; exact hinp) (by rw [hc₁_inp]; exact hinp_h)
        (by rw [hc₁_out]; exact hout) (by rw [hc₁_out]; exact hout_h)
        (by intro j hj; rw [hc₁_desc_cells]; exact hdesc_ns j hj)
        (by omega)
        (by intro i hne; rw [hc₁_other i hne]; exact hother i hne)
    refine ⟨c', .step hstep' hreach', hst', ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · rw [hhead', hc₁_desc_h]; omega
    · rw [hcells', hc₁_desc_cells]
    · intro i hne; rw [hother' i hne, hc₁_other i hne]
    · rw [hinp', hc₁_inp]
    · rw [hout', hc₁_out]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 4: rewindScratch simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind the scratch tape to cell 1 after mismatch.
    From `rewindScratch` with scratch head at position `sh`, after `sh + 2`
    steps reach `compare 0` (via `rewindScratchR`), with scratch head = 1.

    The extra +2 accounts for: hit ▷ at cell 0 (1 step to `rewindScratchR`),
    then move right to cell 1 and transition to `compare 0` (1 step). -/
private theorem rewindScratch_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q) (sh : ℕ)
    (hstate : c.state = .rewindScratch)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = sh)
    (hother : ∀ i, i ≠ utmScratchTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (sh + 2) c c' ∧
      c'.state = .compare ⟨0, by omega⟩ ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction sh generalizing c with
  | zero =>
    -- scratch head = 0, so read ▷ at cell 0
    have hread : (c.work utmScratchTape).read = Γ.start := by
      simp [Tape.read, hscratch_h, hwf.1 utmScratchTape]
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    -- Step 1: rewindScratch → rewindScratchR (read ▷, move right)
    have hstep1 : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindScratchR ∧
        (c₁.work utmScratchTape).head = 1 ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep1
    -- Step 2: rewindScratchR → compare 0 (all idle)
    have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
      intro i; by_cases h : i = utmScratchTape
      · rw [h]; omega
      · rw [hw1 i h]; exact (hother i h).2
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    have hinp1' : c₁.input.read ≠ Γ.start := by rw [hinp1]; exact hinp
    have hout1' : c₁.output.read ≠ Γ.start := by rw [hout1]; exact hout
    have hstep2 : ∃ c₂, (lookupTM (n := n) k).step c₁ = some c₂ ∧
        c₂.state = .compare ⟨0, by omega⟩ ∧
        c₂.work = c₁.work ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output := by
      simp only [TM.step, lookupTM, hst1]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · ext i; dsimp only []
        exact lu_tape_idle_preserve (c₁.work i)
          (lu_tape_read_ne_start_of_wf _ (hheads1 i) (hwf1.2 i)) (hheads1 i)
      · simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve c₁.output hout1' (by rw [hout1]; exact hout_h)
    obtain ⟨c₂, hstep2', hst2, hwork2, hinp2, hout2⟩ := hstep2
    refine ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork2]; exact hhead1
    · rw [hwork2, hcells1]
    · intro i hne; rw [hwork2, hw1 i hne]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]
    · rw [hwork2]; exact hwf1
  | succ sh ih =>
    have hread_ne : (c.work utmScratchTape).read ≠ Γ.start := by
      simp [Tape.read, hscratch_h]; exact hscratch_ns (sh + 1) (by omega)
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindScratch ∧
        (c₁.work utmScratchTape).head = sh ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ := ih c₁
      hst1 hwf1
      (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
      (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
      (by intro j hj; rw [hcells1]; exact hscratch_ns j hj)
      hhead1
      (by intro i hne; rw [hw1 i hne]; exact hother i hne)
    refine ⟨c_f, .step hstep' hreach, hst_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 5: process a non-matching entry
-- ════════════════════════════════════════════════════════════════════════

/-- Process one non-matching entry: compare → mismatch → skipRest → rewindScratch → compare.
    Combines `compare_mismatch`, `skipRest_loop`, and `rewindScratch_loop`.

    From `compare 0` at the start of a non-matching entry, reach `compare 0`
    at the start of the next entry, with desc advanced by `entryWidth` and
    scratch rewound to cell 1. -/
private theorem process_nonmatch_entry
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (mismatchPos : ℕ) (hmp : mismatchPos < TMEncoding.inputPatternWidth k n)
    (hstate : c.state = .compare ⟨0, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hmatch_before : ∀ (j : ℕ), j < mismatchPos →
      (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
      (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j))
    (hmismatch :
      (c.work utmDescTape).cells ((c.work utmDescTape).head + mismatchPos) ≠
      (c.work utmScratchTape).cells ((c.work utmScratchTape).head + mismatchPos)) :
    ∃ (c' : Cfg 4 (lookupTM (n := n) k).Q) (steps : ℕ),
      steps ≤ TMEncoding.entryWidth k n + TMEncoding.inputPatternWidth k n + 3 ∧
      (lookupTM (n := n) k).reachesIn steps c c' ∧
      c'.state = .compare ⟨0, by omega⟩ ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + TMEncoding.entryWidth k n ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  -- Step 1: compare_mismatch
  obtain ⟨c₁, hreach₁, hst₁, hd₁, hdc₁, hs₁, hsc₁, ho₁, hi₁, hou₁, hwf₁⟩ :=
    compare_mismatch c mismatchPos hmp hstate hwf hinp hinp_h hout hout_h
      hdesc_ns hdesc_h hscratch_ns (by omega) hother hmatch_before hmismatch
  -- Step 2: skipRest_loop
  have hskip_rem : TMEncoding.entryWidth k n - mismatchPos - 1 ≤ TMEncoding.entryWidth k n := by omega
  have hc₁_scratch_read : (c₁.work utmScratchTape).read ≠ Γ.start :=
    lu_tape_read_ne_start_of_wf _ (by rw [hs₁, hscratch_h]; omega)
      (by intro j hj; rw [hsc₁]; exact hscratch_ns j hj)
  obtain ⟨c₂, hreach₂, hst₂, hd₂, hdc₂, ho₂, hi₂, hou₂, hwf₂⟩ :=
    skipRest_loop c₁ (TMEncoding.entryWidth k n - mismatchPos - 1) hskip_rem hst₁ hwf₁
      (by rw [hi₁]; exact hinp) (by rw [hi₁]; exact hinp_h)
      (by rw [hou₁]; exact hout) (by rw [hou₁]; exact hout_h)
      (by intro j hj; rw [hdc₁]; exact hdesc_ns j hj)
      (by rw [hd₁]; omega)
      (by intro i hne
          by_cases hi : i = utmScratchTape
          · subst hi; exact ⟨hc₁_scratch_read, by rw [hs₁, hscratch_h]; omega⟩
          · exact ⟨by rw [ho₁ i hne hi]; exact (hother i hne hi).1,
                   by rw [ho₁ i hne hi]; exact (hother i hne hi).2⟩)
  -- Step 3: rewindScratch_loop
  have hscratch_h₂ : (c₂.work utmScratchTape).head =
      (c.work utmScratchTape).head + mismatchPos := by
    rw [ho₂ utmScratchTape (by decide)]; exact hs₁
  have hscratch_ns₂ : ∀ j, j ≥ 1 → (c₂.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [ho₂ utmScratchTape (by decide), hsc₁]; exact hscratch_ns j hj
  obtain ⟨c₃, hreach₃, hst₃, hsh₃, hsc₃, ho₃, hi₃, hou₃, hwf₃⟩ :=
    rewindScratch_loop c₂ ((c.work utmScratchTape).head + mismatchPos)
      hst₂ hwf₂
      (by rw [hi₂, hi₁]; exact hinp) (by rw [hi₂, hi₁]; exact hinp_h)
      (by rw [hou₂, hou₁]; exact hout) (by rw [hou₂, hou₁]; exact hout_h)
      hscratch_ns₂
      hscratch_h₂
      (by intro i hne
          by_cases hi_d : i = utmDescTape
          · subst hi_d; constructor
            · exact lu_tape_read_ne_start_of_wf _ (by rw [hd₂, hd₁]; omega)
                (by intro j hj; rw [hdc₂, hdc₁]; exact hdesc_ns j hj)
            · rw [hd₂, hd₁]; omega
          · constructor
            · rw [ho₂ i (show i ≠ utmDescTape from hi_d), ho₁ i hi_d hne]
              exact (hother i hi_d hne).1
            · rw [ho₂ i (show i ≠ utmDescTape from hi_d), ho₁ i hi_d hne]
              exact (hother i hi_d hne).2)
  -- Compose all three
  refine ⟨c₃, _, ?_, reachesIn_trans _ (reachesIn_trans _ hreach₁ hreach₂) hreach₃,
    hst₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf₃⟩
  · -- step bound: (mismatchPos + 1) + (ew - mismatchPos - 1 + 1) + (1 + mismatchPos + 2) ≤ ew + ipw + 3
    have : TMEncoding.entryWidth k n ≥ mismatchPos + 1 := by
      simp [TMEncoding.entryWidth, TMEncoding.inputPatternWidth] at hmp ⊢; omega
    rw [hscratch_h]; omega
  · -- desc head
    rw [ho₃ utmDescTape (by decide), hd₂, hd₁]
    have : TMEncoding.entryWidth k n ≥ mismatchPos + 1 := by
      simp [TMEncoding.entryWidth, TMEncoding.inputPatternWidth] at hmp ⊢; omega
    omega
  · rw [ho₃ utmDescTape (by decide), hdc₂, hdc₁]
  · exact hsh₃
  · rw [hsc₃, ho₂ utmScratchTape (by decide), hsc₁]
  · intro i hne_d hne_s
    rw [ho₃ i hne_s, ho₂ i (show i ≠ utmDescTape from hne_d), ho₁ i hne_d hne_s]
  · rw [hi₃, hi₂, hi₁]
  · rw [hou₃, hou₂, hou₁]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 6: scan past non-matching entries to find the match
-- ════════════════════════════════════════════════════════════════════════

/-- Scan past `numBefore` non-matching entries and reach the matching entry.
    From `compare 0` with desc at the first entry, after processing
    `numBefore` non-matching entries, reach `matchRewind` positioned at the
    matching entry's separator on desc.

    This is proved by induction on `numBefore`, composing
    `process_nonmatch_entry` for each non-matching entry and finishing with
    `compare_match_loop` on the matching entry. -/
private theorem entry_scan_to_match
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (numBefore : ℕ)
    (hstate : c.state = .compare ⟨0, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    -- Each of the numBefore entries before the match has a mismatch position
    (hnonmatch : ∀ (j : ℕ), j < numBefore →
      ∃ mismatchPos, mismatchPos < TMEncoding.inputPatternWidth k n ∧
        (c.work utmDescTape).cells
          ((c.work utmDescTape).head + j * TMEncoding.entryWidth k n + mismatchPos) ≠
        (c.work utmScratchTape).cells (1 + mismatchPos))
    -- The matching entry at position numBefore has all bits matching
    (hmatch_entry : ∀ (j : ℕ), j < TMEncoding.inputPatternWidth k n →
      (c.work utmDescTape).cells
        ((c.work utmDescTape).head + numBefore * TMEncoding.entryWidth k n + j) =
      (c.work utmScratchTape).cells (1 + j)) :
    ∃ (c' : Cfg 4 (lookupTM (n := n) k).Q) (steps : ℕ),
      steps ≤ numBefore * (TMEncoding.entryWidth k n + TMEncoding.inputPatternWidth k n + 4) +
        TMEncoding.inputPatternWidth k n ∧
      (lookupTM (n := n) k).reachesIn steps c c' ∧
      c'.state = .matchRewind ∧
      (c'.work utmDescTape).head =
        (c.work utmDescTape).head + numBefore * TMEncoding.entryWidth k n +
          TMEncoding.inputPatternWidth k n ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      -- Scratch advanced by ipw - 1 (last compare step only advances desc)
      (c'.work utmScratchTape).head = TMEncoding.inputPatternWidth k n ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction numBefore generalizing c with
  | zero =>
    -- No non-matching entries: apply compare_match_loop directly
    have hipw : 0 < TMEncoding.inputPatternWidth k n := by
      simp [TMEncoding.inputPatternWidth]
    obtain ⟨c', hreach, hst, hd, hdc, hs, hsc, ho, hi, hou, hwf'⟩ :=
      compare_match_loop c 0 hipw hstate hwf hinp hinp_h hout hout_h
        hdesc_ns hdesc_h hscratch_ns (by rw [hscratch_h]) hother
        (by intro j hj; rw [hscratch_h]
            have := hmatch_entry j hj; simp only [Nat.zero_mul, Nat.zero_add] at this
            exact this)
    refine ⟨c', _, ?_, hreach, hst, ?_, hdc, ?_, hsc, ho, hi, hou, hwf'⟩
    · omega
    · rw [hd]; omega
    · rw [hs, hscratch_h]; omega
  | succ numBefore ih =>
    -- Process one non-matching entry, then IH
    obtain ⟨mpPos, hmpPos_lt, hmpPos_ne⟩ := hnonmatch 0 (by omega)
    -- Find the first mismatch position
    have hne : (c.work utmDescTape).cells ((c.work utmDescTape).head + mpPos) ≠
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + mpPos) := by
      rw [hscratch_h]; simpa using hmpPos_ne
    -- Find the first mismatch using Nat.find
    have hdec : ∀ j, Decidable ((c.work utmDescTape).cells ((c.work utmDescTape).head + j) ≠
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j)) := by
      intro j; exact instDecidableNot
    have hex_raw : ∃ fm, (c.work utmDescTape).cells ((c.work utmDescTape).head + fm) ≠
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + fm) := ⟨mpPos, hne⟩
    set firstMismatch := Nat.find hex_raw with hfm_def
    have hfm_ne : (c.work utmDescTape).cells ((c.work utmDescTape).head + firstMismatch) ≠
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + firstMismatch) :=
      Nat.find_spec hex_raw
    have hfm_before : ∀ j, j < firstMismatch →
        (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
        (c.work utmScratchTape).cells ((c.work utmScratchTape).head + j) := by
      intro j hj; by_contra h
      exact Nat.find_min hex_raw hj h
    have hfm_le : firstMismatch ≤ mpPos := Nat.find_min' hex_raw hne
    have hfm_lt : firstMismatch < TMEncoding.inputPatternWidth k n := by omega
    -- Apply process_nonmatch_entry
    obtain ⟨c₁, steps₁, hbound₁, hreach₁, hst₁, hd₁, hdc₁, hs₁, hsc₁, ho₁, hi₁, hou₁, hwf₁⟩ :=
      process_nonmatch_entry c firstMismatch hfm_lt hstate hwf hinp hinp_h hout hout_h
        hdesc_ns hdesc_h hscratch_ns hscratch_h hother hfm_before hfm_ne
    -- Apply IH to c₁
    have ih_hnonmatch : ∀ j, j < numBefore →
        ∃ mismatchPos, mismatchPos < TMEncoding.inputPatternWidth k n ∧
          (c₁.work utmDescTape).cells
            ((c₁.work utmDescTape).head + j * TMEncoding.entryWidth k n + mismatchPos) ≠
          (c₁.work utmScratchTape).cells (1 + mismatchPos) := by
      intro j hj
      obtain ⟨mp, hmp_lt, hmp_ne⟩ := hnonmatch (j + 1) (by omega)
      refine ⟨mp, hmp_lt, ?_⟩
      rw [hdc₁, hd₁, hsc₁]
      convert hmp_ne using 2
      show (c.work utmDescTape).head + TMEncoding.entryWidth k n +
        j * TMEncoding.entryWidth k n + mp =
        (c.work utmDescTape).head + (j + 1) * TMEncoding.entryWidth k n + mp
      rw [Nat.add_mul]; omega
    have ih_hmatch : ∀ j, j < TMEncoding.inputPatternWidth k n →
        (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + numBefore * TMEncoding.entryWidth k n + j) =
        (c₁.work utmScratchTape).cells (1 + j) := by
      intro j hj
      rw [hdc₁, hd₁, hsc₁]
      convert hmatch_entry j hj using 2
      show (c.work utmDescTape).head + TMEncoding.entryWidth k n +
        numBefore * TMEncoding.entryWidth k n + j =
        (c.work utmDescTape).head + (numBefore + 1) * TMEncoding.entryWidth k n + j
      rw [Nat.add_mul]; omega
    obtain ⟨c', steps', hbound', hreach', hst', hd', hdc', hs', hsc', ho', hi', hou', hwf'⟩ :=
      ih c₁ hst₁ hwf₁
        (by rw [hi₁]; exact hinp) (by rw [hi₁]; exact hinp_h)
        (by rw [hou₁]; exact hout) (by rw [hou₁]; exact hout_h)
        (by intro j hj; rw [hdc₁]; exact hdesc_ns j hj)
        (by rw [hd₁]; omega)
        (by intro j hj; rw [hsc₁]; exact hscratch_ns j hj)
        hs₁
        (by intro i hne_d hne_s; rw [ho₁ i hne_d hne_s]; exact hother i hne_d hne_s)
        ih_hnonmatch ih_hmatch
    refine ⟨c', _, ?_, reachesIn_trans _ hreach₁ hreach', hst', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf'⟩
    · -- step bound: steps₁ + steps' ≤ (numBefore + 1) * (ew + ipw + 4) + ipw
      have h1 := Nat.add_le_add hbound₁ hbound'
      rw [Nat.succ_mul] at *; omega
    · rw [hd', hd₁]; rw [Nat.add_mul]; omega
    · rw [hdc', hdc₁]
    · exact hs'
    · rw [hsc', hsc₁]
    · intro i hne_d hne_s; rw [ho' i hne_d hne_s, ho₁ i hne_d hne_s]
    · rw [hi', hi₁]
    · rw [hou', hou₁]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 7: matchRewind simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind scratch after full match.
    From `matchRewind` with scratch head at position `sh`, after `sh + 2`
    steps reach `matchRewindR` then immediately continue.

    The scratch tape is rewound from position `sh` down to cell 0 (hit ▷),
    then move right to cell 1 in the `matchRewindR` step. -/
private theorem matchRewind_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q) (sh : ℕ)
    (hstate : c.state = .matchRewind)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = sh)
    (hother : ∀ i, i ≠ utmScratchTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (sh + 1) c c' ∧
      c'.state = .matchRewindR ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction sh generalizing c with
  | zero =>
    -- scratch head = 0, so read ▷ at cell 0
    have hread : (c.work utmScratchTape).read = Γ.start := by
      simp [Tape.read, hscratch_h, hwf.1 utmScratchTape]
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    -- Step: matchRewind → matchRewindR (read ▷, move right)
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .matchRewindR ∧
        (c₁.work utmScratchTape).head = 1 ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    refine ⟨c₁, .step hstep' .zero, hst1, hhead1, hcells1, hw1, hinp1, hout1, ?_⟩
    constructor
    · intro i; by_cases h : i = utmScratchTape
      · rw [h, hcells1]; exact hwf.1 utmScratchTape
      · rw [hw1 i h]; exact hwf.1 i
    · intro i j hj; by_cases h : i = utmScratchTape
      · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
      · rw [hw1 i h]; exact hwf.2 i j hj
  | succ sh ih =>
    have hread_ne : (c.work utmScratchTape).read ≠ Γ.start := by
      simp [Tape.read, hscratch_h]; exact hscratch_ns (sh + 1) (by omega)
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .matchRewind ∧
        (c₁.work utmScratchTape).head = sh ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ := ih c₁
      hst1 hwf1
      (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
      (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
      (by intro j hj; rw [hcells1]; exact hscratch_ns j hj)
      hhead1
      (by intro i hne; rw [hw1 i hne]; exact hother i hne)
    refine ⟨c_f, .step hstep' hreach, hst_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 8: matchRewindR step
-- ════════════════════════════════════════════════════════════════════════

/-- From `matchRewindR` with scratch at cell 1, take 1 step to `copyOutput ow`.
    Desc advances past the separator bit. -/
private theorem matchRewindR_step
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (hstate : c.state = .matchRewindR)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    let ow := TMEncoding.outputWidth k n
    ∃ c',
      (lookupTM (n := n) k).reachesIn 1 c c' ∧
      c'.state = .copyOutput ⟨ow, by omega⟩ ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + 1 ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (∀ i, i ≠ utmDescTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro ow
  have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by simp [lookupTM, hstate]
  have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
    lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
  have hscratch_read : (c.work utmScratchTape).read ≠ Γ.start :=
    lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
  -- matchRewindR: desc moves right, scratch and others idle
  have hstep : ∃ c', (lookupTM (n := n) k).step c = some c' ∧
      c'.state = .copyOutput ⟨ow, by omega⟩ ∧
      (c'.work utmDescTape = (c.work utmDescTape).writeAndMove
        (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
      (∀ i, i ≠ utmDescTape → c'.work i = (c.work i).writeAndMove
        (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
      c'.input = c.input.move (idleDir c.input.read) ∧
      c'.output = c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) := by
    simp only [TM.step, hne_halt, ↓reduceIte, lookupTM, hstate]
    refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · show (c.work utmDescTape).writeAndMove (readBackWrite (c.work utmDescTape).read)
          (if utmDescTape = utmDescTape then Dir3.right
           else idleDir (c.work utmDescTape).read) = _
      simp only [↓reduceIte]
    · intro i hne
      show (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (if i = utmDescTape then Dir3.right else idleDir (c.work i).read) = _
      simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
  obtain ⟨c', hstep', hst', hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep
  refine ⟨c', .step hstep' .zero, hst', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- desc head + 1
    rw [hdesc₁, Tape.writeAndMove, Tape.move]
    show (Tape.write _ _).head + 1 = _
    rw [lu_tape_write_head]
  · -- desc cells
    rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
    split
    · rfl
    · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
  · -- other tapes
    intro i hne; rw [hother₁ i hne]
    by_cases hi : i = utmScratchTape
    · subst hi; exact lu_tape_idle_preserve _ hscratch_read hscratch_h
    · exact lu_tape_idle_preserve _ (hother i hne hi).1 (hother i hne hi).2
  · rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  · rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
  · -- WorkTapesWF
    have hdesc_cells : (c'.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    have hother_eq : ∀ i, i ≠ utmDescTape → c'.work i = c.work i := by
      intro i hne; rw [hother₁ i hne]
      by_cases hi : i = utmScratchTape
      · subst hi; exact lu_tape_idle_preserve _ hscratch_read hscratch_h
      · exact lu_tape_idle_preserve _ (hother i hne hi).1 (hother i hne hi).2
    constructor
    · intro i; by_cases hi : i = utmDescTape
      · subst hi; rw [hdesc_cells]; exact hwf.1 _
      · rw [hother_eq i hi]; exact hwf.1 _
    · intro i j hj; by_cases hi : i = utmDescTape
      · subst hi; rw [hdesc_cells]; exact hwf.2 _ j hj
      · rw [hother_eq i hi]; exact hwf.2 _ j hj

-- ════════════════════════════════════════════════════════════════════════
-- Phase 9: copyOutput simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Copy `rem` output bits from desc to scratch.
    From `copyOutput rem`, after `rem + 1` steps reach `rewindDesc`,
    with `rem` bits copied from desc to scratch.

    After copying, scratch contains the transition output bits at cells
    1 through ow, and the head is positioned at ow + 1. The desc tape
    has advanced past all output bits. -/
private theorem copyOutput_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q)
    (rem : ℕ) (hrem : rem ≤ TMEncoding.outputWidth k n)
    (hstate : c.state = .copyOutput ⟨rem, by omega⟩)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = TMEncoding.outputWidth k n - rem + 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    -- The output bits to be copied from desc
    (outputBits : List Bool)
    (houtLen : outputBits.length = TMEncoding.outputWidth k n)
    -- desc stores the remaining output bits starting at its current head
    (hdesc_bits : ∀ (j : ℕ), j < rem →
      ∃ (hj : TMEncoding.outputWidth k n - rem + j < outputBits.length),
      (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
      Γ.ofBool (outputBits[TMEncoding.outputWidth k n - rem + j]'hj))
    -- Already-copied bits on scratch
    (hscratch_bits : ∀ (j : ℕ) (hj : j < outputBits.length),
      j < TMEncoding.outputWidth k n - rem →
      (c.work utmScratchTape).cells (1 + j) = Γ.ofBool (outputBits[j]'hj)) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (rem + 1) c c' ∧
      c'.state = .rewindDesc ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + rem - 1 ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      -- Scratch now has the output bits written
      (∀ (j : ℕ) (hj : j < outputBits.length),
        j < TMEncoding.outputWidth k n →
        (c'.work utmScratchTape).cells (1 + j) = Γ.ofBool (outputBits[j]'hj)) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (c'.work utmScratchTape).head = TMEncoding.outputWidth k n + 1 ∧
      (∀ j, j ≥ TMEncoding.outputWidth k n + 1 →
        (c'.work utmScratchTape).cells j = (c.work utmScratchTape).cells j) ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction rem generalizing c with
  | zero =>
    -- copyOutput 0 → rewindDesc: one step, desc moves left, others idle
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hscratch_read : (c.work utmScratchTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ (by omega) hscratch_ns
    -- Verify the step
    have hstep : ∃ c', (lookupTM (n := n) k).step c = some c' ∧
        c'.state = .rewindDesc ∧
        (c'.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read)
          (moveLeftDir (c.work utmDescTape).read)) ∧
        (∀ i, i ≠ utmDescTape → c'.work i = (c.work i).writeAndMove
          (readBackWrite (c.work i).read) (idleDir (c.work i).read)) ∧
        c'.input = c.input.move (idleDir c.input.read) ∧
        c'.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate]
      refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · show (c.work utmDescTape).writeAndMove (readBackWrite (c.work utmDescTape).read)
            (if utmDescTape = utmDescTape then moveLeftDir (c.work utmDescTape).read
             else idleDir (c.work utmDescTape).read) = _
        simp only [↓reduceIte]
      · intro i hne
        show (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (if i = utmDescTape then moveLeftDir (c.work utmDescTape).read
             else idleDir (c.work i).read) = _
        simp only [show ¬(i = utmDescTape) from hne, ↓reduceIte]
    obtain ⟨c', hstep', hst', hdesc₁, hother₁, hinp₁, hout₁⟩ := hstep
    -- Establish scratch preservation
    have hscratch_eq : c'.work utmScratchTape = c.work utmScratchTape := by
      rw [hother₁ _ (by decide : utmScratchTape ≠ utmDescTape)]
      exact lu_tape_idle_preserve _ hscratch_read (by omega)
    have hmld : moveLeftDir (c.work utmDescTape).read = Dir3.left := by
      simp [moveLeftDir, hdesc_read]
    have hdesc_cells : (c'.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁, Tape.writeAndMove, hmld, Tape.move]
      simp only [Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    refine ⟨c', .step hstep' .zero, hst', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- desc head
      rw [hdesc₁, Tape.writeAndMove, hmld, Tape.move]
      show (Tape.write _ _).head - 1 = _
      rw [lu_tape_write_head]; omega
    · -- desc cells
      exact hdesc_cells
    · -- scratch bits (from hscratch_bits)
      intro j hj hjow
      rw [hscratch_eq]; exact hscratch_bits j hj (by omega)
    · -- scratch cell 0
      rw [hscratch_eq]; exact hwf.1 utmScratchTape
    · -- scratch head
      rw [hscratch_eq, hscratch_h]; omega
    · -- scratch cells beyond ow preserved
      intro j _; rw [hscratch_eq]
    · -- other tapes
      intro i hne_desc hne_scratch
      rw [hother₁ i hne_desc]
      exact lu_tape_idle_preserve _ (hother i hne_desc hne_scratch).1
        (hother i hne_desc hne_scratch).2
    · -- input
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    · -- output
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    · -- WorkTapesWF
      constructor
      · intro i
        by_cases hi1 : i = utmDescTape
        · subst hi1; rw [hdesc_cells]; exact hwf.1 _
        · by_cases hi2 : i = utmScratchTape
          · subst hi2; rw [hscratch_eq]; exact hwf.1 _
          · rw [hother₁ i hi1, lu_tape_idle_preserve _ (hother i hi1 hi2).1
              (hother i hi1 hi2).2]; exact hwf.1 _
      · intro i j hj
        by_cases hi1 : i = utmDescTape
        · subst hi1; rw [hdesc_cells]; exact hwf.2 _ j hj
        · by_cases hi2 : i = utmScratchTape
          · subst hi2; rw [hscratch_eq]; exact hwf.2 _ j hj
          · rw [hother₁ i hi1, lu_tape_idle_preserve _ (hother i hi1 hi2).1
              (hother i hi1 hi2).2]; exact hwf.2 _ j hj
  | succ rem ih =>
    -- copyOutput (rem+1) → copyOutput rem: copy one bit, desc & scratch move right
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hdesc_read : (c.work utmDescTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hdesc_h hdesc_ns
    have hscratch_read : (c.work utmScratchTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ (by omega) hscratch_ns
    -- The value written to scratch
    let w : Γw := match (c.work utmDescTape).read with
      | .zero => .zero | .one => .one | .blank => .blank | .start => .blank
    -- Verify the step
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .copyOutput ⟨rem, by omega⟩ ∧
        (c₁.work utmDescTape = (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read) Dir3.right) ∧
        (c₁.work utmScratchTape = (c.work utmScratchTape).writeAndMove w Dir3.right) ∧
        (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
          c₁.work i = (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)) ∧
        c₁.input = c.input.move (idleDir c.input.read) ∧
        c₁.output = c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) := by
      simp only [TM.step, lookupTM, hstate]
      split_ifs <;> try (first | rfl | contradiction)
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
      · -- desc tape
        simp only [show ¬(utmDescTape = utmScratchTape) from (by decide), ↓reduceIte]
      · -- scratch tape
        simp only [show ¬(utmScratchTape = utmDescTape) from (by decide), ↓reduceIte]
        rfl
      · -- other tapes
        intro i hne_desc hne_scratch
        simp only [show ¬(i = utmScratchTape) from hne_scratch,
          show ¬(i = utmDescTape) from hne_desc, ↓reduceIte]
    obtain ⟨c₁, hstep', hst₁, hdesc₁, hscratch₁, hother₁, hinp₁, hout₁⟩ := hstep
    -- Properties of c₁: desc tape
    have hc₁_desc_h : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      rw [hdesc₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head]
    have hc₁_desc_cells : (c₁.work utmDescTape).cells = (c.work utmDescTape).cells := by
      rw [hdesc₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
      split
      · rfl
      · rw [lu_readBackWrite_toΓ_eq hdesc_read]; exact Function.update_eq_self _ _
    -- Properties of c₁: scratch tape
    have hc₁_scratch_h : (c₁.work utmScratchTape).head =
        TMEncoding.outputWidth k n - rem + 1 := by
      rw [hscratch₁, Tape.writeAndMove, Tape.move]
      show (Tape.write _ _).head + 1 = _
      rw [lu_tape_write_head, hscratch_h]; omega
    have hc₁_scratch_cells_0 : (c₁.work utmScratchTape).cells 0 = Γ.start := by
      rw [hscratch₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      split
      · exact hwf.1 utmScratchTape
      · simp only [Function.update]
        split
        · omega
        · exact hwf.1 utmScratchTape
    -- Properties of c₁: other tapes preserved
    have hc₁_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₁.work i = c.work i := by
      intro i hne_d hne_s; rw [hother₁ i hne_d hne_s]
      exact lu_tape_idle_preserve _ (hother i hne_d hne_s).1 (hother i hne_d hne_s).2
    have hc₁_inp : c₁.input = c.input := by
      rw [hinp₁]; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hc₁_out : c₁.output = c.output := by
      rw [hout₁]; exact lu_tape_idle_preserve _ hout hout_h
    -- w.toΓ ≠ Γ.start
    have hw_ne_start : w.toΓ ≠ Γ.start := by
      show (match (c.work utmDescTape).read with
        | .zero => Γw.zero | .one => Γw.one | .blank => Γw.blank | .start => Γw.blank).toΓ ≠ _
      cases (c.work utmDescTape).read <;> simp [Γw.toΓ]
    -- WorkTapesWF for c₁
    have hc₁_wf : WorkTapesWF c₁.work := by
      constructor
      · intro i
        by_cases hi1 : i = utmDescTape
        · subst hi1; rw [hc₁_desc_cells]; exact hwf.1 _
        · by_cases hi2 : i = utmScratchTape
          · subst hi2; exact hc₁_scratch_cells_0
          · rw [hc₁_other i hi1 hi2]; exact hwf.1 _
      · intro i j hj
        by_cases hi1 : i = utmDescTape
        · subst hi1; rw [hc₁_desc_cells]; exact hwf.2 _ j hj
        · by_cases hi2 : i = utmScratchTape
          · subst hi2
            have : (c₁.work utmScratchTape).cells j ≠ Γ.start := by
              rw [hscratch₁]; simp only [Tape.writeAndMove, Tape.move, Tape.write]
              simp only [show ¬((c.work utmScratchTape).head = 0) from by omega, ↓reduceIte]
              by_cases hjh : j = (c.work utmScratchTape).head
              · rw [Function.update_apply, if_pos hjh]; exact hw_ne_start
              · rw [Function.update_apply, if_neg hjh]; exact hscratch_ns j hj
            exact this
          · rw [hc₁_other i hi1 hi2]; exact hwf.2 _ j hj
    -- Scratch no-start for c₁
    have hc₁_scratch_ns : ∀ j, j ≥ 1 → (c₁.work utmScratchTape).cells j ≠ Γ.start := by
      exact hc₁_wf.2 utmScratchTape
    -- desc bits shifted for IH
    have hc₁_desc_bits : ∀ j, j < rem →
        ∃ (hj : TMEncoding.outputWidth k n - rem + j < outputBits.length),
        (c₁.work utmDescTape).cells ((c₁.work utmDescTape).head + j) =
        Γ.ofBool (outputBits[TMEncoding.outputWidth k n - rem + j]'hj) := by
      intro j hj
      have hdb := hdesc_bits (j + 1) (by omega)
      obtain ⟨hj', hval⟩ := hdb
      have hidx1 : (c.work utmDescTape).head + 1 + j =
          (c.work utmDescTape).head + (j + 1) := by omega
      refine ⟨by omega, ?_⟩
      rw [hc₁_desc_cells, hc₁_desc_h, hidx1]
      have : TMEncoding.outputWidth k n - rem + j =
          TMEncoding.outputWidth k n - (rem + 1) + (j + 1) := by omega
      simp only [this]; exact hval
    -- Already-copied bits for IH: include the bit just copied
    have hc₁_scratch_bits : ∀ (j : ℕ) (hj : j < outputBits.length),
        j < TMEncoding.outputWidth k n - rem →
        (c₁.work utmScratchTape).cells (1 + j) =
        Γ.ofBool (outputBits[j]'hj) := by
      intro j hjlen hjow
      rw [hscratch₁]
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      have hne0 : ¬(TMEncoding.outputWidth k n - (rem + 1) + 1 = 0) := by omega
      simp only [hne0, ↓reduceIte]
      by_cases hjh : 1 + j = TMEncoding.outputWidth k n - (rem + 1) + 1
      · -- j + 1 = head position, so this is the NEW bit
        rw [Function.update_apply, if_pos hjh]
        have hj_eq : j = TMEncoding.outputWidth k n - (rem + 1) := by omega
        subst hj_eq
        -- From hdesc_bits j=0: desc.read = Γ.ofBool outputBits[ow - (rem+1)]
        have hdb0 := hdesc_bits 0 (by omega)
        obtain ⟨_, hval0⟩ := hdb0
        simp only [Nat.add_zero] at hval0
        -- w = match desc.read with ..., desc.read = Γ.ofBool b
        show w.toΓ = _
        show (match (c.work utmDescTape).read with
          | .zero => Γw.zero | .one => Γw.one | .blank => Γw.blank | .start => Γw.blank).toΓ = _
        have : (c.work utmDescTape).read = Γ.ofBool outputBits[TMEncoding.outputWidth k n - (rem + 1)] := hval0
        rw [this]
        cases outputBits[TMEncoding.outputWidth k n - (rem + 1)] <;> simp [Γ.ofBool, Γw.toΓ]
      · -- j ≠ head position, use old scratch bits
        rw [Function.update_apply, if_neg hjh]
        exact hscratch_bits j hjlen (by omega)
    -- Apply IH
    obtain ⟨c', hreach', hst', hhead', hdcells', hbits', hcell0',
            hscratch_head', hscratch_beyond', hother', hinp', hout', hwf'⟩ :=
      ih c₁ (by omega) hst₁ hc₁_wf
        (by rw [hc₁_inp]; exact hinp) (by rw [hc₁_inp]; exact hinp_h)
        (by rw [hc₁_out]; exact hout) (by rw [hc₁_out]; exact hout_h)
        (by intro j hj; rw [hc₁_desc_cells]; exact hdesc_ns j hj)
        (by omega)
        hc₁_scratch_ns
        hc₁_scratch_h
        (by intro i hne_d hne_s; rw [hc₁_other i hne_d hne_s]; exact hother i hne_d hne_s)
        hc₁_desc_bits
        hc₁_scratch_bits
    refine ⟨c', .step hstep' hreach', hst', ?_, ?_, hbits', hcell0',
            hscratch_head', ?_, ?_, ?_, ?_, hwf'⟩
    · -- desc head: (c.head + 1) + rem - 1 = c.head + (rem + 1) - 1
      rw [hhead', hc₁_desc_h]; omega
    · -- desc cells
      rw [hdcells', hc₁_desc_cells]
    · -- scratch cells beyond ow preserved
      intro j hj
      rw [hscratch_beyond' j hj, hscratch₁]
      simp only [Tape.writeAndMove, Tape.move, Tape.write]
      simp only [show ¬((c.work utmScratchTape).head = 0) from by rw [hscratch_h]; omega,
                  ↓reduceIte]
      rw [Function.update_apply, if_neg (by rw [hscratch_h]; omega)]
    · -- other tapes
      intro i hne_d hne_s
      rw [hother' i hne_d hne_s, hc₁_other i hne_d hne_s]
    · -- input
      rw [hinp', hc₁_inp]
    · -- output
      rw [hout', hc₁_out]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 10: rewindDesc simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind the desc tape to cell 1.
    From `rewindDesc` with desc head at position `dh`, after `dh + 2` steps
    reach `rewindDescR` then `rewindScratchFinal`, with desc head = 1.

    The pattern is: move left until hitting ▷ at cell 0 (`dh` steps
    to `rewindDesc`), then 1 step to `rewindDescR` (move right),
    then 1 step to `rewindScratchFinal`. -/
private theorem rewindDesc_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q) (dh : ℕ)
    (hstate : c.state = .rewindDesc)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hdesc_ns : ∀ j, j ≥ 1 → (c.work utmDescTape).cells j ≠ Γ.start)
    (hdesc_h : (c.work utmDescTape).head = dh)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (dh + 2) c c' ∧
      c'.state = .rewindScratchFinal ∧
      (c'.work utmDescTape).head = 1 ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (c'.work utmScratchTape).head = (c.work utmScratchTape).head - 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction dh generalizing c with
  | zero =>
    -- desc head = 0, so read ▷ at cell 0
    have hread : (c.work utmDescTape).read = Γ.start := by
      simp [Tape.read, hdesc_h, hwf.1 utmDescTape]
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hscratch_read : (c.work utmScratchTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
    -- Step 1: rewindDesc → rewindDescR (desc moves right)
    have hstep1 : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindDescR ∧
        (c₁.work utmDescTape).head = 1 ∧
        (c₁.work utmDescTape).cells = (c.work utmDescTape).cells ∧
        (∀ i, i ≠ utmDescTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hdesc_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hdesc_h]
      · intro i hne; dsimp only []; rw [if_neg hne]
        have : (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1 := by
          by_cases hi : i = utmScratchTape
          · subst hi; exact ⟨hscratch_read, hscratch_h⟩
          · exact hother i hne hi
        exact lu_tape_idle_preserve _ this.1 this.2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep1
    -- Prepare for step 2
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmDescTape
        · rw [h, hcells1]; exact hwf.1 utmDescTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmDescTape
        · rw [h, hcells1]; exact hwf.2 utmDescTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    have hinp1' : c₁.input.read ≠ Γ.start := by rw [hinp1]; exact hinp
    have hout1' : c₁.output.read ≠ Γ.start := by rw [hout1]; exact hout
    have hscratch_read1 : (c₁.work utmScratchTape).read ≠ Γ.start := by
      rw [hw1 utmScratchTape (by decide)]; exact hscratch_read
    have hscratch_h1 : (c₁.work utmScratchTape).head ≥ 1 := by
      rw [hw1 utmScratchTape (by decide)]; exact hscratch_h
    have hheads1_desc : (c₁.work utmDescTape).head ≥ 1 := by omega
    -- Step 2: rewindDescR → rewindScratchFinal (desc idle, scratch moves left)
    have hstep2 : ∃ c₂, (lookupTM (n := n) k).step c₁ = some c₂ ∧
        c₂.state = .rewindScratchFinal ∧
        c₂.work utmDescTape = c₁.work utmDescTape ∧
        (c₂.work utmScratchTape).head = (c₁.work utmScratchTape).head - 1 ∧
        (c₂.work utmScratchTape).cells = (c₁.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c₂.work i = c₁.work i) ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output := by
      simp only [TM.step, lookupTM, hst1]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        have : ¬(utmDescTape = utmScratchTape) := by decide
        rw [if_neg this]
        exact lu_tape_idle_preserve _ (lu_tape_read_ne_start_of_wf _
          hheads1_desc (hwf1.2 utmDescTape)) hheads1_desc
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move, moveLeftDir, hscratch_read1, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hscratch_read1]
        simp only [Tape.write]; split
        · omega
        · simp
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move, moveLeftDir, hscratch_read1, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hscratch_read1]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne_d hne_s; dsimp only []
        rw [if_neg hne_s]
        have : (c₁.work i).read ≠ Γ.start ∧ (c₁.work i).head ≥ 1 := by
          rw [hw1 i hne_d]; exact hother i hne_d hne_s
        exact lu_tape_idle_preserve _ this.1 this.2
      · simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve c₁.output hout1' (by rw [hout1]; exact hout_h)
    obtain ⟨c₂, hstep2', hst2, hdesc2, hshead2, hscells2, hw2, hinp2, hout2⟩ := hstep2
    refine ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdesc2]; exact hhead1
    · rw [hdesc2, hcells1]
    · rw [hshead2, hw1 utmScratchTape (by decide)]
    · rw [hscells2, hw1 utmScratchTape (by decide)]
    · intro i hne_d hne_s; rw [hw2 i hne_d hne_s, hw1 i hne_d]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]
    · constructor
      · intro i
        by_cases hi_d : i = utmDescTape
        · rw [hi_d, hdesc2, hcells1]; exact hwf.1 utmDescTape
        · by_cases hi_s : i = utmScratchTape
          · rw [hi_s, hscells2, hw1 utmScratchTape (by decide)]; exact hwf.1 utmScratchTape
          · rw [hw2 i hi_d hi_s, hw1 i hi_d]; exact hwf.1 i
      · intro i j hj
        by_cases hi_d : i = utmDescTape
        · rw [hi_d, hdesc2, hcells1]; exact hwf.2 utmDescTape j hj
        · by_cases hi_s : i = utmScratchTape
          · rw [hi_s, hscells2, hw1 utmScratchTape (by decide)]; exact hwf.2 utmScratchTape j hj
          · rw [hw2 i hi_d hi_s, hw1 i hi_d]; exact hwf.2 i j hj
  | succ dh ih =>
    have hread_ne : (c.work utmDescTape).read ≠ Γ.start := by
      simp [Tape.read, hdesc_h]; exact hdesc_ns (dh + 1) (by omega)
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hscratch_read : (c.work utmScratchTape).read ≠ Γ.start :=
      lu_tape_read_ne_start_of_wf _ hscratch_h hscratch_ns
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindDesc ∧
        (c₁.work utmDescTape).head = dh ∧
        (c₁.work utmDescTape).cells = (c.work utmDescTape).cells ∧
        (∀ i, i ≠ utmDescTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hdesc_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        have : (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1 := by
          by_cases hi : i = utmScratchTape
          · subst hi; exact ⟨hscratch_read, hscratch_h⟩
          · exact hother i hne hi
        exact lu_tape_idle_preserve _ this.1 this.2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmDescTape
        · rw [h, hcells1]; exact hwf.1 utmDescTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmDescTape
        · rw [h, hcells1]; exact hwf.2 utmDescTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hshead_f, hscells_f, hw_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c₁ hst1 hwf1
        (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
        (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
        (by intro j hj; rw [hcells1]; exact hdesc_ns j hj)
        hhead1
        (by intro j hj; rw [hw1 utmScratchTape (by decide)]; exact hscratch_ns j hj)
        (by rw [hw1 utmScratchTape (by decide)]; exact hscratch_h)
        (by intro i hne_d hne_s; rw [hw1 i hne_d]; exact hother i hne_d hne_s)
    refine ⟨c_f, .step hstep' hreach, hst_f, hhead_f, ?_, ?_, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · rw [hshead_f, hw1 utmScratchTape (by decide)]
    · rw [hscells_f, hw1 utmScratchTape (by decide)]
    · intro i hne_d hne_s; rw [hw_f i hne_d hne_s, hw1 i hne_d]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 11: rewindScratchFinal simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Final scratch rewind and halt.
    From `rewindScratchFinal` with scratch head at position `sh`, after
    `sh + 2` steps reach `done` (halted) with scratch head = 1.

    The pattern is: move left until hitting ▷ at cell 0, then
    `rewindScratchFinalR` moves right to cell 1, then transition to `done`. -/
private theorem rewindScratchFinal_loop
    (c : Cfg 4 (lookupTM (n := n) k).Q) (sh : ℕ)
    (hstate : c.state = .rewindScratchFinal)
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    (hscratch_ns : ∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start)
    (hscratch_h : (c.work utmScratchTape).head = sh)
    (hother : ∀ i, i ≠ utmScratchTape → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (sh + 2) c c' ∧
      (lookupTM (n := n) k).halted c' ∧
      c'.state = .done ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  induction sh generalizing c with
  | zero =>
    -- scratch head = 0, so read ▷ at cell 0
    have hread : (c.work utmScratchTape).read = Γ.start := by
      simp [Tape.read, hscratch_h, hwf.1 utmScratchTape]
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    -- Step 1: rewindScratchFinal → rewindScratchFinalR (read ▷, move right)
    have hstep1 : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindScratchFinalR ∧
        (c₁.work utmScratchTape).head = 1 ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write, hscratch_h]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep1
    -- Step 2: rewindScratchFinalR → done (all idle)
    have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
      intro i; by_cases h : i = utmScratchTape
      · rw [h]; omega
      · rw [hw1 i h]; exact (hother i h).2
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    have hinp1' : c₁.input.read ≠ Γ.start := by rw [hinp1]; exact hinp
    have hout1' : c₁.output.read ≠ Γ.start := by rw [hout1]; exact hout
    have hne_halt1 : c₁.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hst1]
    have hstep2 : ∃ c₂, (lookupTM (n := n) k).step c₁ = some c₂ ∧
        c₂.state = .done ∧
        c₂.work = c₁.work ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output := by
      simp only [TM.step, lookupTM, hst1]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · ext i; dsimp only []
        exact lu_tape_idle_preserve (c₁.work i)
          (lu_tape_read_ne_start_of_wf _ (hheads1 i) (hwf1.2 i)) (hheads1 i)
      · simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve c₁.output hout1' (by rw [hout1]; exact hout_h)
    obtain ⟨c₂, hstep2', hst2, hwork2, hinp2, hout2⟩ := hstep2
    refine ⟨c₂, .step hstep1' (.step hstep2' .zero), ?_, hst2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [TM.halted, Cfg.isHalted, hst2, lookupTM]
    · rw [hwork2]; exact hhead1
    · rw [hwork2, hcells1]
    · intro i hne; rw [hwork2, hw1 i hne]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]
    · rw [hwork2]; exact hwf1
  | succ sh ih =>
    have hread_ne : (c.work utmScratchTape).read ≠ Γ.start := by
      simp [Tape.read, hscratch_h]; exact hscratch_ns (sh + 1) (by omega)
    have hne_halt : c.state ≠ (lookupTM (n := n) k).qhalt := by
      simp [lookupTM, hstate]
    have hstep : ∃ c₁, (lookupTM (n := n) k).step c = some c₁ ∧
        c₁.state = .rewindScratchFinal ∧
        (c₁.work utmScratchTape).head = sh ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, ↓reduceIte, lookupTM, hstate, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hscratch_h]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, moveLeftDir, hread_ne, ↓reduceIte]
        rw [lu_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact lu_tape_idle_preserve _ (hother i hne).1 (hother i hne).2
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact lu_tape_idle_preserve _ hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmScratchTape
        · rw [h, hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hhalted, hst_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ := ih c₁
      hst1 hwf1
      (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
      (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
      (by intro j hj; rw [hcells1]; exact hscratch_ns j hj)
      hhead1
      (by intro i hne; rw [hw1 i hne]; exact hother i hne)
    refine ⟨c_f, .step hstep' hreach, hhalted, hst_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

-- ════════════════════════════════════════════════════════════════════════
-- Time bound
-- ════════════════════════════════════════════════════════════════════════

/-- Time bound for the lookup machine.
    Components:
    - skipHeader: tableOffset + 1
    - entry scan: numEntries * (ipw + ew + scratchHead + 4) worst case
    - match: ipw + scratchHead + 2
    - matchRewindR: 1
    - copyOutput: ow + 1
    - rewindDesc: descHead + 2
    - rewindScratchFinal: scratchHead + 2

    For a TM with k states and n work tapes, the total number of entries
    is k * 4 * 4^n * 4 = 16 * k * 4^n. Each entry has width `entryWidth k n`.
    The desc tape head stays bounded by tableOffset + numEntries * entryWidth.
    The scratch tape head stays bounded by inputPatternWidth.

    We give a simplified quadratic bound. -/
noncomputable def lookupTimeBound (k n : ℕ) (descLen : ℕ) : ℕ :=
  let tableOff := TMEncoding.tableOffset k n
  let ew := TMEncoding.entryWidth k n
  let ipw := TMEncoding.inputPatternWidth k n
  let ow := TMEncoding.outputWidth k n
  -- skipHeader phase
  (tableOff + 1) +
  -- worst-case entry scan: at most descLen / ew entries, each costs ew + ipw + 4
  (descLen * (ew + ipw + 4)) +
  -- match phase: compare + matchRewind + matchRewindR
  (ipw + ipw + 3) +
  -- copy output
  (ow + 1) +
  -- rewind desc
  (descLen + 2) +
  -- rewind scratch final
  (ow + 2)

-- ════════════════════════════════════════════════════════════════════════
-- Full HoareTime proof (non-private, exported for Lookup.lean)
-- ════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
theorem lookupTM_hoareTime_proof (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm)
    (simCfg : Cfg n tm.Q) (q : Fin k) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    let e := tm.stateEquivK hk
    ∃ B, (lookupTM (n := n) k).HoareTime
      (fun inp work out =>
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        scratchHasInputPattern k n q iHead wHeads oHead (work utmScratchTape) ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        stateOnTapeAt k q (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1)
      (fun inp work out =>
        let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iHead wHeads oHead
        descOnTape desc (work utmDescTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        WorkTapesWF work ∧
        -- Preserved: state/sim tapes and exact head positions
        stateOnTapeAt k q (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        -- Preserved: inp/out tapes
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1)
      B := by
  intro e
  -- Destructure the transition output for later use
  set δ_result := tm.δ (e.symm q) iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δ_result
  -- Provide the time bound
  refine ⟨lookupTimeBound k n desc.length, ?_⟩
  -- Unfold HoareTime
  intro inp work out hpre
  obtain ⟨hdescOnTape, hdesc_head_eq, hheads, hscratch_inp, hscratchSentinel, hwf,
    hinp_ns, hinp_h, hout_ns, hout_h, hstateOnTape, hsimCorrect, hstate_head_eq,
    hsim_head_eq⟩ := hpre
  -- Build the initial configuration
  set c₀ : Cfg 4 (lookupTM (n := n) k).Q :=
    { state := (lookupTM k).qstart
      input := inp
      work := work
      output := out } with hc₀_def
  -- c₀.state = skipHeader (tableOffset k n)
  have hc₀_state : c₀.state = .skipHeader ⟨TMEncoding.tableOffset k n, by omega⟩ := rfl
  -- Extract tape properties from preconditions
  have hdesc_ns : ∀ j, j ≥ 1 → (c₀.work utmDescTape).cells j ≠ Γ.start :=
    hwf.2 utmDescTape
  have hdesc_h : (c₀.work utmDescTape).head ≥ 1 := hheads utmDescTape
  have hscratch_ns : ∀ j, j ≥ 1 → (c₀.work utmScratchTape).cells j ≠ Γ.start :=
    hwf.2 utmScratchTape
  have hscratch_h : (c₀.work utmScratchTape).head = 1 := hscratch_inp.2
  have hother₀ : ∀ i, i ≠ utmDescTape →
      (c₀.work i).read ≠ Γ.start ∧ (c₀.work i).head ≥ 1 := by
    intro i _
    exact ⟨lu_tape_read_ne_start_of_wf _ (hheads i) (hwf.2 i), hheads i⟩
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 1: skipHeader — advance desc past header to table start
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨c₁, hreach₁, hst₁, hdesc_h₁, hdesc_cells₁, hother₁, hinp₁, hout₁, hwf₁⟩ :=
    skipHeader_loop c₀ (TMEncoding.tableOffset k n) (le_refl _) hc₀_state
      hwf hinp_ns hinp_h hout_ns hout_h hdesc_ns hdesc_h hother₀
  -- After skipHeader, c₁.work utmDescTape.head = 1 + tableOffset k n
  -- and desc cells are unchanged from c₀ (= work)
  have hc₁_desc_h : (c₁.work utmDescTape).head =
      (c₀.work utmDescTape).head + TMEncoding.tableOffset k n :=
    hdesc_h₁
  -- c₁ scratch tape = c₀ scratch tape
  have hc₁_scratch : c₁.work utmScratchTape = c₀.work utmScratchTape :=
    hother₁ utmScratchTape (by decide)
  have hc₁_scratch_h : (c₁.work utmScratchTape).head = 1 := by
    rw [hc₁_scratch]; exact hscratch_h
  have hc₁_scratch_ns : ∀ j, j ≥ 1 → (c₁.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hc₁_scratch]; exact hscratch_ns j hj
  have hc₁_desc_ns : ∀ j, j ≥ 1 → (c₁.work utmDescTape).cells j ≠ Γ.start := by
    intro j hj; rw [hdesc_cells₁]; exact hdesc_ns j hj
  have hc₁_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c₁.work i).read ≠ Γ.start ∧ (c₁.work i).head ≥ 1 := by
    intro i hd hs; rw [hother₁ i hd]; exact hother₀ i hd
  -- ──────────────────────────────────────────────────────────────────
  -- Encoding connection: the desc tape after header skip contains the
  -- transition table entries, and the matching entry for (q, iHead, wHeads, oHead)
  -- is at some position numBefore in the enumeration.
  -- ──────────────────────────────────────────────────────────────────
  -- We need to show:
  -- 1. There exists numBefore such that entries 0..numBefore-1 don't match
  --    the scratch input pattern, and entry numBefore does match.
  -- 2. The output portion of the matching entry encodes the transition output.
  --
  -- This requires reasoning about the structure of encodeTransTable.
  -- We establish these encoding-level facts and prove the phase composition.
  have henc_connection : ∃ numBefore : ℕ,
    numBefore < (allTuples k n).length ∧
    -- Non-matching entries before the match
    (∀ j, j < numBefore →
      ∃ mismatchPos, mismatchPos < TMEncoding.inputPatternWidth k n ∧
        (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + j * TMEncoding.entryWidth k n + mismatchPos) ≠
        (c₁.work utmScratchTape).cells (1 + mismatchPos)) ∧
    -- Matching entry's input pattern matches scratch
    (∀ j, j < TMEncoding.inputPatternWidth k n →
      (c₁.work utmDescTape).cells
        ((c₁.work utmDescTape).head + numBefore * TMEncoding.entryWidth k n + j) =
      (c₁.work utmScratchTape).cells (1 + j)) ∧
    -- The output bits of the matching entry (on desc tape, after the separator)
    -- are exactly encodeTransOutput of the transition output
    (let outputBits := TMEncoding.encodeTransOutput k n (e q') wW oW iD wD oD
     ∀ j, j < outputBits.length →
      ∃ (hj : j < outputBits.length),
      (c₁.work utmDescTape).cells
        ((c₁.work utmDescTape).head +
         numBefore * TMEncoding.entryWidth k n +
         TMEncoding.inputPatternWidth k n + 1 + j) =
      Γ.ofBool (outputBits[j]'hj)) := by
    -- The desc tape stores desc = header ++ transTable, with head at 1 + tableOffset.
    -- The transition table is a flat list of entries in canonical order.
    -- We use List.getElem_of_mem to find the entry for (q, iHead, wHeads, oHead).
    subst hk
    -- After subst, e = tm.stateEquiv, and the transition table uses stateEquiv too.
    -- The desc tape cells at offset = 1 + tableOffset + i correspond to desc[tableOffset + i]
    -- = transTable[i] (via descOnTape and header splitting).
    -- Use allTuples_mem to get membership, then List.getElem_of_mem to get index.
    have hmem := allTuples_mem (Fintype.card tm.Q) n q iHead wHeads oHead
    obtain ⟨numBefore, hnumBefore_lt, hnumBefore_eq⟩ := List.getElem_of_mem hmem
    -- The transition table = allTuples.flatMap entryFn (via encodeTransTable_eq_allTuples_flatMap)
    -- Each entry has width entryWidth (via allTuples_entry_width)
    -- Use flatMap_const_width_getElem to index into the table by entry number
    -- Then connect to tape cells via descOnTape
    -- For now, we provide numBefore and prove the three properties
    refine ⟨numBefore, hnumBefore_lt, ?_, ?_, ?_⟩
    · -- Non-matching entries before numBefore
      intro j_entry hj_entry
      let k := Fintype.card tm.Q
      let ew := TMEncoding.entryWidth k n
      let ipw := TMEncoding.inputPatternWidth k n
      have hj_lt : j_entry < (allTuples k n).length := by simp only [k]; omega
      -- Different index → different tuple (via nodup)
      have htuple_ne : (allTuples k n)[j_entry] ≠ (q, iHead, wHeads, oHead) := by
        rw [← hnumBefore_eq]; intro heq
        exact absurd ((allTuples_nodup k n).getElem_inj_iff.mp heq) (by omega)
      -- Destructure j_entry-th tuple
      set tup_j := (allTuples k n)[j_entry] with htup_j_eq
      obtain ⟨q_j, iH_j, wH_j, oH_j⟩ := tup_j
      -- Pattern not equal (contrapositive of encodeInputPattern_injective)
      have hpat_ne : TMEncoding.encodeInputPattern k n q_j iH_j wH_j oH_j ≠
          TMEncoding.encodeInputPattern k n q iHead wHeads oHead := by
        intro heq
        exact htuple_ne (by
          obtain ⟨h1, h2, h3, h4⟩ := encodeInputPattern_injective heq; rw [h1, h2, h3, h4])
      -- By contradiction: if all positions match, patterns are equal
      by_contra hmatch_all; push_neg at hmatch_all
      apply hpat_ne
      apply List.ext_getElem (by rw [encodeInputPattern_length, encodeInputPattern_length])
      intro j_pos hj₁ hj₂
      have hj_ipw : j_pos < ipw := by rw [encodeInputPattern_length] at hj₁; exact hj₁
      have h_eq := hmatch_all j_pos hj_ipw
      have hj_ew : j_pos < ew := by
        simp only [ew, TMEncoding.entryWidth, ipw, TMEncoding.inputPatternWidth] at hj_ipw ⊢; omega
      have htable_eq := encodeTransTable_eq_allTuples_flatMap tm tm.stateEquiv
      have hentry_width := allTuples_entryFn_width tm tm.stateEquiv
      have hbound : j_entry * ew + j_pos < (TMEncoding.encodeTransTable tm tm.stateEquiv).length := by
        rw [htable_eq, flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt j_entry j_pos _ _ hj_lt hj_ew
      -- LHS: desc tape cell = Γ.ofBool(transTable[j_entry * ew + j_pos])
      have h_lhs : (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + j_entry * ew + j_pos) =
          Γ.ofBool ((TMEncoding.encodeTransTable tm tm.stateEquiv)[j_entry * ew + j_pos]'hbound) := by
        rw [hdesc_cells₁, hc₁_desc_h, hdesc_head_eq]
        convert desc_cell_eq_table_bit tm desc (work utmDescTape) hdesc hdescOnTape
          (j_entry * ew + j_pos) hbound using 2
        omega
      -- RHS: scratch tape cell = Γ.ofBool(pattern_match[j_pos])
      have h_rhs : (c₁.work utmScratchTape).cells (1 + j_pos) =
          Γ.ofBool ((TMEncoding.encodeInputPattern k n q iHead wHeads oHead)[j_pos]'hj₂) := by
        rw [hc₁_scratch, show 1 + j_pos = j_pos + 1 by omega]
        exact hscratch_inp.1.2.1 j_pos hj₂
      -- Middle: transTable bit = pattern_j bit
      have hbound_fm : j_entry * ew + j_pos <
          ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv)).length := by
        rw [flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt j_entry j_pos _ _ hj_lt hj_ew
      have h_fm_idx := flatMap_const_width_getElem
        (allTuples k n) (allTuples_entryFn tm tm.stateEquiv) ew
        (fun a ha => hentry_width a ha) j_entry j_pos hj_lt hj_ew
      have hentry_j_bound : j_pos <
          (allTuples_entryFn tm tm.stateEquiv (q_j, iH_j, wH_j, oH_j)).length := by
        rw [hentry_width _ (htup_j_eq ▸ List.getElem_mem hj_lt)]; exact hj_ew
      have h_entry_bit :
          (allTuples_entryFn tm tm.stateEquiv (q_j, iH_j, wH_j, oH_j))[j_pos]'hentry_j_bound =
          (TMEncoding.encodeInputPattern k n q_j iH_j wH_j oH_j)[j_pos]'hj₁ := by
        unfold allTuples_entryFn
        simp only [encodeEntry_eq]
        exact encodeEntry_input_prefix k n q_j iH_j wH_j oH_j _ _ _ _ _ _ j_pos hj_ipw
      have h_entry_at : (allTuples_entryFn tm tm.stateEquiv (allTuples k n)[j_entry]) =
          (allTuples_entryFn tm tm.stateEquiv (q_j, iH_j, wH_j, oH_j)) := by
        rw [htup_j_eq]
      have h_mid : (TMEncoding.encodeTransTable tm tm.stateEquiv)[j_entry * ew + j_pos]'hbound =
          (TMEncoding.encodeInputPattern k n q_j iH_j wH_j oH_j)[j_pos]'hj₁ := by
        have : (TMEncoding.encodeTransTable tm tm.stateEquiv)[j_entry * ew + j_pos]'hbound =
            ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv))[j_entry * ew + j_pos]'hbound_fm := by
          congr 1
        rw [this, h_fm_idx]; simp only [h_entry_at, h_entry_bit]
      -- Combine: Γ.ofBool(pattern_j[j_pos]) = Γ.ofBool(pattern_match[j_pos]) → bits equal
      exact Γ_ofBool_injective (by rw [← congrArg Γ.ofBool h_mid, ← h_lhs, h_eq, h_rhs])
    · -- Matching entry's input pattern matches scratch
      intro j hj_ipw
      let k := Fintype.card tm.Q
      let ew := TMEncoding.entryWidth k n
      have hj_ew : j < ew := by
        simp only [ew, TMEncoding.entryWidth, TMEncoding.inputPatternWidth] at hj_ipw ⊢; omega
      have htable_eq := encodeTransTable_eq_allTuples_flatMap tm tm.stateEquiv
      have hentry_width := allTuples_entryFn_width tm tm.stateEquiv
      have hbound : numBefore * ew + j < (TMEncoding.encodeTransTable tm tm.stateEquiv).length := by
        rw [htable_eq, flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt numBefore j _ _ hnumBefore_lt hj_ew
      -- LHS: desc tape cell = Γ.ofBool (transTable bit)
      have h_lhs : (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + numBefore * ew + j) =
          Γ.ofBool ((TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + j]'hbound) := by
        rw [hdesc_cells₁, hc₁_desc_h, hdesc_head_eq]
        convert desc_cell_eq_table_bit tm desc (work utmDescTape) hdesc hdescOnTape
          (numBefore * ew + j) hbound using 2
        omega
      -- RHS: scratch tape cell = Γ.ofBool (inputPattern bit)
      have h_ipw_bound : j < (TMEncoding.encodeInputPattern k n q iHead wHeads oHead).length := by
        rw [encodeInputPattern_length]; exact hj_ipw
      have h_rhs : (c₁.work utmScratchTape).cells (1 + j) =
          Γ.ofBool ((TMEncoding.encodeInputPattern k n q iHead wHeads oHead)[j]'h_ipw_bound) := by
        rw [hc₁_scratch, show 1 + j = j + 1 by omega]
        exact hscratch_inp.1.2.1 j h_ipw_bound
      -- Middle: transTable bit = inputPattern bit (via entryFn and encodeEntry_input_prefix)
      -- Use a helper that goes through entryFn directly on the concrete tuple
      have hentry_j_bound : j < (allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead)).length := by
        rw [hentry_width _ hmem]; exact hj_ew
      have h_entry_bit :
          (allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead))[j]'hentry_j_bound =
          (TMEncoding.encodeInputPattern k n q iHead wHeads oHead)[j]'h_ipw_bound := by
        unfold allTuples_entryFn
        -- After unfolding, the match on the tuple is reduced but the match on tm.δ
        -- leaves projections. The encodeEntry_eq rewrite splits encodeEntry into
        -- inputPattern ++ [false] ++ output. Then encodeEntry_input_prefix
        -- extracts the j-th bit from the input pattern prefix.
        -- The output part doesn't matter for this index, so we use convert.
        simp only [encodeEntry_eq]
        exact encodeEntry_input_prefix k n q iHead wHeads oHead _ _ _ _ _ _  j hj_ipw
      -- Connect transTable to entryFn via flatMap_const_width_getElem
      have hbound_fm : numBefore * ew + j <
          ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv)).length := by
        rw [flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt numBefore j _ _ hnumBefore_lt hj_ew
      have h_fm_idx := flatMap_const_width_getElem
        (allTuples k n)
        (allTuples_entryFn tm tm.stateEquiv) ew
        (fun a ha => hentry_width a ha) numBefore j hnumBefore_lt hj_ew
      -- h_fm_idx : (allTuples.flatMap entryFn)[numBefore * ew + j] = (entryFn allTuples[numBefore])[j]
      -- We need: transTable[numBefore * ew + j] = inputPattern[j]
      -- Go: transTable = allTuples.flatMap entryFn (htable_eq)
      --     (flatMap entryFn)[...] = (entryFn allTuples[numBefore])[j] (h_fm_idx)
      --     allTuples[numBefore] = (q, iH, wH, oH) (hnumBefore_eq) — handled via congrArg
      --     (entryFn (q,...,oH))[j] = inputPattern[j] (h_entry_bit)
      have h_entry_at : (allTuples_entryFn tm tm.stateEquiv (allTuples k n)[numBefore]) =
          (allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead)) := by
        rw [hnumBefore_eq]
      have h_mid : (TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + j]'hbound =
          (TMEncoding.encodeInputPattern k n q iHead wHeads oHead)[j]'h_ipw_bound := by
        have : (TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + j]'hbound =
            ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv))[numBefore * ew + j]'hbound_fm := by
          congr 1
        rw [this, h_fm_idx]
        simp only [h_entry_at, h_entry_bit]
      rw [h_lhs, h_rhs, congrArg Γ.ofBool h_mid]
    · -- Output bits match
      -- The goal starts with `let outputBits := ...; ∀ j < ..., ...`
      intro outputBits j hj_out
      refine ⟨hj_out, ?_⟩
      let k := Fintype.card tm.Q
      let ew := TMEncoding.entryWidth k n
      let ipw := TMEncoding.inputPatternWidth k n
      -- Position within the entry: ipw + 1 + j
      have hout_len : outputBits.length = TMEncoding.outputWidth k n :=
        encodeTransOutput_length k n (e q') wW oW iD wD oD
      have hpos_ew : ipw + 1 + j < ew := by
        simp only [ew, TMEncoding.entryWidth, ipw]; rw [← hout_len]; omega
      have htable_eq := encodeTransTable_eq_allTuples_flatMap tm tm.stateEquiv
      have hentry_width := allTuples_entryFn_width tm tm.stateEquiv
      have hbound : numBefore * ew + (ipw + 1 + j) <
          (TMEncoding.encodeTransTable tm tm.stateEquiv).length := by
        rw [htable_eq, flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt numBefore (ipw + 1 + j) _ _ hnumBefore_lt hpos_ew
      -- LHS: desc tape cell → transition table bit
      have h_lhs : (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + numBefore * ew + ipw + 1 + j) =
          Γ.ofBool ((TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + (ipw + 1 + j)]'hbound) := by
        rw [hdesc_cells₁, hc₁_desc_h, hdesc_head_eq]
        convert desc_cell_eq_table_bit tm desc (work utmDescTape) hdesc hdescOnTape
          (numBefore * ew + (ipw + 1 + j)) hbound using 2
        omega
      -- Bound for the entry at the matching position
      have hbound_fm : numBefore * ew + (ipw + 1 + j) <
          ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv)).length := by
        rw [flatMap_const_width_length _ _ _ (fun a ha => hentry_width a ha)]
        exact mul_add_lt_mul_of_lt numBefore _ _ _ hnumBefore_lt hpos_ew
      have hentry_j_bound : ipw + 1 + j <
          (allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead)).length := by
        rw [hentry_width _ hmem]; exact hpos_ew
      -- Middle: transTable bit at (numBefore * ew + ipw + 1 + j) = outputBits[j]
      have h_entry_at : (allTuples_entryFn tm tm.stateEquiv (allTuples k n)[numBefore]) =
          (allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead)) := by
        rw [hnumBefore_eq]
      -- entryFn (q,iHead,wHeads,oHead) at position (ipw + 1 + j) = outputBits[j]
      -- We need a helper lemma about allTuples_entryFn output bits
      -- The entryFn at (q,iH,wH,oH) = encodeEntry k n q iH wH oH (e q'') wW' oW' iD' wD' oD'
      --   where (q'',wW',oW',iD',wD',oD') = tm.δ (e.symm q) iH wH oH
      -- After encodeEntry_eq, this = inputPattern ++ [false] ++ transOutput
      -- So at position ipw + 1 + j, we get transOutput[j] = outputBits[j]
      -- Use encodeEntry_output_getElem
      have h_entry_list_eq : allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead) =
          TMEncoding.encodeEntry k n q iHead wHeads oHead
            (tm.stateEquiv (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).1)
            (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).2.1
            (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).2.2.1
            (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).2.2.2.1
            (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).2.2.2.2.1
            (tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead).2.2.2.2.2 := by
        unfold allTuples_entryFn; rfl
      have h_entry_list_eq2 : allTuples_entryFn tm tm.stateEquiv (q, iHead, wHeads, oHead) =
          TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false] ++ outputBits := by
        rw [h_entry_list_eq, encodeEntry_eq]
        congr 1
        -- Need: the encodeTransOutput with tm.δ projections = outputBits
        -- outputBits = encodeTransOutput k n (e q') wW oW iD wD oD
        -- and (q', wW, oW, iD, wD, oD) = tm.δ (e.symm q) iHead wHeads oHead
        -- so the projections of tm.δ are exactly (q', wW, oW, iD, wD, oD)
        -- and tm.stateEquiv = e, so e q' = the first component of the output
        generalize hres : tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead = res
        obtain ⟨rq, rwW, roW, riD, rwD, roD⟩ := res
        have : (q', wW, oW, iD, wD, oD) = (rq, rwW, roW, riD, rwD, roD) := by
          rw [hδ_def]; exact hres
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := this
        rfl
      have h_ipw_len : (TMEncoding.encodeInputPattern k n q iHead wHeads oHead).length = ipw :=
        encodeInputPattern_length k n q iHead wHeads oHead
      have h_list_rw : allTuples_entryFn tm tm.stateEquiv (allTuples k n)[numBefore] =
          TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false] ++ outputBits :=
        h_entry_at ▸ h_entry_list_eq2
      have happ_bound : ipw + 1 + j <
          (TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false] ++ outputBits).length := by
        rw [List.length_append, List.length_append, h_ipw_len,
            List.length_cons, List.length_nil]; omega
      have hlen1 : (TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false]).length = ipw + 1 := by
        rw [List.length_append, h_ipw_len, List.length_cons, List.length_nil]
      have h_app_idx : (TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false] ++ outputBits)[ipw + 1 + j]'happ_bound =
          outputBits[j]'hj_out := by
        rw [List.getElem_append_right (by rw [hlen1]; omega)]
        congr 1; rw [hlen1]; omega
      have h_mid : (TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + (ipw + 1 + j)]'hbound =
          outputBits[j]'hj_out := by
        have h1 : (TMEncoding.encodeTransTable tm tm.stateEquiv)[numBefore * ew + (ipw + 1 + j)]'hbound =
            ((allTuples k n).flatMap (allTuples_entryFn tm tm.stateEquiv))[numBefore * ew + (ipw + 1 + j)]'hbound_fm := by
          congr 1
        rw [h1, flatMap_const_width_getElem _ _ _ (fun a ha => hentry_width a ha) numBefore _ hnumBefore_lt hpos_ew]
        have hbound_entry : ipw + 1 + j < (allTuples_entryFn tm tm.stateEquiv (allTuples k n)[numBefore]).length := by
          rw [h_entry_at]; exact hentry_j_bound
        calc (allTuples_entryFn tm tm.stateEquiv (allTuples k n)[numBefore])[ipw + 1 + j]'hbound_entry =
              (TMEncoding.encodeInputPattern k n q iHead wHeads oHead ++ [false] ++ outputBits)[ipw + 1 + j]'happ_bound := by
                congr 1
            _ = outputBits[j] := h_app_idx
      convert h_lhs.trans (congrArg Γ.ofBool h_mid) using 2
  obtain ⟨numBefore, hnumBefore_lt, hnonmatch, hmatch_entry, houtput_bits⟩ := henc_connection
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 2: entry_scan_to_match — scan entries until match found
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨c₂, steps₂, hsteps₂_bound, hreach₂, hst₂, hdesc_h₂, hdesc_cells₂,
          hscratch_h₂, hscratch_cells₂, hother₂, hinp₂, hout₂, hwf₂⟩ :=
    entry_scan_to_match c₁ numBefore hst₁ hwf₁
      (by rw [hinp₁]; exact hinp_ns) (by rw [hinp₁]; exact hinp_h)
      (by rw [hout₁]; exact hout_ns) (by rw [hout₁]; exact hout_h)
      hc₁_desc_ns (by omega) hc₁_scratch_ns hc₁_scratch_h hc₁_other
      hnonmatch hmatch_entry
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 3: matchRewind — rewind scratch after match
  -- ──────────────────────────────────────────────────────────────────
  have hc₂_scratch_ns : ∀ j, j ≥ 1 → (c₂.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hscratch_cells₂, hc₁_scratch]; exact hscratch_ns j hj
  have hc₂_other_scratch : ∀ i, i ≠ utmScratchTape →
      (c₂.work i).read ≠ Γ.start ∧ (c₂.work i).head ≥ 1 := by
    intro i hne
    by_cases hd : i = utmDescTape
    · subst hd
      exact ⟨lu_tape_read_ne_start_of_wf _ (by omega) (hwf₂.2 utmDescTape),
             by omega⟩
    · rw [hother₂ i hd hne]; exact hc₁_other i hd hne
  obtain ⟨c₃, hreach₃, hst₃, hscratch_h₃, hscratch_cells₃, hother₃, hinp₃, hout₃, hwf₃⟩ :=
    matchRewind_loop c₂ (TMEncoding.inputPatternWidth k n) hst₂ hwf₂
      (by rw [hinp₂, hinp₁]; exact hinp_ns) (by rw [hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₂, hout₁]; exact hout_ns) (by rw [hout₂, hout₁]; exact hout_h)
      hc₂_scratch_ns hscratch_h₂ hc₂_other_scratch
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 4: matchRewindR — advance desc past separator
  -- ──────────────────────────────────────────────────────────────────
  have hc₃_desc : c₃.work utmDescTape = c₂.work utmDescTape :=
    hother₃ utmDescTape (by decide)
  have hc₃_desc_ns : ∀ j, j ≥ 1 → (c₃.work utmDescTape).cells j ≠ Γ.start := by
    intro j hj; rw [hc₃_desc]; exact hwf₂.2 utmDescTape j hj
  have hc₃_desc_h : (c₃.work utmDescTape).head ≥ 1 := by
    rw [hc₃_desc, hdesc_h₂]; omega
  have hc₃_scratch_ns : ∀ j, j ≥ 1 → (c₃.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hscratch_cells₃]; exact hc₂_scratch_ns j hj
  have hc₃_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c₃.work i).read ≠ Γ.start ∧ (c₃.work i).head ≥ 1 := by
    intro i hd hs
    have hne_s : i ≠ utmScratchTape := hs
    rw [hother₃ i (by intro h; subst h; exact hs (by decide))]
    exact hc₂_other_scratch i hne_s
  obtain ⟨c₄, hreach₄, hst₄, hdesc_h₄, hdesc_cells₄, hother₄, hinp₄, hout₄, hwf₄⟩ :=
    matchRewindR_step c₃ hst₃ hwf₃
      (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_ns)
      (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₃, hout₂, hout₁]; exact hout_ns)
      (by rw [hout₃, hout₂, hout₁]; exact hout_h)
      hc₃_desc_ns hc₃_desc_h
      (by intro j hj; rw [hscratch_cells₃]; exact hc₂_scratch_ns j hj)
      (by omega) hc₃_other
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 5: copyOutput — copy output bits from desc to scratch
  -- ──────────────────────────────────────────────────────────────────
  -- After matchRewindR: desc advanced by 1 past separator, now at output bits
  -- c₄.work utmDescTape.head = c₃.work utmDescTape.head + 1
  --                           = c₂.work utmDescTape.head + 1
  --                           = (c₁.head + numBefore * ew + ipw) + 1
  -- which is exactly at the output bits position
  set outputBits := TMEncoding.encodeTransOutput k n (e q') wW oW iD wD oD with houtputBits_def
  have houtLen : outputBits.length = TMEncoding.outputWidth k n :=
    encodeTransOutput_length k n (e q') wW oW iD wD oD
  -- c₄ scratch tape preserved from c₃
  have hc₄_scratch : c₄.work utmScratchTape = c₃.work utmScratchTape :=
    hother₄ utmScratchTape (by decide)
  have hc₄_scratch_h : (c₄.work utmScratchTape).head = 1 := by
    rw [hc₄_scratch]; exact hscratch_h₃
  -- The desc bits at c₄ correspond to the output bits
  have hc₄_desc_bits : ∀ (j : ℕ), j < TMEncoding.outputWidth k n →
      ∃ (hj : TMEncoding.outputWidth k n - TMEncoding.outputWidth k n + j < outputBits.length),
      (c₄.work utmDescTape).cells ((c₄.work utmDescTape).head + j) =
      Γ.ofBool (outputBits[TMEncoding.outputWidth k n - TMEncoding.outputWidth k n + j]'hj) := by
    intro j hj
    have hj' : j < outputBits.length := by rw [houtLen]; exact hj
    refine ⟨by omega, ?_⟩
    simp only [Nat.sub_self, Nat.zero_add]
    have hobits := houtput_bits j hj'
    obtain ⟨_, hval⟩ := hobits
    have : (c₄.work utmDescTape).cells ((c₄.work utmDescTape).head + j) =
        (c₁.work utmDescTape).cells
          ((c₁.work utmDescTape).head + numBefore * TMEncoding.entryWidth k n +
           TMEncoding.inputPatternWidth k n + 1 + j) := by
      rw [hdesc_cells₄, hc₃_desc, hdesc_cells₂]
      congr 1
      rw [hdesc_h₄, hc₃_desc, hdesc_h₂]
    rw [this]; exact hval
  -- Scratch head at ow - ow + 1 = 1
  have hc₄_scratch_h' : (c₄.work utmScratchTape).head =
      TMEncoding.outputWidth k n - TMEncoding.outputWidth k n + 1 := by
    rw [hc₄_scratch_h]; omega
  have hc₄_scratch_ns : ∀ j, j ≥ 1 → (c₄.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hc₄_scratch, hscratch_cells₃]; exact hc₂_scratch_ns j hj
  have hc₄_desc_ns : ∀ j, j ≥ 1 → (c₄.work utmDescTape).cells j ≠ Γ.start := by
    intro j hj; rw [hdesc_cells₄]; exact hc₃_desc_ns j hj
  have hc₄_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c₄.work i).read ≠ Γ.start ∧ (c₄.work i).head ≥ 1 := by
    intro i hd hs; rw [hother₄ i hd]; exact hc₃_other i hd hs
  -- No previously copied bits (rem = ow, so ow - rem = 0)
  have hc₄_scratch_bits_prev : ∀ (j : ℕ) (hj : j < outputBits.length),
      j < TMEncoding.outputWidth k n - TMEncoding.outputWidth k n →
      (c₄.work utmScratchTape).cells (1 + j) =
      Γ.ofBool (outputBits[j]'hj) := by
    intro j _ hj; omega
  obtain ⟨c₅, hreach₅, hst₅, hdesc_h₅, hdesc_cells₅, hbits₅, hcell0₅,
          hscratch_h₅, hscratch_beyond₅, hother₅, hinp₅, hout₅, hwf₅⟩ :=
    copyOutput_loop c₄ (TMEncoding.outputWidth k n) (le_refl _)
      (by exact hst₄)
      hwf₄
      (by rw [hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_ns)
      (by rw [hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₄, hout₃, hout₂, hout₁]; exact hout_ns)
      (by rw [hout₄, hout₃, hout₂, hout₁]; exact hout_h)
      hc₄_desc_ns (by rw [hdesc_h₄]; omega)
      hc₄_scratch_ns hc₄_scratch_h'
      hc₄_other outputBits houtLen hc₄_desc_bits hc₄_scratch_bits_prev
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 6: rewindDesc — rewind desc tape to cell 1
  -- ──────────────────────────────────────────────────────────────────
  -- c₅ is in state rewindDesc
  -- We need the desc head position for rewindDesc_loop
  -- After copyOutput, desc head = c₄.desc.head + ow - 1
  have hc₅_desc_ns : ∀ j, j ≥ 1 → (c₅.work utmDescTape).cells j ≠ Γ.start := hwf₅.2 utmDescTape
  have hc₅_scratch_ns : ∀ j, j ≥ 1 → (c₅.work utmScratchTape).cells j ≠ Γ.start := hwf₅.2 utmScratchTape
  have hc₅_other : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c₅.work i).read ≠ Γ.start ∧ (c₅.work i).head ≥ 1 := by
    intro i hd hs; rw [hother₅ i hd hs]; exact hc₄_other i hd hs
  -- Need scratch head for rewindDesc_loop
  -- copyOutput ends with scratch head ≥ 1 (from WorkTapesWF)
  -- Actually need to compute it. After copyOutput with rem=ow, scratch head ends at ow + 1
  -- The rewindDesc_loop wants scratch head ≥ 1, which is fine.
  obtain ⟨c₆, hreach₆, hst₆, hdesc_h₆, hdesc_cells₆,
          hscratch_h₆, hscratch_cells₆, hother₆, hinp₆, hout₆, hwf₆⟩ :=
    rewindDesc_loop c₅ ((c₅.work utmDescTape).head) hst₅ hwf₅
      (by rw [hinp₅, hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_ns)
      (by rw [hinp₅, hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout_ns)
      (by rw [hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout_h)
      hc₅_desc_ns rfl hc₅_scratch_ns
      (by rw [hscratch_h₅]; omega)
      hc₅_other
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 7: rewindScratchFinal — rewind scratch and halt
  -- ──────────────────────────────────────────────────────────────────
  have hc₆_scratch_ns : ∀ j, j ≥ 1 → (c₆.work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hscratch_cells₆]; exact hc₅_scratch_ns j hj
  have hc₆_other_scratch : ∀ i, i ≠ utmScratchTape →
      (c₆.work i).read ≠ Γ.start ∧ (c₆.work i).head ≥ 1 := by
    intro i hne
    by_cases hd : i = utmDescTape
    · subst hd
      refine ⟨lu_tape_read_ne_start_of_wf _ (by omega) (hwf₆.2 utmDescTape), by omega⟩
    · rw [hother₆ i hd hne]; exact hc₅_other i hd hne
  obtain ⟨c₇, hreach₇, hhalted₇, hst₇, hscratch_h₇, hscratch_cells₇,
          hother₇, hinp₇, hout₇, hwf₇⟩ :=
    rewindScratchFinal_loop c₆ ((c₆.work utmScratchTape).head) hst₆ hwf₆
      (by rw [hinp₆, hinp₅, hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_ns)
      (by rw [hinp₆, hinp₅, hinp₄, hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout_ns)
      (by rw [hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]; exact hout_h)
      hc₆_scratch_ns rfl hc₆_other_scratch
  -- ──────────────────────────────────────────────────────────────────
  -- Assemble the final result
  -- ──────────────────────────────────────────────────────────────────
  -- Chain all the reachesIn steps
  have htotal := reachesIn_trans _ hreach₁
    (reachesIn_trans _ hreach₂
    (reachesIn_trans _ hreach₃
    (reachesIn_trans _ hreach₄
    (reachesIn_trans _ hreach₅
    (reachesIn_trans _ hreach₆ hreach₇)))))
  refine ⟨c₇, _, ?_, htotal, hhalted₇, ?_⟩
  · -- Time bound
    subst hk
    -- Compute intermediate head positions
    have hc₆_sh : (c₆.work utmScratchTape).head = TMEncoding.outputWidth (Fintype.card tm.Q) n := by
      rw [hscratch_h₆, hscratch_h₅]; omega
    have hew_eq : TMEncoding.entryWidth (Fintype.card tm.Q) n =
        TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 1 +
        TMEncoding.outputWidth (Fintype.card tm.Q) n := by
      simp [TMEncoding.entryWidth]
    have hc₅_dh : (c₅.work utmDescTape).head =
        TMEncoding.tableOffset (Fintype.card tm.Q) n +
        (numBefore + 1) * TMEncoding.entryWidth (Fintype.card tm.Q) n := by
      rw [hdesc_h₅, hdesc_h₄, hc₃_desc, hdesc_h₂, hc₁_desc_h, hdesc_head_eq]
      rw [Nat.succ_mul, hew_eq]; omega
    -- desc.length decomposition
    have hDescLen : desc.length = TMEncoding.tableOffset (Fintype.card tm.Q) n +
        (allTuples (Fintype.card tm.Q) n).length *
        TMEncoding.entryWidth (Fintype.card tm.Q) n := by
      rw [hdesc, encodeTM_eq_header_append_table, List.length_append,
          encodeTM_header_length tm rfl,
          encodeTransTable_eq_allTuples_flatMap tm tm.stateEquiv,
          flatMap_const_width_length _ _ _ (fun a ha =>
            allTuples_entryFn_width tm tm.stateEquiv a ha)]
    -- Key bounds
    have hc₅_le : (c₅.work utmDescTape).head ≤ desc.length := by
      rw [hc₅_dh, hDescLen]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hnumBefore_lt) _
    have hDescGe : desc.length ≥ (allTuples (Fintype.card tm.Q) n).length := by
      rw [hDescLen]
      calc (allTuples (Fintype.card tm.Q) n).length
          ≤ (allTuples (Fintype.card tm.Q) n).length *
            TMEncoding.entryWidth (Fintype.card tm.Q) n :=
              Nat.le_mul_of_pos_right _ (by simp [TMEncoding.entryWidth]; omega)
        _ ≤ _ := Nat.le_add_left _ _
    have hstep_le : steps₂ ≤ desc.length *
        (TMEncoding.entryWidth (Fintype.card tm.Q) n +
         TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 4) := by
      calc steps₂
          ≤ numBefore * (TMEncoding.entryWidth (Fintype.card tm.Q) n +
              TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 4) +
            TMEncoding.inputPatternWidth (Fintype.card tm.Q) n := hsteps₂_bound
        _ ≤ (numBefore + 1) * (TMEncoding.entryWidth (Fintype.card tm.Q) n +
              TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 4) := by
            rw [Nat.succ_mul]; omega
        _ ≤ (allTuples (Fintype.card tm.Q) n).length *
              (TMEncoding.entryWidth (Fintype.card tm.Q) n +
               TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 4) :=
            Nat.mul_le_mul_right _ hnumBefore_lt
        _ ≤ desc.length * (TMEncoding.entryWidth (Fintype.card tm.Q) n +
              TMEncoding.inputPatternWidth (Fintype.card tm.Q) n + 4) :=
            Nat.mul_le_mul_right _ hDescGe
    -- Combine: use hstep_le and hc₅_le to reduce to linear arithmetic
    -- After rw, LHS has steps₂ and (numBefore+1)*ew; RHS has desc.length*(ew+ipw+4) and desc.length
    -- omega handles cancellation since steps₂ ≤ desc.length*(ew+ipw+4) and
    -- tableOff + (numBefore+1)*ew ≤ desc.length are both in context
    have hc₅_le' : TMEncoding.tableOffset (Fintype.card tm.Q) n +
        (numBefore + 1) * TMEncoding.entryWidth (Fintype.card tm.Q) n ≤ desc.length := by
      rw [← hc₅_dh]; exact hc₅_le
    simp only [lookupTimeBound]
    rw [hc₅_dh, hc₆_sh]
    omega
  · -- Postcondition
    dsimp only []
    -- Trace tapes back to work
    have hc₇_desc : c₇.work utmDescTape = c₆.work utmDescTape :=
      hother₇ utmDescTape (by decide)
    -- descOnTape: desc tape cells unchanged throughout
    have hfinal_descOnTape : descOnTape desc (c₇.work utmDescTape) := by
      have hcells : (c₇.work utmDescTape).cells = (work utmDescTape).cells := by
        rw [hc₇_desc, hdesc_cells₆, hdesc_cells₅, hdesc_cells₄, hc₃_desc,
            hdesc_cells₂, hdesc_cells₁]
      constructor
      · rw [hcells]; exact hdescOnTape.1
      constructor
      · intro i hi; rw [hcells]; exact hdescOnTape.2.1 i hi
      · rw [hcells]; exact hdescOnTape.2.2
    -- scratchHasTransOutput: scratch now has outputBits
    have hfinal_scratchOutput : scratchHasTransOutput k n (e q') wW oW iD wD oD
        (c₇.work utmScratchTape) := by
      constructor
      · -- tapeStoresBools outputBits scratch
        have hcells : (c₇.work utmScratchTape).cells = (c₅.work utmScratchTape).cells := by
          rw [hscratch_cells₇, hscratch_cells₆]
        constructor
        · -- cells 0 = start
          rw [hcells]; exact hcell0₅
        constructor
        · -- cells (i+1) = ofBool outputBits[i]
          intro i hi
          rw [hcells]
          have : (c₅.work utmScratchTape).cells (1 + i) = Γ.ofBool outputBits[i] :=
            hbits₅ i hi (by rw [houtLen] at hi; exact hi)
          rw [show i + 1 = 1 + i from by omega]; exact this
        · -- cells (length + 1) = blank
          show (c₇.work utmScratchTape).cells (outputBits.length + 1) = Γ.blank
          rw [hcells]
          have hge : outputBits.length + 1 ≥ TMEncoding.outputWidth k n + 1 := by
            rw [houtLen]
          have h_beyond := hscratch_beyond₅ (outputBits.length + 1) hge
          rw [h_beyond, hc₄_scratch, hscratch_cells₃, hscratch_cells₂,
              hc₁_scratch, houtLen]
          exact hscratchSentinel
      · exact hscratch_h₇
    -- Trace state/sim tapes back to work (preserved through all phases)
    have hc₇_state : c₇.work utmStateTape = work utmStateTape := by
      rw [hother₇ utmStateTape (by decide),
          hother₆ utmStateTape (by decide) (by decide),
          hother₅ utmStateTape (by decide) (by decide),
          hother₄ utmStateTape (by decide),
          hother₃ utmStateTape (by decide),
          hother₂ utmStateTape (by decide) (by decide),
          hother₁ utmStateTape (by decide)]
    have hc₇_sim : c₇.work utmSimTape = work utmSimTape := by
      rw [hother₇ utmSimTape (by decide),
          hother₆ utmSimTape (by decide) (by decide),
          hother₅ utmSimTape (by decide) (by decide),
          hother₄ utmSimTape (by decide),
          hother₃ utmSimTape (by decide),
          hother₂ utmSimTape (by decide) (by decide),
          hother₁ utmSimTape (by decide)]
    have hc₇_inp : c₇.input = inp := by
      rw [hinp₇, hinp₆, hinp₅, hinp₄, hinp₃, hinp₂, hinp₁]
    have hc₇_out : c₇.output = out := by
      rw [hout₇, hout₆, hout₅, hout₄, hout₃, hout₂, hout₁]
    refine ⟨hfinal_descOnTape, hfinal_scratchOutput, ?_, hscratch_h₇, hwf₇,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- desc head = 1
    · rw [hc₇_desc]; exact hdesc_h₆
    -- stateOnTapeAt preserved
    · rw [hc₇_state]; exact hstateOnTape
    -- superCellsCorrect preserved
    · rw [hc₇_sim]; exact hsimCorrect
    -- exact state/sim heads preserved
    · rw [hc₇_state, hstate_head_eq]
    · rw [hc₇_sim, hsim_head_eq]
    -- all heads ≥ 1
    · intro i
      have him : i = utmDescTape ∨ i = utmStateTape ∨ i = utmSimTape ∨ i = utmScratchTape := by
        revert i; decide
      rcases him with rfl | rfl | rfl | rfl
      · rw [hc₇_desc, hdesc_h₆]
      · rw [hc₇_state]; exact hheads utmStateTape
      · rw [hc₇_sim]; exact hheads utmSimTape
      · rw [hscratch_h₇]
    -- inp preserved
    · rw [hc₇_inp]; exact hinp_ns
    · rw [hc₇_inp]; exact hinp_h
    -- out preserved
    · rw [hc₇_out]; exact hout_ns
    · rw [hc₇_out]; exact hout_h

end TM
