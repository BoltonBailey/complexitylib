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
  sorry

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
  sorry

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
      (lookupTM (n := n) k).reachesIn steps c c' ∧
      c'.state = .compare ⟨0, by omega⟩ ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + TMEncoding.entryWidth k n ∧
      (c'.work utmDescTape).cells = (c.work utmDescTape).cells ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  sorry

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
  sorry

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
    (hscratch_h : (c.work utmScratchTape).head ≥ 1)
    (hother : ∀ i, i ≠ utmDescTape → i ≠ utmScratchTape →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    -- The output bits to be copied from desc
    (outputBits : List Bool)
    (houtLen : outputBits.length = TMEncoding.outputWidth k n)
    -- desc stores the remaining output bits starting at its current head
    (hdesc_bits : ∀ (j : ℕ), j < rem →
      ∃ (hj : TMEncoding.outputWidth k n - rem + j < outputBits.length),
      (c.work utmDescTape).cells ((c.work utmDescTape).head + j) =
      Γ.ofBool (outputBits[TMEncoding.outputWidth k n - rem + j]'hj)) :
    ∃ c',
      (lookupTM (n := n) k).reachesIn (rem + 1) c c' ∧
      c'.state = .rewindDesc ∧
      (c'.work utmDescTape).head = (c.work utmDescTape).head + rem ∧
      -- Scratch now has the output bits written
      (∀ (j : ℕ) (hj : j < outputBits.length),
        j < TMEncoding.outputWidth k n →
        (c'.work utmScratchTape).cells (1 + j) = Γ.ofBool (outputBits[j]'hj)) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (∀ i, i ≠ utmDescTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  sorry

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

end TM
