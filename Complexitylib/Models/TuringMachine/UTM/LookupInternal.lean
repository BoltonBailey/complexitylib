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
  refine ⟨c₃, _, reachesIn_trans _ (reachesIn_trans _ hreach₁ hreach₂) hreach₃,
    hst₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf₃⟩
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
    refine ⟨c', _, hreach, hst, ?_, hdc, ?_, hsc, ho, hi, hou, hwf'⟩
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
    obtain ⟨c₁, steps₁, hreach₁, hst₁, hd₁, hdc₁, hs₁, hsc₁, ho₁, hi₁, hou₁, hwf₁⟩ :=
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
    obtain ⟨c', steps', hreach', hst', hd', hdc', hs', hsc', ho', hi', hou', hwf'⟩ :=
      ih c₁ hst₁ hwf₁
        (by rw [hi₁]; exact hinp) (by rw [hi₁]; exact hinp_h)
        (by rw [hou₁]; exact hout) (by rw [hou₁]; exact hout_h)
        (by intro j hj; rw [hdc₁]; exact hdesc_ns j hj)
        (by rw [hd₁]; omega)
        (by intro j hj; rw [hsc₁]; exact hscratch_ns j hj)
        hs₁
        (by intro i hne_d hne_s; rw [ho₁ i hne_d hne_s]; exact hother i hne_d hne_s)
        ih_hnonmatch ih_hmatch
    refine ⟨c', _, reachesIn_trans _ hreach₁ hreach', hst', ?_, ?_, ?_, ?_, ?_, ?_, ?_, hwf'⟩
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
      -- Scratch now has the output bits written
      (∀ (j : ℕ) (hj : j < outputBits.length),
        j < TMEncoding.outputWidth k n →
        (c'.work utmScratchTape).cells (1 + j) = Γ.ofBool (outputBits[j]'hj)) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
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
    refine ⟨c', .step hstep' .zero, hst', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- desc head
      rw [hdesc₁, Tape.writeAndMove, hmld, Tape.move]
      show (Tape.write _ _).head - 1 = _
      rw [lu_tape_write_head]; omega
    · -- scratch bits (from hscratch_bits)
      intro j hj hjow
      rw [hscratch_eq]; exact hscratch_bits j hj (by omega)
    · -- scratch cell 0
      rw [hscratch_eq]; exact hwf.1 utmScratchTape
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
    obtain ⟨c', hreach', hst', hhead', hbits', hcell0', hother', hinp', hout', hwf'⟩ :=
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
    refine ⟨c', .step hstep' hreach', hst', ?_, hbits', hcell0', ?_, ?_, ?_, hwf'⟩
    · -- desc head: (c.head + 1) + rem - 1 = c.head + (rem + 1) - 1
      rw [hhead', hc₁_desc_h]; omega
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

theorem lookupTM_hoareTime_proof (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm)
    (q : Fin k) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    let e := tm.stateEquivK hk
    ∃ B, (lookupTM (n := n) k).HoareTime
      (fun inp work out =>
        descOnTape desc (work utmDescTape) ∧
        (∀ i, (work i).head ≥ 1) ∧
        scratchHasInputPattern k n q iHead wHeads oHead (work utmScratchTape) ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1)
      (fun _inp work _out =>
        let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iHead wHeads oHead
        descOnTape desc (work utmDescTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  intro e
  -- Destructure the transition output for later use
  set δ_result := tm.δ (e.symm q) iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δ_result
  -- Provide the time bound
  refine ⟨lookupTimeBound k n desc.length, ?_⟩
  -- Unfold HoareTime
  intro inp work out hpre
  obtain ⟨hdescOnTape, hheads, hscratch_inp, hwf, hinp_ns, hinp_h, hout_ns, hout_h⟩ := hpre
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
  -- We sorry these encoding-level facts and prove the phase composition.
  have henc_connection : ∃ numBefore : ℕ,
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
    sorry
  obtain ⟨numBefore, hnonmatch, hmatch_entry, houtput_bits⟩ := henc_connection
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 2: entry_scan_to_match — scan entries until match found
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨c₂, steps₂, hreach₂, hst₂, hdesc_h₂, hdesc_cells₂,
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
  obtain ⟨c₅, hreach₅, hst₅, hdesc_h₅, hbits₅, hcell0₅, hother₅, hinp₅, hout₅, hwf₅⟩ :=
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
      (by sorry)
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
  · -- Time bound: sorry for now, can be filled in later
    sorry
  · -- Postcondition
    dsimp only []
    -- Trace tapes back to work
    have hc₇_desc : c₇.work utmDescTape = c₆.work utmDescTape :=
      hother₇ utmDescTape (by decide)
    -- descOnTape: desc tape cells unchanged throughout
    have hfinal_descOnTape : descOnTape desc (c₇.work utmDescTape) := by
      have hcells : (c₇.work utmDescTape).cells = (work utmDescTape).cells := by
        sorry
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
          sorry
      · exact hscratch_h₇
    refine ⟨hfinal_descOnTape, hfinal_scratchOutput, ?_, hscratch_h₇, hwf₇⟩
    -- desc head = 1
    rw [hc₇_desc]; exact hdesc_h₆

end TM
