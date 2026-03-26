import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Initialization: proof internals

HoareTime proof for `copyInputToWorkTM`: copies the TM description from the
input tape to work tape 0, stopping at the Γ.blank separator.
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Definitions
-- ════════════════════════════════════════════════════════════════════════

def initTM_pre (tm : TM n) (x : List Bool) : TapePred 4 :=
  fun inp work out =>
    inp = initTape (encodeUTMInput tm x) ∧
    work = (fun _ => initTape []) ∧
    out = initTape []

def copyBound (descLen : ℕ) : ℕ := descLen + 2

def postCopy (tm : TM n) (x : List Bool) : TapePred 4 :=
  fun inp work out =>
    let desc := TMEncoding.encodeTM tm
    descOnTape desc (work 0) ∧
    (work 0).head = desc.length + 1 ∧
    inp.head = desc.length + 1 ∧
    (∀ i : Fin 4, i ≠ 0 → (work i).head = 1) ∧
    out.head = 1 ∧
    WorkTapesWF work ∧
    (∀ i : Fin 4, i ≠ 0 → (work i).cells = (initTape []).cells) ∧
    inp.cells = (initTape (encodeUTMInput tm x)).cells ∧
    out.cells = (initTape []).cells

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem ofBool_ne_start (b : Bool) : Γ.ofBool b ≠ Γ.start := by
  cases b <;> simp [Γ.ofBool]

private theorem ofBool_ne_blank (b : Bool) : Γ.ofBool b ≠ Γ.blank := by
  cases b <;> simp [Γ.ofBool]

private theorem initTape_cells_succ {contents : List Γ} {j : ℕ} (hj : j < contents.length) :
    (initTape contents).cells (j + 1) = contents[j] := by
  simp only [initTape]
  simp [show j + 1 - 1 = j by omega, List.getElem?_eq_getElem hj]

private theorem initTape_cells_past {contents : List Γ} {j : ℕ} (hj : contents.length ≤ j) :
    (initTape contents).cells (j + 1) = Γ.blank := by
  simp only [initTape]
  simp [show j + 1 - 1 = j by omega, List.getElem?_eq_none hj]

private theorem write_head (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp [Tape.write]; split <;> rfl

private theorem write_cells_of_ne_head (t : Tape) (s : Γ) (h : t.head ≠ 0) (j : ℕ)
    (hj : j ≠ t.head) : (t.write s).cells j = t.cells j := by
  simp [Tape.write, h, Function.update, hj]

private theorem write_cells_at_head (t : Tape) (s : Γ) (h : t.head ≠ 0) :
    (t.write s).cells t.head = s := by
  simp [Tape.write, h, Function.update_self]

private theorem write_cells_at (t : Tape) (s : Γ) (h : t.head ≠ 0) (j : ℕ) (hj : t.head = j) :
    (t.write s).cells j = s := by
  subst hj; exact write_cells_at_head t s h

private theorem input_sep (desc : List Bool) (rest : List Γ) :
    (initTape (desc.map Γ.ofBool ++ [Γ.blank] ++ rest)).cells (desc.length + 1) =
    Γ.blank := by
  rw [initTape_cells_succ (by simp)]; simp [List.length_map]

private theorem input_desc (desc : List Bool) (rest : List Γ) (j : ℕ) (hj : j < desc.length) :
    (initTape (desc.map Γ.ofBool ++ [Γ.blank] ++ rest)).cells (j + 1) =
    Γ.ofBool desc[j] := by
  rw [initTape_cells_succ (by simp; omega)]
  simp only [List.append_assoc]
  rw [List.getElem_append_left (by simp; exact hj)]
  simp [List.getElem_map]

theorem encodeUTMInput_ne_start (tm : TM n) (x : List Bool) :
    ∀ g ∈ encodeUTMInput tm x, g ≠ Γ.start := by
  intro g hg habs; subst habs
  simp only [encodeUTMInput, List.mem_append, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false, Γ.ofBool] at hg
  rcases hg with ⟨_ | _, _, hc⟩ | hc | ⟨_ | _, _, hc⟩ <;> simp_all

-- ════════════════════════════════════════════════════════════════════════
-- The copy loop
-- ════════════════════════════════════════════════════════════════════════

private theorem copy_loop (desc : List Bool) (rest : List Γ) :
    ∀ (remaining copied : ℕ) (hrem : remaining = desc.length - copied)
    (hcopied : copied ≤ desc.length)
    (c : Cfg 4 (copyInputToWorkTM (0 : Fin 4)).Q),
    c.state = CopyPhase.copying →
    c.input.cells = (initTape (desc.map Γ.ofBool ++ [Γ.blank] ++ rest)).cells →
    c.input.head = copied + 1 →
    (c.work 0).head = copied + 1 →
    (c.work 0).cells 0 = Γ.start →
    (∀ (j : ℕ) (hj : j < copied), (c.work 0).cells (j + 1) = Γ.ofBool (desc[j]'(by omega))) →
    (∀ j, j ≥ copied + 1 → (c.work 0).cells j = Γ.blank) →
    (∀ i : Fin 4, i ≠ 0 → (c.work i).cells = (initTape []).cells ∧ (c.work i).head = 1) →
    c.output.cells = (initTape []).cells → c.output.head = 1 →
    ∃ c',
      (copyInputToWorkTM (0 : Fin 4)).reachesIn (remaining + 1) c c' ∧
      (copyInputToWorkTM (0 : Fin 4)).halted c' ∧
      (c'.work 0).cells 0 = Γ.start ∧
      (∀ (j : ℕ) (hj : j < desc.length),
        (c'.work 0).cells (j + 1) = Γ.ofBool (desc[j]'hj)) ∧
      (c'.work 0).cells (desc.length + 1) = Γ.blank ∧
      (c'.work 0).head = desc.length + 1 ∧
      c'.input.head = desc.length + 1 ∧
      (∀ i : Fin 4, i ≠ 0 → (c'.work i).head = 1) ∧
      c'.output.head = 1 ∧
      (∀ i : Fin 4, (c'.work i).cells 0 = Γ.start) ∧
      (∀ i : Fin 4, ∀ j, j ≥ 1 → (c'.work i).cells j ≠ Γ.start) ∧
      (∀ i : Fin 4, i ≠ 0 → (c'.work i).cells = (initTape []).cells) ∧
      c'.input.cells = c.input.cells ∧
      c'.output.cells = (initTape []).cells := by
  intro remaining
  induction remaining with
  | zero =>
    intro copied hrem hcopied c hstate hinp_cells hinp_head hw0_head hw0_cell0 hw0_copied
      hw0_blank hother hout_cells hout_head
    have hceq : copied = desc.length := by omega
    subst hceq
    have hinp_read : c.input.read = Γ.blank := by
      rw [Tape.read, hinp_head, hinp_cells]; exact input_sep desc rest
    have hw0_ne : (c.work 0).read ≠ Γ.start := by
      rw [Tape.read, hw0_head]; intro h
      have := hw0_blank _ le_rfl; rw [h] at this; exact Γ.noConfusion this
    have hother_ne : ∀ i : Fin 4, i ≠ 0 → (c.work i).read ≠ Γ.start := by
      intro i hi; rw [Tape.read, (hother i hi).2, (hother i hi).1]; simp [initTape]
    have hout_ne : c.output.read ≠ Γ.start := by
      rw [Tape.read, hout_head, hout_cells]; simp [initTape]
    have hiDir : idleDir c.input.read = Dir3.stay := by simp [idleDir, hinp_read]
    have hw0Dir : idleDir (c.work 0).read = Dir3.stay := by simp [idleDir, hw0_ne]
    -- Compute the step
    have hstep : (copyInputToWorkTM (0 : Fin 4)).step c = some
        { state := CopyPhase.done
          input := c.input.move (idleDir c.input.read)
          work := fun i => (c.work i).writeAndMove
            (Γw.blank).toΓ (idleDir (c.work i).read)
          output := c.output.writeAndMove (Γw.blank).toΓ (idleDir c.output.read) } := by
      simp only [TM.step, hstate, copyInputToWorkTM, hinp_read, allIdle, ↓reduceIte]
      congr 1
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- For each goal, the `c'.work i` is `(c.work i).writeAndMove Γw.blank.toΓ (idleDir (c.work i).read)`
    -- For i=0: writeAndMove(.blank, stay) since hw0Dir. head and cells[0] preserved.
    -- For i≠0: writeAndMove(.blank, stay) since hother_dir. head=1 preserved.
    -- cell 0
    · simp only [Tape.writeAndMove, hw0Dir, Tape.move]
      rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) 0 (by rw [hw0_head]; omega)]
      exact hw0_cell0
    -- desc bits
    · intro j hj
      simp only [Tape.writeAndMove, hw0Dir, Tape.move]
      rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) (j + 1) (by rw [hw0_head]; omega)]
      exact hw0_copied j hj
    -- blank sentinel
    · simp only [Tape.writeAndMove, hw0Dir, Tape.move]
      rw [write_cells_at _ _ (by rw [hw0_head]; omega) _ hw0_head]; rfl
    -- work 0 head
    · simp only [Tape.writeAndMove, hw0Dir, Tape.move, write_head, hw0_head]
    -- input head
    · simp only [hiDir, Tape.move, hinp_head]
    -- other work heads
    · intro i hi
      have hd : idleDir (c.work i).read = Dir3.stay := by simp [idleDir, hother_ne i hi]
      simp only [Tape.writeAndMove, hd, Tape.move, write_head, (hother i hi).2]
    -- output head
    · have hoDir : idleDir c.output.read = Dir3.stay := by simp [idleDir, hout_ne]
      simp only [Tape.writeAndMove, hoDir, Tape.move, write_head, hout_head]
    -- all work cells 0 = ▷
    · intro i
      by_cases hi : (i : Fin 4) = 0
      · subst hi
        simp only [Tape.writeAndMove, hw0Dir, Tape.move]
        rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) 0 (by rw [hw0_head]; omega)]
        exact hw0_cell0
      · have hd : idleDir (c.work i).read = Dir3.stay := by simp [idleDir, hother_ne i hi]
        simp only [Tape.writeAndMove, hd, Tape.move]
        rw [write_cells_of_ne_head _ _ (by rw [(hother i hi).2]; omega) 0
          (by rw [(hother i hi).2]; omega)]
        rw [(hother i hi).1]; rfl
    -- all work cells j ≥ 1 ≠ ▷
    · intro i j hj
      by_cases hi : (i : Fin 4) = 0
      · subst hi
        simp only [Tape.writeAndMove, hw0Dir, Tape.move]
        by_cases hje : j = desc.length + 1
        · subst hje; rw [write_cells_at _ _ (by rw [hw0_head]; omega) _ hw0_head]; exact Γ.noConfusion
        · rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) _ (by rw [hw0_head]; exact hje)]
          intro habs
          by_cases hjl : j ≤ desc.length
          · have := hw0_copied (j - 1) (by omega)
            rw [show j - 1 + 1 = j by omega] at this
            rw [this] at habs; exact ofBool_ne_start _ habs
          · have := hw0_blank j (by omega); rw [this] at habs; exact Γ.noConfusion habs
      · have hd : idleDir (c.work i).read = Dir3.stay := by simp [idleDir, hother_ne i hi]
        simp only [Tape.writeAndMove, hd, Tape.move]
        by_cases hje : j = 1
        · subst hje; rw [write_cells_at _ _ (by rw [(hother i hi).2]; omega) _ (hother i hi).2]
          exact Γ.noConfusion
        · rw [write_cells_of_ne_head _ _ (by rw [(hother i hi).2]; omega) _
            (by rw [(hother i hi).2]; exact hje)]
          rw [(hother i hi).1]
          intro habs; simp only [initTape] at habs
          have : j ≠ 0 := by omega
          simp [this] at habs
    -- non-target work tape cells preserved
    · intro i hi
      have hd : idleDir (c.work i).read = Dir3.stay := by simp [idleDir, hother_ne i hi]
      simp only [Tape.writeAndMove, hd, Tape.move]
      ext j
      by_cases hj0 : (c.work i).head = 0
      · rw [(hother i hi).2] at hj0; omega
      · by_cases hje : j = (c.work i).head
        · subst hje; rw [write_cells_at_head _ _ hj0, (hother i hi).2]
          simp [initTape, Γw.toΓ]
        · rw [write_cells_of_ne_head _ _ hj0 j hje, (hother i hi).1]
    -- input cells preserved (move only changes head)
    · simp only [hiDir, Tape.move]
    -- output cells = initTape []
    · have hoDir : idleDir c.output.read = Dir3.stay := by simp [idleDir, hout_ne]
      simp only [Tape.writeAndMove, hoDir, Tape.move]
      ext j
      by_cases hj0 : c.output.head = 0
      · omega
      · by_cases hje : j = c.output.head
        · subst hje; rw [write_cells_at_head _ _ hj0, hout_head]; simp [initTape, Γw.toΓ]
        · rw [write_cells_of_ne_head _ _ hj0 j hje, hout_cells]
  | succ rem ih =>
    intro copied hrem hcopied c hstate hinp_cells hinp_head hw0_head hw0_cell0 hw0_copied
      hw0_blank hother hout_cells hout_head
    have hclt : copied < desc.length := by omega
    have hinp_read : c.input.read = Γ.ofBool desc[copied] := by
      rw [Tape.read, hinp_head, hinp_cells]; exact input_desc desc rest copied hclt
    have hinp_ne_blank : c.input.read ≠ Γ.blank := by rw [hinp_read]; exact ofBool_ne_blank _
    have hwrite_val : (match c.input.read with
      | .zero => Γw.zero | .one => Γw.one | .blank => Γw.blank | .start => Γw.blank
      : Γw).toΓ = Γ.ofBool desc[copied] := by
      rw [hinp_read]; cases desc[copied] <;> rfl
    have hw0_ne : (c.work 0).read ≠ Γ.start := by
      rw [Tape.read, hw0_head]; intro h
      have := hw0_blank _ le_rfl; rw [h] at this; exact Γ.noConfusion this
    have hother_ne : ∀ i : Fin 4, i ≠ 0 → (c.work i).read ≠ Γ.start := by
      intro i hi; rw [Tape.read, (hother i hi).2, (hother i hi).1]; simp [initTape]
    have hout_ne : c.output.read ≠ Γ.start := by
      rw [Tape.read, hout_head, hout_cells]; simp [initTape]
    -- set up the write value
    set w : Γw := match c.input.read with
      | .zero => .zero | .one => .one | .blank => .blank | .start => .blank with w_def
    -- Build step result
    let c₁ : Cfg 4 (copyInputToWorkTM (0 : Fin 4)).Q :=
      { state := CopyPhase.copying
        input := c.input.move Dir3.right
        work := fun i => if i = (0 : Fin 4)
          then (c.work 0).writeAndMove w.toΓ Dir3.right
          else (c.work i).writeAndMove (Γw.blank).toΓ (idleDir (c.work i).read)
        output := c.output.writeAndMove (Γw.blank).toΓ (idleDir c.output.read) }
    have hstep : (copyInputToWorkTM (0 : Fin 4)).step c = some c₁ := by
      unfold TM.step; rw [show (copyInputToWorkTM (0 : Fin 4)).qhalt = CopyPhase.done from rfl]
      rw [show c.state = CopyPhase.copying from hstate]
      simp only [↓reduceIte, copyInputToWorkTM, hinp_ne_blank]
      show some _ = some c₁
      congr 1
      simp only [c₁]; congr 1
      ext i : 1
      split
      · next h => subst h; rfl
      · rfl
    -- Properties of c₁
    have h₁_inp_cells : c₁.input.cells = c.input.cells := by
      change (c.input.move Dir3.right).cells = _; simp [Tape.move]
    have h₁_inp_head : c₁.input.head = copied + 2 := by
      simp [c₁, Tape.move, hinp_head]
    have h₁_w0_head : (c₁.work 0).head = copied + 2 := by
      show ((c.work 0).writeAndMove w.toΓ Dir3.right).head = _
      simp [Tape.writeAndMove, Tape.move, write_head, hw0_head]
    have h₁_w0_cell0 : (c₁.work 0).cells 0 = Γ.start := by
      show ((c.work 0).writeAndMove w.toΓ Dir3.right).cells 0 = _
      rw [Tape.writeAndMove, Tape.move]
      rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) 0 (by rw [hw0_head]; omega)]
      exact hw0_cell0
    have h₁_w0_copied : ∀ (j : ℕ) (hj : j < copied + 1),
        (c₁.work 0).cells (j + 1) = Γ.ofBool (desc[j]'(by omega)) := by
      intro j hj
      change ((c.work 0).writeAndMove w.toΓ Dir3.right).cells (j + 1) = _
      simp only [Tape.writeAndMove, Tape.move]
      by_cases hje : j = copied
      · subst hje
        rw [write_cells_at _ _ (by rw [hw0_head]; omega) _ hw0_head]
        exact hwrite_val
      · rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) (j + 1)
            (by rw [hw0_head]; omega)]
        exact hw0_copied j (by omega)
    have h₁_w0_blank : ∀ j, j ≥ copied + 2 → (c₁.work 0).cells j = Γ.blank := by
      intro j hj
      change ((c.work 0).writeAndMove w.toΓ Dir3.right).cells j = _
      simp only [Tape.writeAndMove, Tape.move]
      rw [write_cells_of_ne_head _ _ (by rw [hw0_head]; omega) j (by rw [hw0_head]; omega)]
      exact hw0_blank j (by omega)
    have h₁_other : ∀ i : Fin 4, i ≠ 0 →
        (c₁.work i).cells = (initTape []).cells ∧ (c₁.work i).head = 1 := by
      intro i hi
      have hd : idleDir (c.work i).read = Dir3.stay := by simp [idleDir, hother_ne i hi]
      have hh := (hother i hi).2
      constructor
      · change (if (i : Fin 4) = 0 then _ else (c.work i).writeAndMove _ _).cells = _
        rw [if_neg hi, Tape.writeAndMove, hd, Tape.move]
        ext j
        by_cases hj0 : (c.work i).head = 0
        · omega -- head = 1 and head = 0 is contradictory
        · by_cases hje : j = (c.work i).head
          · subst hje; rw [write_cells_at_head _ _ hj0]; rw [hh]; simp [initTape]
          · rw [write_cells_of_ne_head _ _ hj0 j hje, (hother i hi).1]
      · change (if (i : Fin 4) = 0 then _ else (c.work i).writeAndMove _ _).head = _
        rw [if_neg hi, Tape.writeAndMove, hd, Tape.move, write_head, hh]
    have h₁_out_cells : c₁.output.cells = (initTape []).cells := by
      change (c.output.writeAndMove _ _).cells = _
      have hoDir : idleDir c.output.read = Dir3.stay := by simp [idleDir, hout_ne]
      rw [Tape.writeAndMove, hoDir, Tape.move]
      ext j
      by_cases hj0 : c.output.head = 0
      · omega -- head = 1 and head = 0 is contradictory
      · by_cases hje : j = c.output.head
        · subst hje; rw [write_cells_at_head _ _ hj0]; rw [hout_head]; simp [initTape]
        · rw [write_cells_of_ne_head _ _ hj0 j hje, hout_cells]
    have h₁_out_head : c₁.output.head = 1 := by
      change (c.output.writeAndMove _ _).head = _
      have hoDir : idleDir c.output.read = Dir3.stay := by simp [idleDir, hout_ne]
      rw [Tape.writeAndMove, hoDir, Tape.move, write_head, hout_head]
    -- Apply IH
    obtain ⟨c', hreach, hhalt, r1, r2, r3, r4, r5, r6, r7, r8, r9, r9b, r10, r11⟩ :=
      ih (copied + 1) (by omega) (by omega) c₁ rfl (h₁_inp_cells ▸ hinp_cells)
        h₁_inp_head h₁_w0_head h₁_w0_cell0 h₁_w0_copied h₁_w0_blank h₁_other
        h₁_out_cells h₁_out_head
    exact ⟨c', .step hstep hreach, hhalt, r1, r2, r3, r4, r5, r6, r7, r8, r9,
           fun i hi => r9b i hi,
           r10.trans h₁_inp_cells, r11⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

theorem copyInputToWorkTM_hoareTime (tm : TM n) (x : List Bool) :
    (copyInputToWorkTM (0 : Fin 4)).HoareTime
      (initTM_pre tm x)
      (postCopy tm x)
      (copyBound (TMEncoding.encodeTM tm).length) := by
  intro inp work out ⟨hinp, hwork, hout⟩
  set desc := TMEncoding.encodeTM tm
  set rest := x.map Γ.ofBool
  -- With head := 1, the initial config already has all heads at position 1,
  -- so we can directly apply copy_loop without an initial ▷-skip step.
  set c₀ : Cfg 4 (copyInputToWorkTM (0 : Fin 4)).Q :=
    { state := CopyPhase.copying, input := inp, work := work, output := out }
  -- Verify copy_loop preconditions hold for the initial config
  have hinp_cells₀ : c₀.input.cells =
      (initTape (desc.map Γ.ofBool ++ [Γ.blank] ++ rest)).cells := by
    simp only [c₀, hinp, encodeUTMInput, desc, rest]
  have hinp_head₀ : c₀.input.head = 0 + 1 := by
    simp [c₀, hinp, initTape]
  have hw0_head₀ : (c₀.work 0).head = 0 + 1 := by
    simp [c₀, hwork, initTape]
  have hw0_cell0₀ : (c₀.work 0).cells 0 = Γ.start := by
    simp [c₀, hwork, initTape]
  have hw0_blank₀ : ∀ j, j ≥ 0 + 1 → (c₀.work 0).cells j = Γ.blank := by
    intro j hj; simp only [c₀, hwork, initTape]
    have : j ≠ 0 := by omega
    simp [this]
  have hother₀ : ∀ i : Fin 4, i ≠ 0 →
      (c₀.work i).cells = (initTape []).cells ∧ (c₀.work i).head = 1 := by
    intro i _; exact ⟨by simp [c₀, hwork], by simp [c₀, hwork, initTape]⟩
  have hout_cells₀ : c₀.output.cells = (initTape []).cells := by
    simp [c₀, hout]
  have hout_head₀ : c₀.output.head = 1 := by
    simp [c₀, hout, initTape]
  -- Apply copy_loop from copied=0
  obtain ⟨c', hreach, hhalt, r1, r2, r3, r4, r5, r6, r7, r8, r9, r9b, r10, r11⟩ :=
    copy_loop desc rest desc.length 0 (by omega) (by omega) c₀ rfl
      hinp_cells₀ hinp_head₀ hw0_head₀ hw0_cell0₀
      (by intro j hj; omega) hw0_blank₀ hother₀ hout_cells₀ hout_head₀
  refine ⟨c', desc.length + 1, by unfold copyBound; omega, hreach, hhalt, ?_⟩
  · exact ⟨⟨r1, r2, r3⟩, r4, r5, r6, r7, ⟨r8, r9⟩, r9b, r10.trans hinp_cells₀, r11⟩

end TM
