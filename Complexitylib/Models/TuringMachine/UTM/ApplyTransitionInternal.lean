import Complexitylib.Models.TuringMachine.UTM.ApplyTransition
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# ApplyTransition proof internals

Step-by-step simulation lemmas for `applyTransitionTM`.

## Architecture

Phase 0 (writeState): copy k state bits from scratch to state tape.
Phase 1 (write symbols): for each of n+1 tapes, write new symbol on sim tape.
Phase 2 (move heads): for each of n+2 tapes, move head marker on sim tape.
Phase 3 (cleanup): clear scratch, rewind all work tapes, halt.

## Main result

- `applyTransitionTM_hoareTime_proof` — HoareTime spec for `applyTransitionTM`
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem at_read_ne_start (t : Tape) (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hns _ hh

private theorem at_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start) (hh : t.head ≥ 1) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t :=
  tape_idle_preserve t hns hh

-- ════════════════════════════════════════════════════════════════════════
-- Phase 0: writeState — copy k bits from scratch to state tape
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 0: from writeState ⟨k,_⟩ to rdWrHi 0.
    Copies k bits from scratch tape to state tape in k+1 steps.
    After: state tape has new one-hot encoding, both state/scratch heads at k+1,
    sim/desc tapes unchanged, input/output unchanged. -/
private theorem phase0_writeState
    (c₀ : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (q' : Fin k)
    (hstate : c₀.state = ApplyTransQ.writeState ⟨k, by omega⟩)
    (hwf : WorkTapesWF c₀.work)
    (hstate_h : (c₀.work utmStateTape).head = 1)
    (hstate_blank : (c₀.work utmStateTape).cells (k + 1) = Γ.blank)
    (hscratch_h : (c₀.work utmScratchTape).head = 1)
    (hscratch_bits : ∀ j, j < k → (c₀.work utmScratchTape).cells (1 + j) =
      if j = q'.val then Γ.one else Γ.zero)
    (hsim_h : (c₀.work utmSimTape).head ≥ 1)
    (hdesc_h : (c₀.work utmDescTape).head ≥ 1)
    (hinp : c₀.input.read ≠ Γ.start) (hinp_h : c₀.input.head ≥ 1)
    (hout : c₀.output.read ≠ Γ.start) (hout_h : c₀.output.head ≥ 1) :
    ∃ c₁,
      (applyTransitionTM (n := n) k).reachesIn (k + 1) c₀ c₁ ∧
      c₁.state = ApplyTransQ.rdWrHi ⟨0, by omega⟩ ∧
      (∀ j, j < k → (c₁.work utmStateTape).cells (1 + j) =
        if j = q'.val then Γ.one else Γ.zero) ∧
      (c₁.work utmStateTape).cells (k + 1) = Γ.blank ∧
      (c₁.work utmStateTape).cells 0 = Γ.start ∧
      (c₁.work utmStateTape).head = k + 1 ∧
      (c₁.work utmScratchTape).cells = (c₀.work utmScratchTape).cells ∧
      (c₁.work utmScratchTape).head = k + 1 ∧
      c₁.work utmSimTape = c₀.work utmSimTape ∧
      c₁.work utmDescTape = c₀.work utmDescTape ∧
      c₁.input = c₀.input ∧ c₁.output = c₀.output ∧
      WorkTapesWF c₁.work := by
  -- Generalized loop: from writeState ⟨rem, _⟩ with heads at (k - rem + 1),
  -- after rem+1 steps reach rdWrHi 0 with the right properties.
  suffices loop : ∀ (rem : ℕ) (hrem : rem ≤ k)
    (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
    c.state = ApplyTransQ.writeState ⟨rem, by omega⟩ →
    (c.work utmStateTape).head = k - rem + 1 →
    (c.work utmScratchTape).head = k - rem + 1 →
    -- bits already copied
    (∀ j, j < k - rem → (c.work utmStateTape).cells (1 + j) =
      if j = q'.val then Γ.one else Γ.zero) →
    -- bits not yet copied are unchanged from c₀
    (∀ j, k - rem ≤ j → j < k → (c.work utmStateTape).cells (1 + j) =
      (c₀.work utmStateTape).cells (1 + j)) →
    (c.work utmStateTape).cells (k + 1) = Γ.blank →
    (c.work utmStateTape).cells 0 = Γ.start →
    (c.work utmScratchTape).cells = (c₀.work utmScratchTape).cells →
    c.work utmSimTape = c₀.work utmSimTape →
    c.work utmDescTape = c₀.work utmDescTape →
    c.input = c₀.input → c.output = c₀.output →
    WorkTapesWF c.work →
    ∃ c₁,
      (applyTransitionTM (n := n) k).reachesIn (rem + 1) c c₁ ∧
      c₁.state = ApplyTransQ.rdWrHi ⟨0, by omega⟩ ∧
      (∀ j, j < k → (c₁.work utmStateTape).cells (1 + j) =
        if j = q'.val then Γ.one else Γ.zero) ∧
      (c₁.work utmStateTape).cells (k + 1) = Γ.blank ∧
      (c₁.work utmStateTape).cells 0 = Γ.start ∧
      (c₁.work utmStateTape).head = k + 1 ∧
      (c₁.work utmScratchTape).cells = (c₀.work utmScratchTape).cells ∧
      (c₁.work utmScratchTape).head = k + 1 ∧
      c₁.work utmSimTape = c₀.work utmSimTape ∧
      c₁.work utmDescTape = c₀.work utmDescTape ∧
      c₁.input = c₀.input ∧ c₁.output = c₀.output ∧
      WorkTapesWF c₁.work by
    -- Instantiate loop with rem = k, initial config c₀
    have := loop k (le_refl k) c₀ hstate
      (by omega) (by omega)
      (by intro j hj; omega)
      (by intro j hj1 hj2; rfl)
      hstate_blank (hwf.1 utmStateTape)
      rfl rfl rfl rfl rfl hwf
    simpa using this
  intro rem
  induction rem with
  | zero =>
    -- Base case: rem = 0, one step from writeState ⟨0,_⟩ to rdWrHi 0
    intro hrem c hst hsh hsch hcopied _ hblank hcell0 hscr_cells hsim hdesc hinp_eq hout_eq hwf_c
    -- The state is not done
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    -- Head bounds
    have hsh' : (c.work utmStateTape).head ≥ 1 := by omega
    have hsch' : (c.work utmScratchTape).head ≥ 1 := by omega
    have hsim_h' : (c.work utmSimTape).head ≥ 1 := by rw [hsim]; exact hsim_h
    have hdesc_h' : (c.work utmDescTape).head ≥ 1 := by rw [hdesc]; exact hdesc_h
    have hinp' : c.input.read ≠ Γ.start := by rw [hinp_eq]; exact hinp
    have hinp_h' : c.input.head ≥ 1 := by rw [hinp_eq]; exact hinp_h
    have hout' : c.output.read ≠ Γ.start := by rw [hout_eq]; exact hout
    have hout_h' : c.output.head ≥ 1 := by rw [hout_eq]; exact hout_h
    -- Each work tape has head ≥ 1
    have hw_head : ∀ i : Fin 4, (c.work i).head ≥ 1 := by
      intro ⟨i, hi⟩
      match i, hi with
      | 0, _ => simp only [show (⟨0, by omega⟩ : Fin 4) = utmDescTape from rfl]; rw [hdesc]; exact hdesc_h
      | 1, _ => simp only [show (⟨1, by omega⟩ : Fin 4) = utmStateTape from rfl]; omega
      | 2, _ => simp only [show (⟨2, by omega⟩ : Fin 4) = utmSimTape from rfl]; rw [hsim]; exact hsim_h
      | 3, _ => simp only [show (⟨3, by omega⟩ : Fin 4) = utmScratchTape from rfl]; omega
    -- Each work tape has read ≠ start
    have hw_ns : ∀ i : Fin 4, (c.work i).read ≠ Γ.start :=
      fun i => at_read_ne_start _ (hw_head i) (hwf_c.2 i)
    -- Compute the step
    have hstep : (applyTransitionTM (n := n) k).step c = some
        { state := ApplyTransQ.rdWrHi ⟨0, by omega⟩
          input := c.input.move (idleDir c.input.read)
          work := fun i => (c.work i).writeAndMove
            ((readBackWrite ((c.work i).read)).toΓ) (idleDir ((c.work i).read))
          output := c.output.writeAndMove
            ((readBackWrite c.output.read).toΓ) (idleDir c.output.read) } := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, ↓reduceIte]
    -- Idle operations preserve tapes
    have hw_idle : ∀ i, (c.work i).writeAndMove
        ((readBackWrite ((c.work i).read)).toΓ) (idleDir ((c.work i).read)) = c.work i :=
      fun i => at_idle_preserve _ (hw_ns i) (hw_head i)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp', ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove
        ((readBackWrite c.output.read).toΓ) (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout' hout_h'
    -- Simplify step result
    have hstep' : (applyTransitionTM (n := n) k).step c = some
        { state := ApplyTransQ.rdWrHi ⟨0, by omega⟩
          input := c.input, work := c.work, output := c.output } := by
      rw [hstep]; congr 1; simp only [Cfg.mk.injEq]
      exact ⟨trivial, hinp_idle, funext hw_idle, hout_idle⟩
    exact ⟨{ state := ApplyTransQ.rdWrHi ⟨0, by omega⟩
             input := c.input, work := c.work, output := c.output },
           reachesIn.step hstep' reachesIn.zero, rfl,
           fun j hj => hcopied j (by omega),
           hblank, hcell0, by simp [hsh], hscr_cells, by simp [hsch],
           hsim, hdesc, hinp_eq, hout_eq, hwf_c⟩
  | succ rem' ih =>
    intro hrem c hst hsh hsch hcopied huncop hblank hcell0 hscr_cells hsim_eq hdesc_eq hinp_eq hout_eq hwf_c
    -- rem' + 1 > 0, so δ takes the copy branch
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    -- Head bounds
    have hsh_ge : (c.work utmStateTape).head ≥ 1 := by omega
    have hsch_ge : (c.work utmScratchTape).head ≥ 1 := by omega
    have hsim_h' : (c.work utmSimTape).head ≥ 1 := by rw [hsim_eq]; exact hsim_h
    have hdesc_h' : (c.work utmDescTape).head ≥ 1 := by rw [hdesc_eq]; exact hdesc_h
    have hinp' : c.input.read ≠ Γ.start := by rw [hinp_eq]; exact hinp
    have hout' : c.output.read ≠ Γ.start := by rw [hout_eq]; exact hout
    have hinp_h' : c.input.head ≥ 1 := by rw [hinp_eq]; exact hinp_h
    have hout_h' : c.output.head ≥ 1 := by rw [hout_eq]; exact hout_h
    -- Each work tape has head ≥ 1
    have hw_head : ∀ i : Fin 4, (c.work i).head ≥ 1 := by
      intro ⟨i, hi⟩
      match i, hi with
      | 0, _ => simp only [show (⟨0, by omega⟩ : Fin 4) = utmDescTape from rfl]; rw [hdesc_eq]; exact hdesc_h
      | 1, _ => simp only [show (⟨1, by omega⟩ : Fin 4) = utmStateTape from rfl]; omega
      | 2, _ => simp only [show (⟨2, by omega⟩ : Fin 4) = utmSimTape from rfl]; rw [hsim_eq]; exact hsim_h
      | 3, _ => simp only [show (⟨3, by omega⟩ : Fin 4) = utmScratchTape from rfl]; omega
    -- Each work tape has read ≠ start
    have hw_ns : ∀ i : Fin 4, (c.work i).read ≠ Γ.start :=
      fun i => at_read_ne_start _ (hw_head i) (hwf_c.2 i)
    -- The scratch tape read
    have hpos_eq : k - (rem' + 1) + 1 = (c.work utmScratchTape).head := by omega
    have hscr_read : (c.work utmScratchTape).read =
        if (k - (rem' + 1)) = q'.val then Γ.one else Γ.zero := by
      simp only [Tape.read, hsch]
      rw [hscr_cells]
      have : k - (rem' + 1) + 1 = 1 + (k - (rem' + 1)) := by omega
      rw [this]
      exact hscratch_bits (k - (rem' + 1)) (by omega)
    -- Abbreviations for the written symbol
    set scrVal := (readBackWrite ((c.work utmScratchTape).read)).toΓ with hscrVal_def
    -- Define the next config
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.writeState ⟨rem', by omega⟩
        input := c.input.move (idleDir c.input.read)
        work := fun i =>
          if i = utmStateTape then
            (c.work utmStateTape).writeAndMove scrVal Dir3.right
          else if i = utmScratchTape then
            (c.work utmScratchTape).writeAndMove scrVal Dir3.right
          else
            (c.work i).writeAndMove
              ((readBackWrite ((c.work i).read)).toΓ) (idleDir ((c.work i).read))
        output := c.output.writeAndMove
          ((readBackWrite c.output.read).toΓ) (idleDir c.output.read) }
    -- The work tape write function from δ
    have hworkW : ∀ i, (fun i => if i = utmStateTape then readBackWrite ((c.work utmScratchTape).read)
          else if i = utmScratchTape then readBackWrite ((c.work utmScratchTape).read)
          else readBackWrite ((c.work i).read)) i =
        (if i = utmStateTape then readBackWrite ((c.work utmScratchTape).read)
         else if i = utmScratchTape then readBackWrite ((c.work utmScratchTape).read)
         else readBackWrite ((c.work i).read)) := fun _ => rfl
    -- The work tape direction function from δ
    have hworkD : ∀ i, (fun i => if i = utmStateTape then Dir3.right
          else if i = utmScratchTape then Dir3.right
          else idleDir ((c.work i).read)) i =
        (if i = utmStateTape then Dir3.right
         else if i = utmScratchTape then Dir3.right
         else idleDir ((c.work i).read)) := fun _ => rfl
    -- For any tape i, the actual write+move matches c'.work i
    have hw_match : ∀ i,
        (c.work i).writeAndMove
          ((if i = utmStateTape then readBackWrite ((c.work utmScratchTape).read)
            else if i = utmScratchTape then readBackWrite ((c.work utmScratchTape).read)
            else readBackWrite ((c.work i).read)).toΓ)
          (if i = utmStateTape then Dir3.right
           else if i = utmScratchTape then Dir3.right
           else idleDir ((c.work i).read)) =
        c'.work i := by
      intro i; simp only [c']; split
      · next h => rw [h]
      · split
        · next _ h => rw [h]
        · next h1 h2 => rfl
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, show (rem' + 1) ≠ 0 from by omega, ↓reduceIte]
      congr 1; exact funext hw_match
    -- Helper: state tape writeAndMove expands
    have hst_wam := show c'.work utmStateTape =
        (c.work utmStateTape).writeAndMove scrVal Dir3.right by
      simp only [c', ↓reduceIte]
    -- Helper: scratch tape access
    have hsc_wam := show c'.work utmScratchTape =
        (c.work utmScratchTape).writeAndMove scrVal Dir3.right by
      simp only [c', show (utmScratchTape : Fin 4) ≠ utmStateTape from by decide, ↓reduceIte]
    -- Input idle
    have hc'_inp : c'.input = c.input := by
      simp only [c', idleDir, hinp', ↓reduceIte, Tape.move]
    -- Output idle
    have hc'_out : c'.output = c.output := tape_idle_preserve _ hout' hout_h'
    -- scrVal = the one-hot bit value
    have hscrVal_eq : scrVal = if (k - (rem' + 1)) = q'.val then Γ.one else Γ.zero := by
      simp only [scrVal, readBackWrite_toΓ_eq (hw_ns utmScratchTape), hscr_read]
    -- Tape.write is not at cell 0 (head ≥ 1)
    have hst_h_ne0 : ¬ (c.work utmStateTape).head = 0 := by omega
    have hsc_h_ne0 : ¬ (c.work utmScratchTape).head = 0 := by omega
    -- State tape head
    have hc'_st_head : (c'.work utmStateTape).head = k - rem' + 1 := by
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      simp only [hsh]; omega
    -- Scratch tape head
    have hc'_scr_head : (c'.work utmScratchTape).head = k - rem' + 1 := by
      rw [hsc_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc_h_ne0, ↓reduceIte]
      simp only [hsch]; omega
    -- State tape: the newly written cell
    have hc'_st_cells_new : (c'.work utmStateTape).cells (1 + (k - (rem' + 1))) =
        if (k - (rem' + 1)) = q'.val then Γ.one else Γ.zero := by
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      have : 1 + (k - (rem' + 1)) = (c.work utmStateTape).head := by omega
      rw [Function.update_apply]; simp [this, hscrVal_eq]
    -- State tape: previously copied bits unchanged (j < k - (rem'+1))
    have hc'_st_cells_old : ∀ j, j < k - (rem' + 1) →
        (c'.work utmStateTape).cells (1 + j) = if j = q'.val then Γ.one else Γ.zero := by
      intro j hj
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      rw [Function.update_apply]; simp only [hsh]; split
      · omega
      · exact hcopied j hj
    -- State tape: uncopied bits unchanged (k - rem' ≤ j < k)
    have hc'_st_cells_future : ∀ j, k - rem' ≤ j → j < k →
        (c'.work utmStateTape).cells (1 + j) = (c₀.work utmStateTape).cells (1 + j) := by
      intro j hj1 hj2
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      rw [Function.update_apply]; simp only [hsh]; split
      · omega
      · exact huncop j (by omega) hj2
    -- Scratch tape cells preserved (readBackWrite is identity for non-start)
    have hc'_scr_cells : (c'.work utmScratchTape).cells = (c₀.work utmScratchTape).cells := by
      rw [hsc_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc_h_ne0, ↓reduceIte]
      rw [hscrVal_def, readBackWrite_toΓ_eq (hw_ns utmScratchTape)]
      simp only [Tape.read]; rw [Function.update_eq_self]; exact hscr_cells
    -- Sim tape idle
    have hc'_sim : c'.work utmSimTape = c₀.work utmSimTape := by
      simp only [c', show (utmSimTape : Fin 4) ≠ utmStateTape from by decide,
                 show (utmSimTape : Fin 4) ≠ utmScratchTape from by decide, ↓reduceIte]
      rw [← hsim_eq]; exact at_idle_preserve _ (hw_ns utmSimTape) hsim_h'
    -- Desc tape idle
    have hc'_desc : c'.work utmDescTape = c₀.work utmDescTape := by
      simp only [c', show (utmDescTape : Fin 4) ≠ utmStateTape from by decide,
                 show (utmDescTape : Fin 4) ≠ utmScratchTape from by decide, ↓reduceIte]
      rw [← hdesc_eq]; exact at_idle_preserve _ (hw_ns utmDescTape) hdesc_h'
    -- State tape blank sentinel preserved
    have hc'_blank : (c'.work utmStateTape).cells (k + 1) = Γ.blank := by
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      rw [Function.update_apply]; simp only [hsh]; split
      · omega
      · exact hblank
    -- State tape cell 0 preserved
    have hc'_cell0 : (c'.work utmStateTape).cells 0 = Γ.start := by
      rw [hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
      rw [Function.update_apply]; simp only [hsh]; split
      · omega
      · exact hcell0
    -- WorkTapesWF preserved
    have hc'_wf : WorkTapesWF c'.work := by
      constructor
      · -- cells 0 = start for all tapes
        intro i
        by_cases hi1 : i = utmStateTape
        · rw [hi1, hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
          rw [Function.update_apply]; simp only [hsh]; split <;> [omega; exact hcell0]
        · by_cases hi2 : i = utmScratchTape
          · rw [hi2, hsc_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc_h_ne0, ↓reduceIte]
            rw [Function.update_apply]; simp only [hsch]; split <;> [omega; exact hwf_c.1 utmScratchTape]
          · -- other tapes idle
            have : c'.work i = c.work i := by
              change (if i = utmStateTape then _ else if i = utmScratchTape then _ else _) = _
              simp only [hi1, hi2, ↓reduceIte]
              exact at_idle_preserve _ (hw_ns i) (hw_head i)
            rw [this]; exact hwf_c.1 i
      · -- cells j ≠ start for j ≥ 1
        intro i j hj
        by_cases hi1 : i = utmStateTape
        · rw [hi1, hst_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h_ne0, ↓reduceIte]
          rw [Function.update_apply]; simp only [hsh]; split
          · rw [hscrVal_eq]; split <;> simp
          · exact hwf_c.2 utmStateTape j hj
        · by_cases hi2 : i = utmScratchTape
          · rw [hi2, hsc_wam]; simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc_h_ne0, ↓reduceIte]
            rw [Function.update_apply]; simp only [hsch]; split
            · rw [hscrVal_def, readBackWrite_toΓ_eq (hw_ns utmScratchTape)]
              exact hwf_c.2 utmScratchTape _ hsch_ge
            · exact hwf_c.2 utmScratchTape j hj
          · have : c'.work i = c.work i := by
              change (if i = utmStateTape then _ else if i = utmScratchTape then _ else _) = _
              simp only [hi1, hi2, ↓reduceIte]
              exact at_idle_preserve _ (hw_ns i) (hw_head i)
            rw [this]; exact hwf_c.2 i j hj
    -- Copied bits for IH: bits 0..k-rem'-1 are correct
    have hc'_copied : ∀ j, j < k - rem' →
        (c'.work utmStateTape).cells (1 + j) = if j = q'.val then Γ.one else Γ.zero := by
      intro j hj
      by_cases hjn : j < k - (rem' + 1)
      · exact hc'_st_cells_old j hjn
      · have : j = k - (rem' + 1) := by omega
        rw [this]; exact hc'_st_cells_new
    -- Apply IH
    obtain ⟨c₁, hreach₁, hst₁, hbits₁, hblank₁, hcell0₁, hhead₁,
            hscr₁, hsch₁, hsim₁, hdesc₁, hinp₁, hout₁, hwf₁⟩ :=
      ih (by omega) c' (by simp [c']) hc'_st_head hc'_scr_head hc'_copied
        hc'_st_cells_future hc'_blank hc'_cell0 hc'_scr_cells hc'_sim hc'_desc
        (by rw [hc'_inp, hinp_eq]) (by rw [hc'_out, hout_eq]) hc'_wf
    exact ⟨c₁, reachesIn.step hstep hreach₁, hst₁, hbits₁, hblank₁, hcell0₁,
           hhead₁, hscr₁, hsch₁, hsim₁, hdesc₁, hinp₁, hout₁, hwf₁⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: write symbols to sim tape
-- ════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
private theorem phase1_rwWr_loop (k : ℕ) (wrIdx : Fin (n + 1)) :
    ∀ (h : ℕ) (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
    c.state = ApplyTransQ.rwWr wrIdx →
    (c.work utmSimTape).head = h →
    WorkTapesWF c.work →
    (∀ i : Fin 4, i ≠ utmSimTape → (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      (applyTransitionTM (n := n) k).reachesIn (h + 1) c c' ∧
      c'.state = ApplyTransQ.rwWrR wrIdx ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (∀ i : Fin 4, i ≠ utmSimTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro h
  induction h with
  | zero =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hread : (c.work utmSimTape).read = Γ.start := by
      simp only [Tape.read, hhead]; exact hwf.1 utmSimTape
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmSimTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmSimTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have hsim_wam : (c.work utmSimTape).writeAndMove
        ((readBackWrite ((c.work utmSimTape).read)).toΓ) Dir3.right =
        ⟨1, (c.work utmSimTape).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.write, hhead, ↓reduceIte, Tape.move]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwWrR wrIdx
        input := c.input
        work := fun i => if i = utmSimTape then ⟨1, (c.work utmSimTape).cells⟩
                         else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmSimTape
      · subst hi; simp only [↓reduceIte]; exact hsim_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    exact ⟨c', reachesIn.step hstep reachesIn.zero, rfl,
      by simp [c'],
      by simp [c'],
      fun i hi => by simp [c', hi],
      rfl, rfl,
      ⟨fun i => by
        by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.1 utmSimTape]
        · simp [c', hi, hwf.1 i],
       fun i j hj => by
        by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.2 utmSimTape j hj]
        · simp [c', hi, hwf.2 i j hj]⟩⟩
  | succ h ih =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hhead_ne0 : ¬ (c.work utmSimTape).head = 0 := by omega
    have hsim_ge1 : (c.work utmSimTape).head ≥ 1 := by omega
    have hread_ne : (c.work utmSimTape).read ≠ Γ.start :=
      at_read_ne_start _ hsim_ge1 (hwf.2 utmSimTape)
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmSimTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmSimTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have h_ne0 : ¬ (h + 1 = 0) := by omega
    have hread_eq : (c.work utmSimTape).read = (c.work utmSimTape).cells (h + 1) := by
      simp [Tape.read, hhead]
    have hcell_ns : (c.work utmSimTape).cells (h + 1) ≠ Γ.start := hread_eq ▸ hread_ne
    have hsim_wam : (c.work utmSimTape).writeAndMove
        ((readBackWrite ((c.work utmSimTape).read)).toΓ) Dir3.left =
        ⟨h, (c.work utmSimTape).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hhead, h_ne0, ↓reduceIte,
        hread_eq, readBackWrite_toΓ_eq hcell_ns, Function.update_eq_self, Nat.add_sub_cancel]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwWr wrIdx
        input := c.input
        work := fun i => if i = utmSimTape then ⟨h, (c.work utmSimTape).cells⟩ else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread_ne, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmSimTape
      · subst hi; simp only [↓reduceIte]; exact hsim_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    have hc'_other : ∀ i, i ≠ utmSimTape → c'.work i = c.work i :=
      fun i hi => by simp [c', hi]
    have hc'_cells : (c'.work utmSimTape).cells = (c.work utmSimTape).cells := by
      simp [c']
    have hc'_wf : WorkTapesWF c'.work := by
      constructor
      · intro i; by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.1 utmSimTape]
        · rw [hc'_other i hi]; exact hwf.1 i
      · intro i j hj; by_cases hi : i = utmSimTape
        · simp [c', hi]; exact hwf.2 utmSimTape j hj
        · rw [hc'_other i hi]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hother_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c' (by simp [c']) (by simp [c']) hc'_wf
        (fun i hi => by rw [hc'_other i hi]; exact hother i hi)
        (by simp [c']; exact hinp) (by simp [c']; exact hinp_h)
        (by simp [c']; exact hout) (by simp [c']; exact hout_h)
    exact ⟨c_f, reachesIn.step hstep hreach, hst_f, hhead_f,
      by rw [hcells_f, hc'_cells],
      fun i hi => by rw [hother_f i hi, hc'_other i hi],
      by rw [hinp_f], by rw [hout_f], hwf_f⟩

set_option maxHeartbeats 800000 in
private theorem phase2_rwMv_loop (k : ℕ) (mvIdx : Fin (n + 2)) :
    ∀ (h : ℕ) (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
    c.state = ApplyTransQ.rwMv mvIdx →
    (c.work utmSimTape).head = h →
    WorkTapesWF c.work →
    (∀ i : Fin 4, i ≠ utmSimTape → (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      (applyTransitionTM (n := n) k).reachesIn (h + 1) c c' ∧
      c'.state = ApplyTransQ.rwMvR mvIdx ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (∀ i : Fin 4, i ≠ utmSimTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro h
  induction h with
  | zero =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hread : (c.work utmSimTape).read = Γ.start := by
      simp only [Tape.read, hhead]; exact hwf.1 utmSimTape
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmSimTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmSimTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have hsim_wam : (c.work utmSimTape).writeAndMove
        ((readBackWrite ((c.work utmSimTape).read)).toΓ) Dir3.right =
        ⟨1, (c.work utmSimTape).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.write, hhead, ↓reduceIte, Tape.move]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwMvR mvIdx
        input := c.input
        work := fun i => if i = utmSimTape then ⟨1, (c.work utmSimTape).cells⟩
                         else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmSimTape
      · subst hi; simp only [↓reduceIte]; exact hsim_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    exact ⟨c', reachesIn.step hstep reachesIn.zero, rfl,
      by simp [c'],
      by simp [c'],
      fun i hi => by simp [c', hi],
      rfl, rfl,
      ⟨fun i => by
        by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.1 utmSimTape]
        · simp [c', hi, hwf.1 i],
       fun i j hj => by
        by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.2 utmSimTape j hj]
        · simp [c', hi, hwf.2 i j hj]⟩⟩
  | succ h ih =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hhead_ne0 : ¬ (c.work utmSimTape).head = 0 := by omega
    have hsim_ge1 : (c.work utmSimTape).head ≥ 1 := by omega
    have hread_ne : (c.work utmSimTape).read ≠ Γ.start :=
      at_read_ne_start _ hsim_ge1 (hwf.2 utmSimTape)
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmSimTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmSimTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have h_ne0 : ¬ (h + 1 = 0) := by omega
    have hread_eq : (c.work utmSimTape).read = (c.work utmSimTape).cells (h + 1) := by
      simp [Tape.read, hhead]
    have hcell_ns : (c.work utmSimTape).cells (h + 1) ≠ Γ.start := hread_eq ▸ hread_ne
    have hsim_wam : (c.work utmSimTape).writeAndMove
        ((readBackWrite ((c.work utmSimTape).read)).toΓ) Dir3.left =
        ⟨h, (c.work utmSimTape).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hhead, h_ne0, ↓reduceIte,
        hread_eq, readBackWrite_toΓ_eq hcell_ns, Function.update_eq_self, Nat.add_sub_cancel]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwMv mvIdx
        input := c.input
        work := fun i => if i = utmSimTape then ⟨h, (c.work utmSimTape).cells⟩ else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread_ne, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmSimTape
      · subst hi; simp only [↓reduceIte]; exact hsim_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    have hc'_other : ∀ i, i ≠ utmSimTape → c'.work i = c.work i :=
      fun i hi => by simp [c', hi]
    have hc'_cells : (c'.work utmSimTape).cells = (c.work utmSimTape).cells := by
      simp [c']
    have hc'_wf : WorkTapesWF c'.work := by
      constructor
      · intro i; by_cases hi : i = utmSimTape
        · simp [c', hi, hwf.1 utmSimTape]
        · rw [hc'_other i hi]; exact hwf.1 i
      · intro i j hj; by_cases hi : i = utmSimTape
        · simp [c', hi]; exact hwf.2 utmSimTape j hj
        · rw [hc'_other i hi]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hother_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c' (by simp [c']) (by simp [c']) hc'_wf
        (fun i hi => by rw [hc'_other i hi]; exact hother i hi)
        (by simp [c']; exact hinp) (by simp [c']; exact hinp_h)
        (by simp [c']; exact hout) (by simp [c']; exact hout_h)
    exact ⟨c_f, reachesIn.step hstep hreach, hst_f, hhead_f,
      by rw [hcells_f, hc'_cells],
      fun i hi => by rw [hother_f i hi, hc'_other i hi],
      by rw [hinp_f], by rw [hout_f], hwf_f⟩

/-- Phase 1: processes n+1 tapes (work 0..n-1, output), writing new symbols.
    Reads 2 bits per tape from scratch (the Γw encoding), scans sim tape for
    the head marker, writes the decoded symbol's hi/lo cells, and rewinds sim
    tape back to cell 1. -/
private theorem phase1_writeSymbols {Q : Type} [DecidableEq Q]
    (c₁ : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (simCfg : Cfg n Q) (wW : Fin n → Γw) (oW : Γw)
    (hstate : c₁.state = ApplyTransQ.rdWrHi ⟨0, by omega⟩)
    (hwf : WorkTapesWF c₁.work)
    (hsim_correct : superCellsCorrect simCfg (c₁.work utmSimTape))
    (hsim_h : (c₁.work utmSimTape).head = 1)
    (hscratch_h : (c₁.work utmScratchTape).head = k + 1)
    (hscratch_wf : ∀ j, j ≥ 1 → (c₁.work utmScratchTape).cells j ≠ Γ.start)
    (hinp : c₁.input.read ≠ Γ.start) (hinp_h : c₁.input.head ≥ 1)
    (hout : c₁.output.read ≠ Γ.start) (hout_h : c₁.output.head ≥ 1)
    (hheads : ∀ i : Fin 4, (c₁.work i).head ≥ 1) :
    ∃ steps c₂,
      (applyTransitionTM (n := n) k).reachesIn steps c₁ c₂ ∧
      c₂.state = ApplyTransQ.rdMvHi ⟨0, by omega⟩ ∧
      (c₂.work utmSimTape).head = 1 ∧
      c₂.work utmDescTape = c₁.work utmDescTape ∧
      (c₂.work utmStateTape).cells = (c₁.work utmStateTape).cells ∧
      c₂.input = c₁.input ∧ c₂.output = c₁.output ∧
      WorkTapesWF c₂.work ∧
      (∀ i : Fin 4, (c₂.work i).head ≥ 1) := by
  -- Outer induction: process tapes wrIdx = 0, ..., n
  suffices outer : ∀ (fuel wrIdx : ℕ) (hwi : wrIdx < n + 1)
      (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
      fuel + wrIdx = n + 1 →
      c.state = ApplyTransQ.rdWrHi ⟨wrIdx, hwi⟩ →
      (c.work utmSimTape).head = 1 →
      (∀ p t, (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t)) →
      WorkTapesWF c.work →
      c.work utmDescTape = c₁.work utmDescTape →
      (c.work utmStateTape).cells = (c₁.work utmStateTape).cells →
      c.input = c₁.input → c.output = c₁.output →
      (∀ i : Fin 4, (c.work i).head ≥ 1) →
      (∀ j, j ≥ 1 → (c.work utmScratchTape).cells j ≠ Γ.start) →
      ∃ steps c₂,
        (applyTransitionTM (n := n) k).reachesIn steps c c₂ ∧
        c₂.state = ApplyTransQ.rdMvHi ⟨0, by omega⟩ ∧
        (c₂.work utmSimTape).head = 1 ∧
        c₂.work utmDescTape = c₁.work utmDescTape ∧
        (c₂.work utmStateTape).cells = (c₁.work utmStateTape).cells ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output ∧
        WorkTapesWF c₂.work ∧
        (∀ i : Fin 4, (c₂.work i).head ≥ 1) by
    exact outer (n + 1) 0 (by omega) c₁ (by omega) hstate hsim_h
      (fun _ _ => rfl) hwf rfl rfl rfl rfl hheads hscratch_wf
  intro fuel
  induction fuel with
  | zero => intro wrIdx hwi c hfuel; omega
  | succ m ih =>
    intro wrIdx hwi c hfuel hst hsimh hmarkers hwf' hdesc hstatecells
      hinp_eq hout_eq hw_heads hscr_wf
    -- Extract marker info for the current tape (tapeIdx = wrIdx + 1)
    set tapeIdx := wrIdx + 1 with htapeIdx_def
    have htapeIdx_lt : tapeIdx < n + 2 := by omega
    have hsim_marker : ∀ pos, (c.work utmSimTape).cells
        (SuperCell.simTapeOffset (n + 2) pos tapeIdx) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx) :=
      fun pos => hmarkers pos tapeIdx
    -- Extract h_target from superCellsCorrect
    obtain ⟨h_target, hmarker_vals⟩ : ∃ h_target, ∀ pos,
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx) =
        if h_target = pos then Γ.one else Γ.blank := by
      by_cases hwk : wrIdx < n
      · exact ⟨(simCfg.work ⟨wrIdx, hwk⟩).head,
          fun pos => (hsim_correct.2.2.1 ⟨wrIdx, hwk⟩ pos).1⟩
      · have hwn : wrIdx = n := by omega
        subst hwn; exact ⟨simCfg.output.head, fun pos => (hsim_correct.2.2.2 pos).1⟩
    have hmarker_current : ∀ pos,
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx) =
        if h_target = pos then Γ.one else Γ.blank := by
      intro pos; rw [hsim_marker pos]; exact hmarker_vals pos
    -- ── One-tape iteration: scan → write → rewind → advance ──
    suffices one_tape : ∃ steps_t c_t,
        (applyTransitionTM (n := n) k).reachesIn steps_t c c_t ∧
        c_t.state = (if h : wrIdx + 1 < n + 1
          then ApplyTransQ.rdWrHi ⟨wrIdx + 1, h⟩
          else ApplyTransQ.rdMvHi ⟨0, by omega⟩) ∧
        (c_t.work utmSimTape).head = 1 ∧
        (∀ p t, (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) =
          (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t)) ∧
        WorkTapesWF c_t.work ∧
        c_t.work utmDescTape = c₁.work utmDescTape ∧
        (c_t.work utmStateTape).cells = (c₁.work utmStateTape).cells ∧
        c_t.input = c₁.input ∧ c_t.output = c₁.output ∧
        (∀ i : Fin 4, (c_t.work i).head ≥ 1) ∧
        (∀ j, j ≥ 1 → (c_t.work utmScratchTape).cells j ≠ Γ.start) by
      -- Dispatch: apply IH or finish
      obtain ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hmarkers_t, hwf_t, hdesc_t,
              hstatecells_t, hinp_t, hout_t, hheads_t, hscr_t⟩ := one_tape
      by_cases hlast : wrIdx + 1 < n + 1
      · -- Not last tape: apply IH
        rw [dif_pos hlast] at hst_t
        obtain ⟨steps_rest, c₂, hreach_rest, hst₂, hsimh₂, hdesc₂, hstatecells₂,
                hinp₂, hout₂, hwf₂, hheads₂⟩ :=
          ih (wrIdx + 1) hlast c_t (by omega) hst_t hsimh_t hmarkers_t hwf_t
            hdesc_t hstatecells_t hinp_t hout_t hheads_t hscr_t
        exact ⟨steps_t + steps_rest, c₂, reachesIn_trans _ hreach_t hreach_rest,
          hst₂, hsimh₂, hdesc₂, hstatecells₂, hinp₂, hout₂, hwf₂, hheads₂⟩
      · -- Last tape: done
        rw [dif_neg hlast] at hst_t
        exact ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hdesc_t, hstatecells_t,
          hinp_t, hout_t, hwf_t, hheads_t⟩
    -- ── Prove one_tape ──
    -- Common helpers
    have hinp' : c.input.read ≠ Γ.start := by rw [hinp_eq]; exact hinp
    have hinp_h' : c.input.head ≥ 1 := by rw [hinp_eq]; exact hinp_h
    have hout' : c.output.read ≠ Γ.start := by rw [hout_eq]; exact hout
    have hout_h' : c.output.head ≥ 1 := by rw [hout_eq]; exact hout_h
    set W := 3 * (n + 2) with hW_def
    set offset := SuperCell.simTapeOffset (n + 2) h_target tapeIdx with hoffset_def
    have hoffset_pos : offset ≥ 1 := by
      simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]; omega
    -- ── Steps 1-2: rdWrHi → rdWrLo → scanWr (2 fixed steps) ──
    -- Read 2 bits from scratch, enter scan mode. Sim tape unchanged.
    have hsteps_12 : ∃ c₁₂ sHi sLo,
        (applyTransitionTM (n := n) k).reachesIn 2 c c₁₂ ∧
        c₁₂.state = .scanWr ⟨wrIdx, hwi⟩ ⟨0, by omega⟩ sHi sLo ∧
        c₁₂.work utmSimTape = c.work utmSimTape ∧
        (∀ i, i ≠ utmScratchTape → i ≠ utmSimTape → c₁₂.work i = c.work i) ∧
        c₁₂.input = c.input ∧ c₁₂.output = c.output ∧
        WorkTapesWF c₁₂.work ∧
        (∀ i : Fin 4, (c₁₂.work i).head ≥ 1) ∧
        (∀ j, j ≥ 1 → (c₁₂.work utmScratchTape).cells j ≠ Γ.start) := by
      -- Setup
      have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        rw [hst]; simp [applyTransitionTM]
      have hw_ns : ∀ i, (c.work i).read ≠ Γ.start :=
        fun i => at_read_ne_start _ (hw_heads i) (hwf'.2 i)
      have hw_idle : ∀ i, (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
        fun i => tape_idle_preserve _ (hw_ns i) (hw_heads i)
      have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
        simp only [idleDir, hinp', ↓reduceIte, Tape.move]
      have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
          (idleDir c.output.read) = c.output :=
        tape_idle_preserve _ hout' hout_h'
      -- Scratch readBackWrite + right = ⟨head+1, cells⟩
      have hscr_wam : (c.work utmScratchTape).writeAndMove
          ((readBackWrite ((c.work utmScratchTape).read)).toΓ) Dir3.right =
          ⟨(c.work utmScratchTape).head + 1, (c.work utmScratchTape).cells⟩ := by
        simp only [Tape.writeAndMove, Tape.write,
          show ¬(c.work utmScratchTape).head = 0 from by have := hw_heads utmScratchTape; omega,
          ↓reduceIte, Tape.move]
        congr 1; rw [readBackWrite_toΓ_eq (hw_ns utmScratchTape)]
        simp only [Tape.read, Function.update_eq_self]
      -- Step 1 config: rdWrHi → rdWrLo
      set c_a : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := .rdWrLo ⟨wrIdx, hwi⟩ (c.work utmScratchTape).read
          input := c.input
          work := fun i => if i = utmScratchTape
            then ⟨(c.work utmScratchTape).head + 1, (c.work utmScratchTape).cells⟩
            else c.work i
          output := c.output }
      have hstep_a : (applyTransitionTM (n := n) k).step c = some c_a := by
        simp only [TM.step, hne, ↓reduceIte]
        congr 1; rw [hst]; simp only [applyTransitionTM]
        simp only [c_a, Cfg.mk.injEq]
        refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
        by_cases hi : i = utmScratchTape
        · subst hi; simp only [↓reduceIte]; exact hscr_wam
        · simp only [hi, ↓reduceIte]; exact hw_idle i
      -- c_a properties
      have hca_other : ∀ i, i ≠ utmScratchTape → c_a.work i = c.work i :=
        fun i hi => by simp [c_a, hi]
      have hca_scr : c_a.work utmScratchTape =
          ⟨(c.work utmScratchTape).head + 1, (c.work utmScratchTape).cells⟩ := by
        simp [c_a]
      have hca_wf : WorkTapesWF c_a.work := by
        constructor
        · intro i; by_cases hi : i = utmScratchTape
          · simp [c_a, hi, hwf'.1 utmScratchTape]
          · rw [hca_other i hi]; exact hwf'.1 i
        · intro i j hj; by_cases hi : i = utmScratchTape
          · simp [c_a, hi]; exact hwf'.2 utmScratchTape j hj
          · rw [hca_other i hi]; exact hwf'.2 i j hj
      have hca_heads : ∀ i : Fin 4, (c_a.work i).head ≥ 1 := by
        intro i; by_cases hi : i = utmScratchTape
        · rw [hi, hca_scr]; dsimp; have := hw_heads utmScratchTape; omega
        · rw [hca_other i hi]; exact hw_heads i
      have hca_ns : ∀ i, (c_a.work i).read ≠ Γ.start :=
        fun i => at_read_ne_start _ (hca_heads i) (hca_wf.2 i)
      have hca_idle : ∀ i, (c_a.work i).writeAndMove ((readBackWrite ((c_a.work i).read)).toΓ)
          (idleDir ((c_a.work i).read)) = c_a.work i :=
        fun i => tape_idle_preserve _ (hca_ns i) (hca_heads i)
      have hne_a : c_a.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        simp [c_a, applyTransitionTM]
      -- Scratch wam for step 2
      have hca_scr_wam : (c_a.work utmScratchTape).writeAndMove
          ((readBackWrite ((c_a.work utmScratchTape).read)).toΓ) Dir3.right =
          ⟨(c.work utmScratchTape).head + 2, (c.work utmScratchTape).cells⟩ := by
        rw [hca_scr]
        simp only [Tape.writeAndMove, Tape.write,
          show ¬((c.work utmScratchTape).head + 1) = 0 from by omega,
          ↓reduceIte, Tape.move, Tape.read,
          Tape.mk.injEq]
        exact ⟨trivial, by rw [readBackWrite_toΓ_eq (hscr_wf _ (by omega))]; exact Function.update_eq_self _ _⟩
      -- Step 2 config: rdWrLo → scanWr
      set c_b : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := .scanWr ⟨wrIdx, hwi⟩ ⟨0, by omega⟩
            (symToSimHi (decodeΓw (c.work utmScratchTape).read (c_a.work utmScratchTape).read))
            (symToSimLo (decodeΓw (c.work utmScratchTape).read (c_a.work utmScratchTape).read))
          input := c.input
          work := fun i => if i = utmScratchTape
            then ⟨(c.work utmScratchTape).head + 2, (c.work utmScratchTape).cells⟩
            else c.work i
          output := c.output }
      have hstep_b : (applyTransitionTM (n := n) k).step c_a = some c_b := by
        simp only [TM.step, hne_a, ↓reduceIte]
        congr 1; simp only [c_a]; simp only [applyTransitionTM, ↓reduceIte]
        simp only [c_b, c_a, decodeΓw, symToSimHi, symToSimLo, ↓reduceIte, Tape.read, Cfg.mk.injEq]
        refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
        by_cases hi : i = utmScratchTape
        · subst hi; simp only [↓reduceIte]; exact hca_scr_wam
        · simp only [hi, ↓reduceIte]; exact hw_idle i
      -- Provide witnesses and prove postconditions
      refine ⟨c_b,
        symToSimHi (decodeΓw (c.work utmScratchTape).read (c_a.work utmScratchTape).read),
        symToSimLo (decodeΓw (c.work utmScratchTape).read (c_a.work utmScratchTape).read),
        reachesIn.step hstep_a (reachesIn.step hstep_b reachesIn.zero),
        rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
      · -- Sim tape unchanged
        simp [c_b, show (utmSimTape : Fin 4) ≠ utmScratchTape from by decide]
      · -- Other tapes preserved
        intro i hi_scr hi_sim; simp [c_b, hi_scr]
      · -- WF
        constructor
        · intro i; by_cases hi : i = utmScratchTape
          · simp [c_b, hi, hwf'.1 utmScratchTape]
          · simp [c_b, hi, hwf'.1 i]
        · intro i j hj; by_cases hi : i = utmScratchTape
          · simp [c_b, hi]; exact hwf'.2 utmScratchTape j hj
          · simp [c_b, hi, hwf'.2 i j hj]
      · -- Heads ≥ 1
        intro i; by_cases hi : i = utmScratchTape
        · subst hi; simp [c_b]
        · simp only [c_b, hi, ↓reduceIte]; exact hw_heads i
      · -- Scratch cells WF
        intro j hj; simp [c_b]; exact hscr_wf j hj
    obtain ⟨c₁₂, sHi, sLo, hreach₁₂, hst₁₂, hsim₁₂, hother₁₂, hinp₁₂,
            hout₁₂, hwf₁₂, hheads₁₂, hscr₁₂⟩ := hsteps_12
    -- ── Step 3: scanWr loop → wrHi (variable steps) ──
    -- Scan sim tape for head marker, find it at position offset.
    have hstep_scan : ∃ steps_s c_s,
        (applyTransitionTM (n := n) k).reachesIn steps_s c₁₂ c_s ∧
        c_s.state = .wrHi ⟨wrIdx, hwi⟩ sHi sLo ∧
        (c_s.work utmSimTape).head = offset + 1 ∧
        (c_s.work utmSimTape).cells = (c₁₂.work utmSimTape).cells ∧
        (∀ i, i ≠ utmSimTape → c_s.work i = c₁₂.work i) ∧
        c_s.input = c₁₂.input ∧ c_s.output = c₁₂.output ∧
        WorkTapesWF c_s.work := by
      -- Key arithmetic: offset - 1 = h_target * W + 3 * tapeIdx
      have hoffset_expand : offset - 1 = h_target * W + 3 * tapeIdx := by
        simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width, hW_def]; omega
      -- sim tape head of c₁₂ = 1
      have hsimh₁₂ : (c₁₂.work utmSimTape).head = 1 := by rw [hsim₁₂, hsimh]
      -- Induction on remaining distance from current sim head to offset
      suffices loop : ∀ (rem : ℕ) (c' : Cfg 4 (applyTransitionTM (n := n) k).Q),
          (c'.work utmSimTape).head + rem = offset →
          c'.state = .scanWr ⟨wrIdx, hwi⟩
            ⟨((c'.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ sHi sLo →
          (c'.work utmSimTape).cells = (c₁₂.work utmSimTape).cells →
          (∀ i, i ≠ utmSimTape → c'.work i = c₁₂.work i) →
          c'.input = c₁₂.input → c'.output = c₁₂.output →
          WorkTapesWF c'.work →
          (∀ i, (c'.work i).head ≥ 1) →
          ∃ c_s,
            (applyTransitionTM (n := n) k).reachesIn (rem + 1) c' c_s ∧
            c_s.state = .wrHi ⟨wrIdx, hwi⟩ sHi sLo ∧
            (c_s.work utmSimTape).head = offset + 1 ∧
            (c_s.work utmSimTape).cells = (c₁₂.work utmSimTape).cells ∧
            (∀ i, i ≠ utmSimTape → c_s.work i = c₁₂.work i) ∧
            c_s.input = c₁₂.input ∧ c_s.output = c₁₂.output ∧
            WorkTapesWF c_s.work by
        obtain ⟨c_s, hr, hst_s, hh_s, hcells_s, ho_s, hinp_s, hout_s, hwf_s⟩ :=
          loop (offset - 1) c₁₂ (by omega)
            (by convert hst₁₂ using 2; ext; simp [hsimh₁₂])
            rfl (fun _ _ => rfl) rfl rfl hwf₁₂ (fun i => hheads₁₂ i)
        exact ⟨offset, c_s, by rwa [show offset - 1 + 1 = offset by omega] at hr,
               hst_s, hh_s, hcells_s, ho_s, hinp_s, hout_s, hwf_s⟩
      intro rem; induction rem with
      | zero =>
        intro c' hhead hstate' hcells' ho' hinp' hout' hwf' hheads'
        -- head = offset, we're at the marker
        have hsim_head' : (c'.work utmSimTape).head = offset := by omega
        -- pos = 3 * tapeIdx = 3 * (wrIdx + 1) (the marker column)
        have hpos_val : ((c'.work utmSimTape).head - 1) % W = 3 * tapeIdx := by
          rw [hsim_head']
          have h1 : offset - 1 = h_target * W + 3 * tapeIdx := hoffset_expand
          rw [h1, Nat.mul_add_mod_self_right,
              Nat.mod_eq_of_lt (show 3 * tapeIdx < W by omega)]
        have hpos_eq_wrIdx : 3 * tapeIdx = 3 * (wrIdx + 1) := by omega
        -- sim reads Γ.one at the marker
        have hread_one : (c'.work utmSimTape).read = Γ.one := by
          simp only [Tape.read, hsim_head', hcells', hsim₁₂]
          have := hmarker_current h_target
          simp only [] at this; exact this
        have hread_ne_start : (c'.work utmSimTape).read ≠ Γ.start :=
          at_read_ne_start _ (hheads' utmSimTape) (hwf'.2 utmSimTape)
        -- Not halted
        have hne : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
          rw [hstate']; simp [applyTransitionTM]
        -- Idle helpers
        have hw_ns : ∀ i, i ≠ utmSimTape → (c'.work i).read ≠ Γ.start :=
          fun i hi => at_read_ne_start _ (hheads' i) (hwf'.2 i)
        have hw_idle : ∀ i, i ≠ utmSimTape →
            (c'.work i).writeAndMove ((readBackWrite ((c'.work i).read)).toΓ)
              (idleDir ((c'.work i).read)) = c'.work i :=
          fun i hi => tape_idle_preserve _ (hw_ns i hi) (hheads' i)
        have hinp_idle : c'.input.move (idleDir c'.input.read) = c'.input := by
          simp only [idleDir,
            (show c'.input.read ≠ Γ.start by rw [hinp', hinp₁₂, hinp_eq]; exact hinp),
            ↓reduceIte, Tape.move]
        have hout_idle : c'.output.writeAndMove ((readBackWrite c'.output.read).toΓ)
            (idleDir c'.output.read) = c'.output :=
          tape_idle_preserve _
            (by rw [hout', hout₁₂, hout_eq]; exact hout)
            (by rw [hout', hout₁₂, hout_eq]; exact hout_h)
        -- Sim tape writeAndMove readBackWrite right = ⟨head+1, cells⟩
        have hsim_wam : (c'.work utmSimTape).writeAndMove
            ((readBackWrite ((c'.work utmSimTape).read)).toΓ) Dir3.right =
            ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩ := by
          simp only [Tape.writeAndMove, Tape.write,
            show ¬(c'.work utmSimTape).head = 0 from by have := hheads' utmSimTape; omega,
            ↓reduceIte, Tape.move]
          congr 1; rw [readBackWrite_toΓ_eq hread_ne_start]
          simp only [Tape.read, Function.update_eq_self]
        -- One step to wrHi
        set c_next : Cfg 4 (applyTransitionTM (n := n) k).Q :=
          { state := .wrHi ⟨wrIdx, hwi⟩ sHi sLo
            input := c'.input
            work := fun i => if i = utmSimTape
              then ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩
              else c'.work i
            output := c'.output }
        have hstep : (applyTransitionTM (n := n) k).step c' = some c_next := by
          simp only [TM.step, hne, ↓reduceIte]
          congr 1; rw [hstate']; simp only [applyTransitionTM]
          simp only [hpos_val, hpos_eq_wrIdx, ↓reduceIte, hread_one]
          simp only [c_next, Cfg.mk.injEq]
          refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
          by_cases hi : i = utmSimTape
          · subst hi; simp only [↓reduceIte]; exact hsim_wam
          · simp only [hi, ↓reduceIte]; exact hw_idle i hi
        have hwf_next : WorkTapesWF c_next.work := by
          constructor
          · intro i; by_cases hi : i = utmSimTape
            · simp [c_next, hi, hwf'.1 utmSimTape]
            · simp [c_next, hi, hwf'.1 i]
          · intro i j hj; by_cases hi : i = utmSimTape
            · simp [c_next, hi, hwf'.2 utmSimTape j hj]
            · simp [c_next, hi, hwf'.2 i j hj]
        exact ⟨c_next, .step hstep .zero, rfl,
          by simp [c_next, hsim_head'],
          by simp [c_next]; exact hcells',
          fun i hi => by simp [c_next, hi]; exact ho' i hi,
          hinp', hout', hwf_next⟩
      | succ m ih =>
        intro c' hhead hstate' hcells' ho' hinp' hout' hwf' hheads'
        -- head < offset since head + (m+1) = offset
        have hhead_lt : (c'.work utmSimTape).head < offset := by omega
        have hhead_ge : (c'.work utmSimTape).head ≥ 1 := hheads' utmSimTape
        have hread_ne_start : (c'.work utmSimTape).read ≠ Γ.start :=
          at_read_ne_start _ hhead_ge (hwf'.2 utmSimTape)
        -- The scan doesn't find the marker at this position.
        set pos := ((c'.work utmSimTape).head - 1) % W with hpos_def
        -- Show the read is NOT Γ.one when pos = 3 * (wrIdx + 1)
        have hread_ne_one : ¬(pos = 3 * (wrIdx + 1) ∧
            (c'.work utmSimTape).read = Γ.one) := by
          intro ⟨hpos_eq, hread_eq⟩
          simp only [Tape.read] at hread_eq
          rw [hcells', hsim₁₂] at hread_eq
          have hdiv := Nat.div_add_mod ((c'.work utmSimTape).head - 1) W
          have hhead_eq : (c'.work utmSimTape).head =
              SuperCell.simTapeOffset (n + 2) (((c'.work utmSimTape).head - 1) / W) tapeIdx := by
            simp only [SuperCell.simTapeOffset, SuperCell.width, hW_def]
            have := hpos_def ▸ hpos_eq
            set q := ((c'.work utmSimTape).head - 1) / W with hq_def
            have : W * q = q * (3 * (n + 2)) := by rw [hW_def, Nat.mul_comm]
            omega
          rw [hhead_eq] at hread_eq
          have hmk := hmarker_current (((c'.work utmSimTape).head - 1) / W)
          rw [hread_eq] at hmk
          split_ifs at hmk with heq
          rw [← heq, ← hoffset_def] at hhead_eq; omega
        -- Not halted
        have hne : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
          rw [hstate']; simp [applyTransitionTM]
        -- Idle helpers
        have hw_ns : ∀ i, i ≠ utmSimTape → (c'.work i).read ≠ Γ.start :=
          fun i hi => at_read_ne_start _ (hheads' i) (hwf'.2 i)
        have hw_idle : ∀ i, i ≠ utmSimTape →
            (c'.work i).writeAndMove ((readBackWrite ((c'.work i).read)).toΓ)
              (idleDir ((c'.work i).read)) = c'.work i :=
          fun i hi => tape_idle_preserve _ (hw_ns i hi) (hheads' i)
        have hinp_idle : c'.input.move (idleDir c'.input.read) = c'.input := by
          simp only [idleDir,
            (show c'.input.read ≠ Γ.start by rw [hinp', hinp₁₂, hinp_eq]; exact hinp),
            ↓reduceIte, Tape.move]
        have hout_idle : c'.output.writeAndMove ((readBackWrite c'.output.read).toΓ)
            (idleDir c'.output.read) = c'.output :=
          tape_idle_preserve _
            (by rw [hout', hout₁₂, hout_eq]; exact hout)
            (by rw [hout', hout₁₂, hout_eq]; exact hout_h)
        -- Sim tape writeAndMove readBackWrite right = ⟨head+1, cells⟩
        have hsim_wam : (c'.work utmSimTape).writeAndMove
            ((readBackWrite ((c'.work utmSimTape).read)).toΓ) Dir3.right =
            ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩ := by
          simp only [Tape.writeAndMove, Tape.write,
            show ¬(c'.work utmSimTape).head = 0 from by have := hheads' utmSimTape; omega,
            ↓reduceIte, Tape.move]
          congr 1; rw [readBackWrite_toΓ_eq hread_ne_start]
          simp only [Tape.read, Function.update_eq_self]
        -- Both branches produce the same tape effects: advance sim right, idle rest.
        -- Define the next config explicitly
        set c_next : Cfg 4 (applyTransitionTM (n := n) k).Q :=
          { state := .scanWr ⟨wrIdx, hwi⟩
              ⟨(pos + 1) % W, Nat.mod_lt _ (by omega)⟩ sHi sLo
            input := c'.input
            work := fun i => if i = utmSimTape
              then ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩
              else c'.work i
            output := c'.output }
        have hstep : (applyTransitionTM (n := n) k).step c' = some c_next := by
          simp only [TM.step, hne, ↓reduceIte]
          congr 1; rw [hstate']; simp only [applyTransitionTM]
          -- Both sub-cases of the outer if produce the same writes/dirs
          by_cases hpeq : ((c'.work utmSimTape).head - 1) % W = 3 * (wrIdx + 1)
          · -- pos = 3*(wrIdx+1), but read ≠ one
            have hread_ne : (c'.work utmSimTape).read ≠ Γ.one :=
              fun h => hread_ne_one ⟨hpeq, h⟩
            simp only [hpeq, ↓reduceIte, hread_ne]
            have hpos_eq_rw : (3 * (wrIdx + 1) + 1) % (3 * (n + 2)) = (pos + 1) % W := by
              rw [hpos_def, hpeq, hW_def]
            simp only [c_next, Cfg.mk.injEq]
            refine ⟨?_, hinp_idle, funext fun i => ?_, hout_idle⟩
            · congr 1; ext1; exact hpos_eq_rw
            · by_cases hi : i = utmSimTape
              · subst hi; simp only [↓reduceIte]; exact hsim_wam
              · simp only [hi, ↓reduceIte]; exact hw_idle i hi
          · -- pos ≠ 3*(wrIdx+1)
            simp only [hpeq, ↓reduceIte]
            simp only [c_next, Cfg.mk.injEq]
            exact ⟨by congr 1, hinp_idle,
              funext fun i => by
                by_cases hi : i = utmSimTape
                · subst hi; simp only [↓reduceIte]; exact hsim_wam
                · simp only [hi, ↓reduceIte]; exact hw_idle i hi,
              hout_idle⟩
        -- c_next properties
        have hh1 : (c_next.work utmSimTape).head = (c'.work utmSimTape).head + 1 := by
          simp [c_next]
        have hcells1 : (c_next.work utmSimTape).cells = (c'.work utmSimTape).cells := by
          simp [c_next]
        have ho1 : ∀ i, i ≠ utmSimTape → c_next.work i = c'.work i :=
          fun i hi => by simp [c_next, hi]
        -- WorkTapesWF for intermediate config
        have hwf1 : WorkTapesWF c_next.work := by
          constructor
          · intro i; by_cases h : i = utmSimTape
            · simp [c_next, h, hwf'.1 utmSimTape]
            · simp [c_next, h, hwf'.1 i]
          · intro i j hj; by_cases h : i = utmSimTape
            · simp [c_next, h, hwf'.2 utmSimTape j hj]
            · simp [c_next, h, hwf'.2 i j hj]
        have hheads1 : ∀ i, (c_next.work i).head ≥ 1 := by
          intro i; by_cases h : i = utmSimTape
          · rw [h, hh1]; omega
          · rw [ho1 i h]; exact hheads' i
        -- Show the new state matches IH form
        have hmod_step : (pos + 1) % W = (c'.work utmSimTape).head % W := by
          rw [hpos_def]
          rw [Nat.mod_add_mod, Nat.sub_add_cancel hhead_ge]
        have hstate1 : c_next.state = .scanWr ⟨wrIdx, hwi⟩
            ⟨((c_next.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ sHi sLo := by
          simp only [c_next]; congr 1; ext; exact hmod_step
        -- Apply IH
        have hhead1 : (c_next.work utmSimTape).head + m = offset := by omega
        obtain ⟨c_f, hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f⟩ :=
          ih c_next hhead1 hstate1 (by rw [hcells1, hcells'])
            (by intro i hne_i; rw [ho1 i hne_i, ho' i hne_i])
            (by simp [c_next, hinp']) (by simp [c_next, hout']) hwf1 hheads1
        exact ⟨c_f, .step hstep hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f⟩
    obtain ⟨steps_s, c_s, hreach_s, hst_s, hsimh_s, hsimcells_s,
            hother_s, hinp_s, hout_s, hwf_s⟩ := hstep_scan
    -- ── Steps 4-5: wrHi → wrLo → rwWr (2 fixed steps) ──
    -- Write sHi and sLo to sim tape. Only sim cells at offset+1, offset+2 change.
    have hsteps_45 : ∃ c₄₅,
        (applyTransitionTM (n := n) k).reachesIn 2 c_s c₄₅ ∧
        c₄₅.state = .rwWr ⟨wrIdx, hwi⟩ ∧
        (c₄₅.work utmSimTape).head = offset + 2 ∧
        (∀ j, j ≠ offset + 1 → j ≠ offset + 2 →
          (c₄₅.work utmSimTape).cells j = (c_s.work utmSimTape).cells j) ∧
        (∀ i, i ≠ utmSimTape → c₄₅.work i = c_s.work i) ∧
        c₄₅.input = c_s.input ∧ c₄₅.output = c_s.output ∧
        WorkTapesWF c₄₅.work := by
      -- Setup
      have hne : c_s.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        rw [hst_s]; simp [applyTransitionTM]
      have hsim_heads_ge : (c_s.work utmSimTape).head ≥ 1 := by rw [hsimh_s]; omega
      have hw_ns : ∀ i, (c_s.work i).read ≠ Γ.start := by
        intro i; by_cases hi : i = utmSimTape
        · subst hi; exact at_read_ne_start _ hsim_heads_ge (hwf_s.2 _)
        · rw [show (c_s.work i).read = (c₁₂.work i).read from by rw [hother_s i hi]]
          exact at_read_ne_start _ (hheads₁₂ i) (hwf₁₂.2 _)
      have hw_heads_s : ∀ i : Fin 4, (c_s.work i).head ≥ 1 := by
        intro i; by_cases hi : i = utmSimTape
        · subst hi; rw [hsimh_s]; omega
        · have : (c_s.work i).head = (c₁₂.work i).head := by
            rw [hother_s i hi]
          rw [this]; exact hheads₁₂ i
      have hw_idle : ∀ i, i ≠ utmSimTape →
          (c_s.work i).writeAndMove ((readBackWrite ((c_s.work i).read)).toΓ)
            (idleDir ((c_s.work i).read)) = c_s.work i :=
        fun i hi => tape_idle_preserve _ (hw_ns i) (hw_heads_s i)
      have hinp_idle : c_s.input.move (idleDir c_s.input.read) = c_s.input := by
        simp only [idleDir, show c_s.input.read ≠ Γ.start from by
          rw [hinp_s, hinp₁₂]; exact hinp', ↓reduceIte, Tape.move]
      have hout_idle : c_s.output.writeAndMove ((readBackWrite c_s.output.read).toΓ)
          (idleDir c_s.output.read) = c_s.output :=
        tape_idle_preserve _ (by rw [hout_s, hout₁₂]; exact hout')
          (by rw [hout_s, hout₁₂]; exact hout_h')
      -- Sim tape writeAndMove for step 1: write sHi at offset+1, move right to offset+2
      have h_ne0_s : ¬(c_s.work utmSimTape).head = 0 := by rw [hsimh_s]; omega
      have hsim_wam_1 : (c_s.work utmSimTape).writeAndMove sHi.toΓ Dir3.right =
          ⟨offset + 2, Function.update (c_s.work utmSimTape).cells (offset + 1) sHi.toΓ⟩ := by
        simp only [Tape.writeAndMove, Tape.write, h_ne0_s, ↓reduceIte, Tape.move]
        simp only [hsimh_s]
      -- Construct intermediate config after step 1 (wrHi → wrLo)
      set c_mid : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := ApplyTransQ.wrLo ⟨wrIdx, hwi⟩ sLo
          input := c_s.input
          work := fun i => if i = utmSimTape
            then ⟨offset + 2, Function.update (c_s.work utmSimTape).cells (offset + 1) sHi.toΓ⟩
            else c_s.work i
          output := c_s.output }
      have hstep_1 : (applyTransitionTM (n := n) k).step c_s = some c_mid := by
        simp only [TM.step, hne, ↓reduceIte]
        congr 1; rw [hst_s]; simp only [applyTransitionTM]
        simp only [c_mid, Cfg.mk.injEq]
        refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
        by_cases hi : i = utmSimTape
        · subst hi; simp only [↓reduceIte]; exact hsim_wam_1
        · simp only [hi, ↓reduceIte]; exact hw_idle i hi
      -- c_mid properties
      have hcm_simh : (c_mid.work utmSimTape).head = offset + 2 := by simp [c_mid]
      have hcm_other : ∀ i, i ≠ utmSimTape → c_mid.work i = c_s.work i :=
        fun i hi => by simp [c_mid, hi]
      have hcm_wf : WorkTapesWF c_mid.work := by
        constructor
        · intro i; by_cases hi : i = utmSimTape
          · simp [c_mid, hi, hwf_s.1 utmSimTape]
          · rw [hcm_other i hi]; exact hwf_s.1 i
        · intro i j hj; by_cases hi : i = utmSimTape
          · subst hi; simp only [c_mid, ↓reduceIte]
            by_cases hje : j = offset + 1
            · subst hje; simp
              cases sHi <;> simp
            · rw [Function.update_of_ne hje]; exact hwf_s.2 utmSimTape j hj
          · rw [hcm_other i hi]; exact hwf_s.2 i j hj
      have hne_mid : c_mid.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        simp [c_mid, applyTransitionTM]
      have hcm_heads : ∀ i : Fin 4, (c_mid.work i).head ≥ 1 := by
        intro i; by_cases hi : i = utmSimTape
        · subst hi; rw [hcm_simh]; omega
        · rw [hcm_other i hi]; exact hw_heads_s i
      have hcm_ns : ∀ i, (c_mid.work i).read ≠ Γ.start :=
        fun i => at_read_ne_start _ (hcm_heads i) (hcm_wf.2 i)
      have hcm_idle : ∀ i, i ≠ utmSimTape →
          (c_mid.work i).writeAndMove ((readBackWrite ((c_mid.work i).read)).toΓ)
            (idleDir ((c_mid.work i).read)) = c_mid.work i :=
        fun i hi => by rw [hcm_other i hi]; exact hw_idle i hi
      -- Sim tape writeAndMove for step 2: write sLo at offset+2, stay at offset+2
      -- In wrLo state, ALL work tapes get idleDir (no special sim direction)
      have hcm_sim_ns : (c_mid.work utmSimTape).read ≠ Γ.start :=
        at_read_ne_start _ (by rw [hcm_simh]; omega) (hcm_wf.2 _)
      have hcm_sim_idle_dir : idleDir ((c_mid.work utmSimTape).read) = Dir3.stay := by
        simp only [idleDir, hcm_sim_ns, ↓reduceIte]
      have h_ne0_mid : ¬(c_mid.work utmSimTape).head = 0 := by rw [hcm_simh]; omega
      have hsim_wam_2 : (c_mid.work utmSimTape).writeAndMove sLo.toΓ
          (idleDir ((c_mid.work utmSimTape).read)) =
          ⟨offset + 2, Function.update (c_mid.work utmSimTape).cells (offset + 2) sLo.toΓ⟩ := by
        rw [hcm_sim_idle_dir]
        simp only [Tape.writeAndMove, Tape.write, h_ne0_mid, ↓reduceIte, Tape.move]
        simp only [hcm_simh]
      -- Construct final config after step 2 (wrLo → rwWr)
      set c₄₅ : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := ApplyTransQ.rwWr ⟨wrIdx, hwi⟩
          input := c_s.input
          work := fun i => if i = utmSimTape
            then ⟨offset + 2, Function.update (c_mid.work utmSimTape).cells (offset + 2) sLo.toΓ⟩
            else c_s.work i
          output := c_s.output }
      have hst_mid : c_mid.state = ApplyTransQ.wrLo ⟨wrIdx, hwi⟩ sLo := rfl
      have hstep_2 : (applyTransitionTM (n := n) k).step c_mid = some c₄₅ := by
        simp only [TM.step, hne_mid, ↓reduceIte]
        congr 1; rw [hst_mid]; simp only [applyTransitionTM]
        simp only [c₄₅, Cfg.mk.injEq]
        refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
        by_cases hi : i = utmSimTape
        · subst hi; simp only [↓reduceIte]; exact hsim_wam_2
        · simp only [hi, ↓reduceIte]
          have : c_mid.work i = c_s.work i := hcm_other i hi
          rw [this]; exact hw_idle i hi
      -- Provide witness and prove postconditions
      refine ⟨c₄₅,
        reachesIn.step hstep_1 (reachesIn.step hstep_2 reachesIn.zero),
        rfl, ?_, ?_, ?_, rfl, rfl, ?_⟩
      · -- Sim head = offset + 2
        simp [c₄₅]
      · -- Cells preserved except at offset+1 and offset+2
        intro j hj1 hj2
        simp only [c₄₅, ↓reduceIte]
        rw [Function.update_of_ne (by omega : j ≠ offset + 2)]
        simp only [c_mid, ↓reduceIte]
        rw [Function.update_of_ne (by omega : j ≠ offset + 1)]
      · -- Other tapes preserved
        intro i hi; simp [c₄₅, hi]
      · -- WorkTapesWF
        constructor
        · intro i; by_cases hi : i = utmSimTape
          · simp [c₄₅, hi]
            simp [c_mid]
            exact hwf_s.1 utmSimTape
          · simp [c₄₅, hi]; exact hwf_s.1 i
        · intro i j hj; by_cases hi : i = utmSimTape
          · subst hi; simp only [c₄₅, ↓reduceIte]
            by_cases hj2 : j = offset + 2
            · subst hj2; simp
              cases sLo <;> simp
            · rw [Function.update_of_ne hj2]
              simp only [c_mid, ↓reduceIte]
              by_cases hj1 : j = offset + 1
              · subst hj1; simp
                cases sHi <;> simp
              · rw [Function.update_of_ne hj1]; exact hwf_s.2 utmSimTape j hj
          · simp [c₄₅, hi]; exact hwf_s.2 i j hj
    obtain ⟨c₄₅, hreach₄₅, hst₄₅, hsimh₄₅, hsimcells₄₅,
            hother₄₅, hinp₄₅, hout₄₅, hwf₄₅⟩ := hsteps_45
    -- ── Step 6: rwWr rewind → rwWrR (variable steps, using helper) ──
    have hother_rw_pre : ∀ i : Fin 4, i ≠ utmSimTape → (c₄₅.work i).head ≥ 1 := by
      intro i hi; rw [hother₄₅ i hi, hother_s i hi]
      by_cases hi' : i = utmScratchTape
      · rw [hi']; exact hheads₁₂ utmScratchTape
      · rw [hother₁₂ i hi' hi]; exact hw_heads i
    obtain ⟨c_rw, hreach_rw, hst_rw, hsimh_rw, hsimcells_rw,
            hother_rw, hinp_rw, hout_rw, hwf_rw⟩ :=
      phase1_rwWr_loop k ⟨wrIdx, hwi⟩ (offset + 2) c₄₅ hst₄₅ hsimh₄₅ hwf₄₅
        hother_rw_pre
        (by rw [hinp₄₅, hinp_s, hinp₁₂]; exact hinp')
        (by rw [hinp₄₅, hinp_s, hinp₁₂]; exact hinp_h')
        (by rw [hout₄₅, hout_s, hout₁₂]; exact hout')
        (by rw [hout₄₅, hout_s, hout₁₂]; exact hout_h')
    -- ── Step 7: rwWrR → next (1 fixed step) ──
    have hstep_7 : ∃ c_end,
        (applyTransitionTM (n := n) k).step c_rw = some c_end ∧
        c_end.state = (if h : wrIdx + 1 < n + 1
          then ApplyTransQ.rdWrHi ⟨wrIdx + 1, h⟩
          else ApplyTransQ.rdMvHi ⟨0, by omega⟩) ∧
        (∀ i, c_end.work i = c_rw.work i) ∧
        c_end.input = c_rw.input ∧ c_end.output = c_rw.output ∧
        WorkTapesWF c_end.work := by
      have hne : c_rw.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        rw [hst_rw]; simp [applyTransitionTM]
      have hrw_heads : ∀ i : Fin 4, (c_rw.work i).head ≥ 1 := by
        intro i; by_cases hi : i = utmSimTape
        · rw [hi, hsimh_rw]
        · rw [hother_rw i hi]; exact hother_rw_pre i hi
      have hw_ns : ∀ i, (c_rw.work i).read ≠ Γ.start :=
        fun i => at_read_ne_start _ (hrw_heads i) (hwf_rw.2 i)
      have hw_idle : ∀ i, (c_rw.work i).writeAndMove
          ((readBackWrite ((c_rw.work i).read)).toΓ) (idleDir ((c_rw.work i).read)) = c_rw.work i :=
        fun i => tape_idle_preserve _ (hw_ns i) (hrw_heads i)
      have hinp_idle : c_rw.input.move (idleDir c_rw.input.read) = c_rw.input := by
        simp only [idleDir, show c_rw.input.read ≠ Γ.start from by
          rw [hinp_rw, hinp₄₅, hinp_s, hinp₁₂]; exact hinp', ↓reduceIte, Tape.move]
      have hout_idle : c_rw.output.writeAndMove ((readBackWrite c_rw.output.read).toΓ)
          (idleDir c_rw.output.read) = c_rw.output :=
        tape_idle_preserve _ (by rw [hout_rw, hout₄₅, hout_s, hout₁₂]; exact hout')
          (by rw [hout_rw, hout₄₅, hout_s, hout₁₂]; exact hout_h')
      set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := if h : wrIdx + 1 < n + 1
                    then ApplyTransQ.rdWrHi ⟨wrIdx + 1, h⟩
                    else ApplyTransQ.rdMvHi ⟨0, by omega⟩
          input := c_rw.input
          work := c_rw.work
          output := c_rw.output }
      have hstep : (applyTransitionTM (n := n) k).step c_rw = some c' := by
        simp only [TM.step, hne, ↓reduceIte]
        congr 1; rw [hst_rw]; simp only [applyTransitionTM]
        simp only [c', Cfg.mk.injEq]
        by_cases hw : (⟨wrIdx, hwi⟩ : Fin (n + 1)).val + 1 < n + 1 <;>
          simp only [hw, ↓reduceDIte]
        · exact ⟨trivial, hinp_idle, funext hw_idle, hout_idle⟩
        · exact ⟨trivial, hinp_idle, funext hw_idle, hout_idle⟩
      exact ⟨c', hstep, rfl, fun i => by simp [c'], rfl, rfl, hwf_rw⟩
    obtain ⟨c_end, hstep_end, hst_end, hwork_end, hinp_end, hout_end, hwf_end⟩ := hstep_7
    -- ── Compose all segments ──
    have htotal := reachesIn_trans _ hreach₁₂
      (reachesIn_trans _ hreach_s
      (reachesIn_trans _ hreach₄₅
      (reachesIn_trans _ hreach_rw
      (reachesIn.step hstep_end reachesIn.zero))))
    -- ── Marker preservation (mod 3 argument) ──
    have hmarkers_end : ∀ p t,
        (c_end.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) := by
      intro p t
      rw [hwork_end utmSimTape, hsimcells_rw]
      -- After rewind, sim cells match c₄₅. After write, unchanged at marker positions.
      have h1 : SuperCell.simTapeOffset (n + 2) p t ≠ offset + 1 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm p 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        omega
      have h2 : SuperCell.simTapeOffset (n + 2) p t ≠ offset + 2 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm p 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        omega
      rw [hsimcells₄₅ _ h1 h2, hsimcells_s, hsim₁₂]
      exact hmarkers p t
    -- ── Heads ≥ 1 ──
    have hheads_end : ∀ i : Fin 4, (c_end.work i).head ≥ 1 := by
      intro i; rw [show c_end.work i = c_rw.work i from hwork_end i]
      by_cases hi : i = utmSimTape
      · rw [hi, hsimh_rw]
      · rw [hother_rw i hi, hother₄₅ i hi, hother_s i hi]
        by_cases hi' : i = utmScratchTape
        · rw [hi']; exact hheads₁₂ utmScratchTape
        · rw [hother₁₂ i hi' hi]; exact hw_heads i
    -- ── Desc tape preserved ──
    have hdesc_end : c_end.work utmDescTape = c₁.work utmDescTape := by
      have hne_sim : utmDescTape ≠ utmSimTape := by decide
      have hne_scr : utmDescTape ≠ utmScratchTape := by decide
      rw [show c_end.work utmDescTape = c_rw.work utmDescTape from hwork_end utmDescTape,
          hother_rw utmDescTape hne_sim, hother₄₅ utmDescTape hne_sim,
          hother_s utmDescTape hne_sim, hother₁₂ utmDescTape hne_scr hne_sim, hdesc]
    -- ── State tape cells preserved ──
    have hstatecells_end : (c_end.work utmStateTape).cells =
        (c₁.work utmStateTape).cells := by
      have hne_sim : utmStateTape ≠ utmSimTape := by decide
      have hne_scr : utmStateTape ≠ utmScratchTape := by decide
      rw [show (c_end.work utmStateTape).cells = (c_rw.work utmStateTape).cells from
        congr_arg Tape.cells (hwork_end utmStateTape)]
      rw [hother_rw utmStateTape hne_sim, hother₄₅ utmStateTape hne_sim,
          hother_s utmStateTape hne_sim, hother₁₂ utmStateTape hne_scr hne_sim, hstatecells]
    -- ── Input/output preserved ──
    have hinp_end_c₁ : c_end.input = c₁.input := by
      rw [show c_end.input = c_rw.input from hinp_end,
          hinp_rw, hinp₄₅, hinp_s, hinp₁₂, hinp_eq]
    have hout_end_c₁ : c_end.output = c₁.output := by
      rw [show c_end.output = c_rw.output from hout_end,
          hout_rw, hout₄₅, hout_s, hout₁₂, hout_eq]
    -- ── Scratch cells WF ──
    have hscr_end : ∀ j, j ≥ 1 → (c_end.work utmScratchTape).cells j ≠ Γ.start := by
      intro j hj
      have hne : utmScratchTape ≠ utmSimTape := by decide
      rw [show c_end.work utmScratchTape = c_rw.work utmScratchTape from hwork_end utmScratchTape,
          hother_rw utmScratchTape hne, hother₄₅ utmScratchTape hne,
          hother_s utmScratchTape hne]
      exact hscr₁₂ j hj
    -- ── Assembly ──
    exact ⟨_, c_end, htotal, hst_end,
      by rw [show c_end.work utmSimTape = c_rw.work utmSimTape from hwork_end utmSimTape,
             hsimh_rw],
      hmarkers_end, hwf_end, hdesc_end, hstatecells_end,
      hinp_end_c₁, hout_end_c₁, hheads_end, hscr_end⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: move head markers on sim tape
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 2: processes n+2 tapes (input, work 0..n-1, output), moving head markers.
    Reads 2 bits per tape from scratch (the Dir3 encoding), scans sim tape for
    the head marker, clears it, steps 3*(n+2) cells in the given direction,
    and writes the new marker. -/
private theorem phase2_moveHeads {Q : Type} [DecidableEq Q]
    (c₂ : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (simCfg : Cfg n Q) (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3)
    (hstate : c₂.state = ApplyTransQ.rdMvHi ⟨0, by omega⟩)
    (hwf : WorkTapesWF c₂.work)
    (hsim_h : (c₂.work utmSimTape).head = 1)
    (hinp : c₂.input.read ≠ Γ.start) (hinp_h : c₂.input.head ≥ 1)
    (hout : c₂.output.read ≠ Γ.start) (hout_h : c₂.output.head ≥ 1) :
    ∃ steps c₃,
      (applyTransitionTM (n := n) k).reachesIn steps c₂ c₃ ∧
      c₃.state = ApplyTransQ.clrScr ∧
      (c₃.work utmSimTape).head = 1 ∧
      c₃.work utmDescTape = c₂.work utmDescTape ∧
      (c₃.work utmStateTape).cells = (c₂.work utmStateTape).cells ∧
      c₃.input = c₂.input ∧ c₃.output = c₂.output ∧
      WorkTapesWF c₃.work ∧
      (∀ i : Fin 4, (c₃.work i).head ≥ 1) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3: cleanup — clear scratch, rewind all tapes
-- ════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
private theorem phase3_clrScr_loop (k : ℕ) :
    ∀ (h : ℕ) (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
    c.state = ApplyTransQ.clrScr →
    (c.work utmScratchTape).head = h →
    WorkTapesWF c.work →
    (∀ i : Fin 4, i ≠ utmScratchTape → (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      (applyTransitionTM (n := n) k).reachesIn (h + 1) c c' ∧
      c'.state = ApplyTransQ.rwTp ⟨0, by omega⟩ ∧
      (c'.work utmScratchTape).head = 1 ∧
      (∀ i : Fin 4, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro h
  induction h with
  | zero =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hread : (c.work utmScratchTape).read = Γ.start := by
      simp only [Tape.read, hhead]; exact hwf.1 utmScratchTape
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmScratchTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmScratchTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have hscr_wam : (c.work utmScratchTape).writeAndMove
        ((readBackWrite ((c.work utmScratchTape).read)).toΓ) Dir3.right =
        ⟨1, (c.work utmScratchTape).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.write, hhead, ↓reduceIte, Tape.move]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwTp ⟨0, by omega⟩
        input := c.input
        work := fun i => if i = utmScratchTape then ⟨1, (c.work utmScratchTape).cells⟩
                         else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmScratchTape
      · subst hi; simp only [↓reduceIte]; exact hscr_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    exact ⟨c', reachesIn.step hstep reachesIn.zero, rfl,
      by simp [c'],
      fun i hi => by simp [c', hi],
      rfl, rfl,
      ⟨fun i => by
        by_cases hi : i = utmScratchTape
        · simp [c', hi, hwf.1 utmScratchTape]
        · simp [c', hi, hwf.1 i],
       fun i j hj => by
        by_cases hi : i = utmScratchTape
        · simp [c', hi, hwf.2 utmScratchTape j hj]
        · simp [c', hi, hwf.2 i j hj]⟩⟩
  | succ h ih =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hscr_ge1 : (c.work utmScratchTape).head ≥ 1 := by omega
    have hread_ne : (c.work utmScratchTape).read ≠ Γ.start :=
      at_read_ne_start _ hscr_ge1 (hwf.2 utmScratchTape)
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ utmScratchTape → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ utmScratchTape →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    set newScrCells := Function.update (c.work utmScratchTape).cells (h + 1) Γ.blank
    have hscr_wam : (c.work utmScratchTape).writeAndMove (Γw.blank.toΓ) Dir3.left =
        ⟨h, newScrCells⟩ := by
      have h_ne0 : ¬ (h + 1 = 0) := by omega
      simp only [Tape.writeAndMove, Tape.write, hhead, h_ne0, ↓reduceIte, Tape.move,
        newScrCells, Γw.toΓ, Nat.add_sub_cancel]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.clrScr
        input := c.input
        work := fun i => if i = utmScratchTape then ⟨h, newScrCells⟩
                         else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread_ne, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = utmScratchTape
      · subst hi; simp only [↓reduceIte]; exact hscr_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    have hc'_state : c'.state = ApplyTransQ.clrScr := rfl
    have hc'_head : (c'.work utmScratchTape).head = h := by
      simp [c']
    have hc'_other : ∀ i, i ≠ utmScratchTape → c'.work i = c.work i :=
      fun i hi => by simp [c', hi]
    have hc'_inp : c'.input = c.input := rfl
    have hc'_out : c'.output = c.output := rfl
    have hc'_wf : WorkTapesWF c'.work := by
      constructor
      · intro i; by_cases hi : i = utmScratchTape
        · simp only [c', hi, ↓reduceIte,
            newScrCells]
          rw [Function.update_apply]; split <;> [omega; exact hwf.1 utmScratchTape]
        · rw [hc'_other i hi]; exact hwf.1 i
      · intro i j hj; by_cases hi : i = utmScratchTape
        · simp only [c', hi, ↓reduceIte,
            newScrCells]
          rw [Function.update_apply]; split
          · simp
          · exact hwf.2 utmScratchTape j hj
        · rw [hc'_other i hi]; exact hwf.2 i j hj
    have hc'_hother : ∀ i, i ≠ utmScratchTape → (c'.work i).head ≥ 1 := by
      intro i hi; rw [hc'_other i hi]; exact hother i hi
    obtain ⟨c_f, hreach, hst_f, hhead_f, hother_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c' hc'_state hc'_head hc'_wf hc'_hother
        (by rw [hc'_inp]; exact hinp) (by rw [hc'_inp]; exact hinp_h)
        (by rw [hc'_out]; exact hout) (by rw [hc'_out]; exact hout_h)
    exact ⟨c_f, reachesIn.step hstep hreach, hst_f, hhead_f,
      fun i hi => by rw [hother_f i hi, hc'_other i hi],
      by rw [hinp_f, hc'_inp], by rw [hout_f, hc'_out], hwf_f⟩

set_option maxHeartbeats 800000 in
private theorem phase3_rwTp_loop (k : ℕ) (t : Fin 4) :
    ∀ (h : ℕ) (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
    c.state = ApplyTransQ.rwTp t →
    (c.work t).head = h →
    WorkTapesWF c.work →
    (∀ i : Fin 4, i ≠ t → (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      (applyTransitionTM (n := n) k).reachesIn (h + 1) c c' ∧
      c'.state = ApplyTransQ.rwTpR t ∧
      (c'.work t).head = 1 ∧
      (c'.work t).cells = (c.work t).cells ∧
      (∀ i : Fin 4, i ≠ t → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro h
  induction h with
  | zero =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hread : (c.work t).read = Γ.start := by
      simp only [Tape.read, hhead]; exact hwf.1 t
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ t → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ t →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have ht_wam : (c.work t).writeAndMove
        ((readBackWrite ((c.work t).read)).toΓ) Dir3.right =
        ⟨1, (c.work t).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.write, hhead, ↓reduceIte, Tape.move]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwTpR t
        input := c.input
        work := fun i => if i = t then ⟨1, (c.work t).cells⟩ else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = t
      · subst hi; simp only [↓reduceIte]; exact ht_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    exact ⟨c', reachesIn.step hstep reachesIn.zero, rfl,
      by simp [c'],
      by simp [c'],
      fun i hi => by simp [c', hi],
      rfl, rfl,
      ⟨fun i => by
        by_cases hi : i = t
        · simp [c', hi, hwf.1 t]
        · simp [c', hi, hwf.1 i],
       fun i j hj => by
        by_cases hi : i = t
        · simp [c', hi, hwf.2 t j hj]
        · simp [c', hi, hwf.2 i j hj]⟩⟩
  | succ h ih =>
    intro c hst hhead hwf hother hinp hinp_h hout hout_h
    have hhead_ne0 : ¬ (c.work t).head = 0 := by omega
    have ht_ge1 : (c.work t).head ≥ 1 := by omega
    have hread_ne : (c.work t).read ≠ Γ.start :=
      at_read_ne_start _ ht_ge1 (hwf.2 t)
    have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
      rw [hst]; simp [applyTransitionTM]
    have hw_ns : ∀ i, i ≠ t → (c.work i).read ≠ Γ.start :=
      fun i hi => at_read_ne_start _ (hother i hi) (hwf.2 i)
    have hw_idle : ∀ i, i ≠ t →
        (c.work i).writeAndMove ((readBackWrite ((c.work i).read)).toΓ)
          (idleDir ((c.work i).read)) = c.work i :=
      fun i hi => tape_idle_preserve _ (hw_ns i hi) (hother i hi)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp, ↓reduceIte, Tape.move]
    have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
        (idleDir c.output.read) = c.output :=
      tape_idle_preserve _ hout hout_h
    have h_ne0 : ¬ (h + 1 = 0) := by omega
    have hread_eq : (c.work t).read = (c.work t).cells (h + 1) := by
      simp [Tape.read, hhead]
    have hcell_ns : (c.work t).cells (h + 1) ≠ Γ.start := hread_eq ▸ hread_ne
    have ht_wam : (c.work t).writeAndMove
        ((readBackWrite ((c.work t).read)).toΓ) Dir3.left =
        ⟨h, (c.work t).cells⟩ := by
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hhead, h_ne0, ↓reduceIte,
        hread_eq, readBackWrite_toΓ_eq hcell_ns, Function.update_eq_self, Nat.add_sub_cancel]
    set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
      { state := ApplyTransQ.rwTp t
        input := c.input
        work := fun i => if i = t then ⟨h, (c.work t).cells⟩ else c.work i
        output := c.output }
    have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
      simp only [TM.step, hne, ↓reduceIte]
      congr 1; rw [hst]; simp only [applyTransitionTM, hread_ne, ↓reduceIte]
      simp only [c', Cfg.mk.injEq]
      refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
      by_cases hi : i = t
      · subst hi; simp only [↓reduceIte]; exact ht_wam
      · simp only [hi, ↓reduceIte]; exact hw_idle i hi
    have hc'_other : ∀ i, i ≠ t → c'.work i = c.work i :=
      fun i hi => by simp [c', hi]
    have hc'_cells : (c'.work t).cells = (c.work t).cells := by
      simp [c']
    have hc'_wf : WorkTapesWF c'.work := by
      constructor
      · intro i; by_cases hi : i = t
        · simp [c', hi, hwf.1 t]
        · rw [hc'_other i hi]; exact hwf.1 i
      · intro i j hj; by_cases hi : i = t
        · simp [c', hi]; exact hwf.2 t j hj
        · rw [hc'_other i hi]; exact hwf.2 i j hj
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hother_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c' (by simp [c']) (by simp [c']) hc'_wf
        (fun i hi => by rw [hc'_other i hi]; exact hother i hi)
        (by simp [c']; exact hinp) (by simp [c']; exact hinp_h)
        (by simp [c']; exact hout) (by simp [c']; exact hout_h)
    exact ⟨c_f, reachesIn.step hstep hreach, hst_f, hhead_f,
      by rw [hcells_f, hc'_cells],
      fun i hi => by rw [hother_f i hi, hc'_other i hi],
      by rw [hinp_f], by rw [hout_f], hwf_f⟩

set_option maxHeartbeats 800000 in
private theorem phase3_rwTpR_step (k : ℕ) (t : Fin 4)
    (c : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (hst : c.state = ApplyTransQ.rwTpR t)
    (hwf : WorkTapesWF c.work)
    (hw_h : ∀ i : Fin 4, (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start) (_hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1) :
    ∃ c',
      (applyTransitionTM (n := n) k).step c = some c' ∧
      c'.state = (if h : t.val + 1 < 4
                   then ApplyTransQ.rwTp ⟨t.val + 1, h⟩
                   else ApplyTransQ.done) ∧
      (∀ i, c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  have hne : c.state ≠ (applyTransitionTM (n := n) k).qhalt := by
    rw [hst]; simp [applyTransitionTM]
  have hw_ns : ∀ i, (c.work i).read ≠ Γ.start :=
    fun i => at_read_ne_start _ (hw_h i) (hwf.2 i)
  have hw_idle : ∀ i, (c.work i).writeAndMove
      ((readBackWrite ((c.work i).read)).toΓ) (idleDir ((c.work i).read)) = c.work i :=
    fun i => tape_idle_preserve _ (hw_ns i) (hw_h i)
  have hinp_idle : c.input.move (idleDir c.input.read) = c.input := by
    simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  have hout_idle : c.output.writeAndMove ((readBackWrite c.output.read).toΓ)
      (idleDir c.output.read) = c.output :=
    tape_idle_preserve _ hout hout_h
  set c' : Cfg 4 (applyTransitionTM (n := n) k).Q :=
    { state := if h : t.val + 1 < 4
                then ApplyTransQ.rwTp ⟨t.val + 1, h⟩
                else ApplyTransQ.done
      input := c.input
      work := c.work
      output := c.output }
  have hstep : (applyTransitionTM (n := n) k).step c = some c' := by
    simp only [TM.step, hne, ↓reduceIte]
    congr 1; rw [hst]; simp only [applyTransitionTM]
    simp only [c', Cfg.mk.injEq]
    by_cases ht4 : t.val + 1 < 4 <;> simp only [ht4, ↓reduceDIte]
    · exact ⟨trivial, hinp_idle, funext hw_idle, hout_idle⟩
    · exact ⟨trivial, hinp_idle, funext hw_idle, hout_idle⟩
  exact ⟨c', hstep, rfl, fun i => by simp [c'], rfl, rfl, hwf⟩

set_option maxHeartbeats 1600000 in
private theorem phase3_cleanup
    (c₃ : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (hstate : c₃.state = ApplyTransQ.clrScr)
    (hwf : WorkTapesWF c₃.work)
    (hw_h : ∀ i : Fin 4, (c₃.work i).head ≥ 1)
    (hinp : c₃.input.read ≠ Γ.start) (hinp_h : c₃.input.head ≥ 1)
    (hout : c₃.output.read ≠ Γ.start) (hout_h : c₃.output.head ≥ 1) :
    ∃ steps c₄,
      (applyTransitionTM (n := n) k).reachesIn steps c₃ c₄ ∧
      (applyTransitionTM (n := n) k).halted c₄ ∧
      (∀ i, (c₄.work i).head = 1) ∧
      (∀ i, i ≠ utmScratchTape → (c₄.work i).cells = (c₃.work i).cells) ∧
      c₄.input = c₃.input ∧ c₄.output = c₃.output ∧
      WorkTapesWF c₄.work := by
  -- Phase 3a: clear scratch tape
  obtain ⟨ca, hreach_a, hst_a, hscr_h_a, hother_a, hinp_a, hout_a, hwf_a⟩ :=
    phase3_clrScr_loop k ((c₃.work utmScratchTape).head) c₃ hstate rfl hwf
      (fun i hi => hw_h i) hinp hinp_h hout hout_h
  have hw_h_a : ∀ i : Fin 4, (ca.work i).head ≥ 1 := by
    intro i; by_cases hi : i = utmScratchTape
    · rw [hi]; omega
    · rw [hother_a i hi]; exact hw_h i
  -- Phase 3b: rewind tape 0 (desc)
  obtain ⟨cb, hreach_b, hst_b, hhead_b, hcells_b, hother_b, hinp_b, hout_b, hwf_b⟩ :=
    phase3_rwTp_loop k ⟨0, by omega⟩ ((ca.work ⟨0, by omega⟩).head) ca hst_a rfl hwf_a
      (fun i hi => hw_h_a i) (by rw [hinp_a]; exact hinp) (by rw [hinp_a]; exact hinp_h)
      (by rw [hout_a]; exact hout) (by rw [hout_a]; exact hout_h)
  have hw_h_b : ∀ i : Fin 4, (cb.work i).head ≥ 1 := by
    intro i; by_cases hi : i = ⟨0, by omega⟩
    · rw [hi]; omega
    · rw [hother_b i hi]; exact hw_h_a i
  obtain ⟨cb', hstep_b', hst_b', hw_b', hinp_b', hout_b', hwf_b'⟩ :=
    phase3_rwTpR_step k ⟨0, by omega⟩ cb hst_b hwf_b hw_h_b
      (by rw [hinp_b, hinp_a]; exact hinp) (by rw [hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_b, hout_a]; exact hout) (by rw [hout_b, hout_a]; exact hout_h)
  have hst_b'_val : cb'.state = ApplyTransQ.rwTp ⟨1, by omega⟩ := by rw [hst_b']; simp
  have hw_h_b' : ∀ i : Fin 4, (cb'.work i).head ≥ 1 := fun i => by rw [hw_b' i]; exact hw_h_b i
  -- Phase 3c: rewind tape 1 (state)
  obtain ⟨cc, hreach_c, hst_c, hhead_c, hcells_c, hother_c, hinp_c, hout_c, hwf_c⟩ :=
    phase3_rwTp_loop k ⟨1, by omega⟩ ((cb'.work ⟨1, by omega⟩).head) cb' hst_b'_val rfl hwf_b'
      (fun i hi => hw_h_b' i) (by rw [hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_b', hout_b, hout_a]; exact hout_h)
  have hw_h_c : ∀ i : Fin 4, (cc.work i).head ≥ 1 := by
    intro i; by_cases hi : i = ⟨1, by omega⟩
    · rw [hi]; omega
    · rw [hother_c i hi]; exact hw_h_b' i
  obtain ⟨cc', hstep_c', hst_c', hw_c', hinp_c', hout_c', hwf_c'⟩ :=
    phase3_rwTpR_step k ⟨1, by omega⟩ cc hst_c hwf_c hw_h_c
      (by rw [hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_c, hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_c, hout_b', hout_b, hout_a]; exact hout_h)
  have hst_c'_val : cc'.state = ApplyTransQ.rwTp ⟨2, by omega⟩ := by rw [hst_c']; simp
  have hw_h_c' : ∀ i : Fin 4, (cc'.work i).head ≥ 1 := fun i => by rw [hw_c' i]; exact hw_h_c i
  -- Phase 3d: rewind tape 2 (sim)
  obtain ⟨cd, hreach_d, hst_d, hhead_d, hcells_d, hother_d, hinp_d, hout_d, hwf_d⟩ :=
    phase3_rwTp_loop k ⟨2, by omega⟩ ((cc'.work ⟨2, by omega⟩).head) cc' hst_c'_val rfl hwf_c'
      (fun i hi => hw_h_c' i) (by rw [hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout_h)
  have hw_h_d : ∀ i : Fin 4, (cd.work i).head ≥ 1 := by
    intro i; by_cases hi : i = ⟨2, by omega⟩
    · rw [hi]; omega
    · rw [hother_d i hi]; exact hw_h_c' i
  obtain ⟨cd', hstep_d', hst_d', hw_d', hinp_d', hout_d', hwf_d'⟩ :=
    phase3_rwTpR_step k ⟨2, by omega⟩ cd hst_d hwf_d hw_h_d
      (by rw [hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout_h)
  have hst_d'_val : cd'.state = ApplyTransQ.rwTp ⟨3, by omega⟩ := by rw [hst_d']; simp
  have hw_h_d' : ∀ i : Fin 4, (cd'.work i).head ≥ 1 := fun i => by rw [hw_d' i]; exact hw_h_d i
  -- Phase 3e: rewind tape 3 (scratch)
  obtain ⟨ce, hreach_e, hst_e, hhead_e, hcells_e, hother_e, hinp_e, hout_e, hwf_e⟩ :=
    phase3_rwTp_loop k ⟨3, by omega⟩ ((cd'.work ⟨3, by omega⟩).head) cd' hst_d'_val rfl hwf_d'
      (fun i hi => hw_h_d' i)
      (by rw [hinp_d', hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_d', hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_d', hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_d', hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout_h)
  have hw_h_e : ∀ i : Fin 4, (ce.work i).head ≥ 1 := by
    intro i; by_cases hi : i = ⟨3, by omega⟩
    · rw [hi]; omega
    · rw [hother_e i hi]; exact hw_h_d' i
  obtain ⟨ce', hstep_e', hst_e', hw_e', hinp_e', hout_e', hwf_e'⟩ :=
    phase3_rwTpR_step k ⟨3, by omega⟩ ce hst_e hwf_e hw_h_e
      (by rw [hinp_e, hinp_d', hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp)
      (by rw [hinp_e, hinp_d', hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]; exact hinp_h)
      (by rw [hout_e, hout_d', hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout)
      (by rw [hout_e, hout_d', hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]; exact hout_h)
  have hst_e'_done : ce'.state = ApplyTransQ.done := by rw [hst_e']; simp
  -- Assemble
  have htotal := reachesIn_trans _ hreach_a
    (reachesIn_trans _ hreach_b (reachesIn.step hstep_b'
    (reachesIn_trans _ hreach_c (reachesIn.step hstep_c'
    (reachesIn_trans _ hreach_d (reachesIn.step hstep_d'
    (reachesIn_trans _ hreach_e (reachesIn.step hstep_e' reachesIn.zero))))))))
  -- Fin inequality helper
  have fne : ∀ (a b : ℕ) (ha : a < 4) (hb : b < 4), a ≠ b →
      (⟨a, ha⟩ : Fin 4) ≠ ⟨b, hb⟩ := by
    intro a b _ _ hab h; exact hab (Fin.mk.inj h)
  have hheads : ∀ i, (ce'.work i).head = 1 := by
    intro ⟨i, hi⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [hw_e' ⟨0, by omega⟩, hother_e ⟨0, by omega⟩ (fne 0 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨0, by omega⟩, hother_d ⟨0, by omega⟩ (fne 0 2 (by omega) (by omega) (by omega)),
          hw_c' ⟨0, by omega⟩, hother_c ⟨0, by omega⟩ (fne 0 1 (by omega) (by omega) (by omega)),
          hw_b' ⟨0, by omega⟩]; exact hhead_b
    · rw [hw_e' ⟨1, by omega⟩, hother_e ⟨1, by omega⟩ (fne 1 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨1, by omega⟩, hother_d ⟨1, by omega⟩ (fne 1 2 (by omega) (by omega) (by omega)),
          hw_c' ⟨1, by omega⟩]; exact hhead_c
    · rw [hw_e' ⟨2, by omega⟩, hother_e ⟨2, by omega⟩ (fne 2 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨2, by omega⟩]; exact hhead_d
    · rw [hw_e' ⟨3, by omega⟩]; exact hhead_e
  have hcells : ∀ i, i ≠ utmScratchTape → (ce'.work i).cells = (c₃.work i).cells := by
    intro ⟨i, hi⟩ hne
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [hw_e' ⟨0, by omega⟩, hother_e ⟨0, by omega⟩ (fne 0 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨0, by omega⟩, hother_d ⟨0, by omega⟩ (fne 0 2 (by omega) (by omega) (by omega)),
          hw_c' ⟨0, by omega⟩, hother_c ⟨0, by omega⟩ (fne 0 1 (by omega) (by omega) (by omega)),
          hw_b' ⟨0, by omega⟩, hcells_b,
          hother_a ⟨0, by omega⟩ (fne 0 3 (by omega) (by omega) (by omega))]
    · rw [hw_e' ⟨1, by omega⟩, hother_e ⟨1, by omega⟩ (fne 1 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨1, by omega⟩, hother_d ⟨1, by omega⟩ (fne 1 2 (by omega) (by omega) (by omega)),
          hw_c' ⟨1, by omega⟩, hcells_c,
          hw_b' ⟨1, by omega⟩, hother_b ⟨1, by omega⟩ (fne 1 0 (by omega) (by omega) (by omega)),
          hother_a ⟨1, by omega⟩ (fne 1 3 (by omega) (by omega) (by omega))]
    · rw [hw_e' ⟨2, by omega⟩, hother_e ⟨2, by omega⟩ (fne 2 3 (by omega) (by omega) (by omega)),
          hw_d' ⟨2, by omega⟩, hcells_d,
          hw_c' ⟨2, by omega⟩, hother_c ⟨2, by omega⟩ (fne 2 1 (by omega) (by omega) (by omega)),
          hw_b' ⟨2, by omega⟩, hother_b ⟨2, by omega⟩ (fne 2 0 (by omega) (by omega) (by omega)),
          hother_a ⟨2, by omega⟩ (fne 2 3 (by omega) (by omega) (by omega))]
    · exact absurd rfl hne
  have hinp_final : ce'.input = c₃.input := by
    rw [hinp_e', hinp_e, hinp_d', hinp_d, hinp_c', hinp_c, hinp_b', hinp_b, hinp_a]
  have hout_final : ce'.output = c₃.output := by
    rw [hout_e', hout_e, hout_d', hout_d, hout_c', hout_c, hout_b', hout_b, hout_a]
  exact ⟨_, ce', htotal, hst_e'_done, hheads, hcells, hinp_final, hout_final, hwf_e'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Encoding connection: scratchHasTransOutput → per-phase scratch bits
-- ════════════════════════════════════════════════════════════════════════

/-- The first k bits of encodeTransOutput are the one-hot encoding of q'. -/
private theorem encodeTransOutput_state_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (j : ℕ) (hj : j < k') :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[j]? =
      some (j == q'.val) := by
  simp [TMEncoding.encodeTransOutput, List.getElem?_append_left, hj]
  exact Fin.ext_iff

-- ════════════════════════════════════════════════════════════════════════
-- Full HoareTime proof
-- ════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
/-- HoareTime specification for `applyTransitionTM`.
    Chains four phases: writeState, write symbols, move heads, cleanup. -/
theorem applyTransitionTM_hoareTime_proof {tm : TM n} (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (simCfg : Cfg n tm.Q) (hNotHalted : simCfg.state ≠ tm.qhalt) :
    let e := tm.stateEquivK hk
    let iHead := simCfg.input.read
    let wHeads := fun i => (simCfg.work i).read
    let oHead := simCfg.output.read
    let (q', wW, oW, iD, wD, oD) := tm.δ simCfg.state iHead wHeads oHead
    ∃ B, (applyTransitionTM (n := n) k).HoareTime
      (fun inp work out =>
        stateOnTapeAt k (e simCfg.state) (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        descOnTape desc (work utmDescTape) ∧
        WorkTapesWF work ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        (work utmDescTape).head = 1 ∧
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1)
      (fun _inp work _out =>
        let simCfg' : Cfg n tm.Q :=
          ⟨q', simCfg.input.move iD,
           fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
           simCfg.output.writeAndMove oW.toΓ oD⟩
        stateOnTapeAt k (e q') (work utmStateTape) ∧
        superCellsCorrect simCfg' (work utmSimTape) ∧
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  intro e iHead wHeads oHead
  set δ_result := tm.δ simCfg.state iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δ_result
  -- Unfold HoareTime: ∃ B, ∀ inp work out, pre → ∃ c' t, t ≤ B ∧ ...
  -- Provide time bound (existential, computed from phase bounds)
  refine ⟨sorry, ?_⟩
  intro inp work out hpre
  obtain ⟨hstateOnTape, hsuperCells, hscratchTrans, hdescOnTape, hwf,
          hstate_head, hsim_head, hdesc_head, hinp_ns, hinp_h, hout_ns, hout_h⟩ := hpre
  -- Build initial config
  set c₀ : Cfg 4 (applyTransitionTM (n := n) k).Q :=
    { state := (applyTransitionTM k).qstart
      input := inp
      work := work
      output := out } with hc₀_def
  have hc₀_state : c₀.state = ApplyTransQ.writeState ⟨k, by omega⟩ := rfl
  -- Extract scratch tape properties from scratchHasTransOutput
  have hscratch_head : (c₀.work utmScratchTape).head = 1 := hscratchTrans.2
  -- The first k scratch bits encode q' as one-hot
  have hscratch_state_bits : ∀ j, j < k → (c₀.work utmScratchTape).cells (1 + j) =
      if j = (e q').val then Γ.one else Γ.zero := by
    intro j hj
    obtain ⟨_, hbits, _⟩ := hscratchTrans.1
    have hlen : j < (TMEncoding.encodeTransOutput k n (e q') wW oW iD wD oD).length := by
      simp only [TMEncoding.encodeTransOutput, List.length_append, List.length_map,
        List.length_finRange]; omega
    rw [show 1 + j = j + 1 from by omega]; rw [hbits j hlen]
    have hget := encodeTransOutput_state_bits k n (e q') wW oW iD wD oD j hj
    simp only [List.getElem?_eq_getElem hlen] at hget
    injection hget with hget'
    rw [hget']; simp only [Γ.ofBool]
    split <;> simp_all
  -- State tape blank sentinel
  have hstate_blank : (c₀.work utmStateTape).cells (k + 1) = Γ.blank :=
    hstateOnTape.2.2
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 0: writeState — copy k state bits from scratch to state tape
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨c₁, hreach₁, hst₁, hbits₁, hblank₁, hcell0₁, hhead₁,
          hscc₁, hsch₁, hsim₁, hdesc₁, hinp₁, hout₁, hwf₁⟩ :=
    phase0_writeState c₀ (e q') hc₀_state hwf hstate_head hstate_blank
      hscratch_head hscratch_state_bits (by rw [hsim_head])
      (by rw [hdesc_head]) hinp_ns hinp_h hout_ns hout_h
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 1: write new symbols on sim tape
  -- ──────────────────────────────────────────────────────────────────
  have hc₁_sim_correct : superCellsCorrect simCfg (c₁.work utmSimTape) := by
    rw [hsim₁]; exact hsuperCells
  have hheads₁ : ∀ i : Fin 4, (c₁.work i).head ≥ 1 := by
    intro ⟨i, hi⟩
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · -- desc (0)
      show (c₁.work utmDescTape).head ≥ 1
      have := congr_arg Tape.head hdesc₁; dsimp [c₀] at this; omega
    · -- state (1)
      show (c₁.work utmStateTape).head ≥ 1; rw [hhead₁]; omega
    · -- sim (2)
      show (c₁.work utmSimTape).head ≥ 1
      have := congr_arg Tape.head hsim₁; dsimp [c₀] at this; omega
    · -- scratch (3)
      show (c₁.work utmScratchTape).head ≥ 1; rw [hsch₁]; omega
  obtain ⟨steps₂, c₂, hreach₂, hst₂, hsim_h₂, hdesc₂, hstatecells₂, hinp₂, hout₂, hwf₂, hheads₂⟩ :=
    phase1_writeSymbols c₁ simCfg wW oW hst₁ hwf₁
      hc₁_sim_correct (by rw [hsim₁]; exact hsim_head)
      hsch₁ (hwf₁.2 utmScratchTape)
      (by rw [hinp₁]; exact hinp_ns) (by rw [hinp₁]; exact hinp_h)
      (by rw [hout₁]; exact hout_ns) (by rw [hout₁]; exact hout_h)
      hheads₁
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 2: move head markers
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨steps₃, c₃, hreach₃, hst₃, hsim_h₃, hdesc₃, hstatecells₃, hinp₃, hout₃, hwf₃, hheads₃⟩ :=
    phase2_moveHeads c₂ simCfg iD wD oD hst₂ hwf₂ hsim_h₂
      (by rw [hinp₂, hinp₁]; exact hinp_ns) (by rw [hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₂, hout₁]; exact hout_ns) (by rw [hout₂, hout₁]; exact hout_h)
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 3: cleanup
  -- ──────────────────────────────────────────────────────────────────
  obtain ⟨steps₄, c₄, hreach₄, hhalted₄, hheads₄, hcells₄, hinp₄, hout₄, hwf₄⟩ :=
    phase3_cleanup c₃ hst₃ hwf₃ hheads₃
      (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_ns)
      (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₃, hout₂, hout₁]; exact hout_ns)
      (by rw [hout₃, hout₂, hout₁]; exact hout_h)
  -- ──────────────────────────────────────────────────────────────────
  -- Assemble the final result
  -- ──────────────────────────────────────────────────────────────────
  have htotal := reachesIn_trans _ hreach₁
    (reachesIn_trans _ hreach₂
    (reachesIn_trans _ hreach₃ hreach₄))
  -- Trace state tape cells back to c₁ (Phase 0 output)
  have hstate_cells_final : (c₄.work utmStateTape).cells =
      (c₁.work utmStateTape).cells := by
    rw [hcells₄ utmStateTape (by decide), hstatecells₃, hstatecells₂]
  -- Trace desc tape cells back to c₀
  have hdesc_cells_final : (c₄.work utmDescTape).cells =
      (c₀.work utmDescTape).cells := by
    have h := hcells₄ utmDescTape (by decide)
    rw [hdesc₃, hdesc₂, hdesc₁] at h; exact h
  refine ⟨c₄, _, sorry, htotal, hhalted₄, ?_, sorry, ?_,
    hheads₄ utmDescTape, hheads₄ utmStateTape, hheads₄ utmSimTape, hwf₄⟩
  · -- stateOnTapeAt k (e q') (c₄.work utmStateTape)
    refine ⟨?_, ?_, ?_⟩
    · rw [hstate_cells_final]; exact hcell0₁
    · intro j hj; rw [hstate_cells_final, show j + 1 = 1 + j from by omega]
      exact hbits₁ j hj
    · rw [hstate_cells_final]; exact hblank₁
  · -- descOnTape desc (c₄.work utmDescTape)
    obtain ⟨hd0, hdbits, hdblank⟩ := hdescOnTape
    refine ⟨?_, ?_, ?_⟩
    · rw [hdesc_cells_final]; exact hd0
    · intro i hi; rw [hdesc_cells_final]; exact hdbits i hi
    · rw [hdesc_cells_final]; exact hdblank

end TM
