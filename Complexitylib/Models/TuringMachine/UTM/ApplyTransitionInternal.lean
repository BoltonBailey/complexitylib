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
-- Super-cell encoding helpers
-- ════════════════════════════════════════════════════════════════════════

/-- symToSimHi writes the same Γ value as the first component of symToCellPair. -/
private theorem symToSimHi_toΓ_eq (w : Γw) :
    (symToSimHi w).toΓ = (SuperCell.symToCellPair w.toΓ).1 := by
  cases w <;> rfl

/-- symToSimLo writes the same Γ value as the second component of symToCellPair. -/
private theorem symToSimLo_toΓ_eq (w : Γw) :
    (symToSimLo w).toΓ = (SuperCell.symToCellPair w.toΓ).2 := by
  cases w <;> rfl

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
      (∀ i : Fin 4, (c₂.work i).head ≥ 1) ∧
      (∀ p t, (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t)) ∧
      (∀ j, j ≥ 1 → (c₂.work utmScratchTape).cells j ≠ Γ.start) ∧
      -- Scratch tracking (Part A)
      (c₂.work utmScratchTape).cells = (c₁.work utmScratchTape).cells ∧
      (c₂.work utmScratchTape).head = (c₁.work utmScratchTape).head + 2 * (n + 1) ∧
      -- Written symbol cells at head positions (Part B)
      (∀ wrIdx' (_ : wrIdx' < n + 1),
          let tapeIdx := wrIdx' + 1
          let h_target := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                          else simCfg.output.head
          let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
          (c₂.work utmSimTape).cells (base + 1) =
            (symToSimHi (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ ∧
          (c₂.work utmSimTape).cells (base + 2) =
            (symToSimLo (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ) ∧
      -- Preserved symbol cells at non-head positions (Part B)
      (∀ pos tapeIdx,
          tapeIdx < n + 2 →
          (tapeIdx = 0 ∨
           ∀ wrIdx', wrIdx' < n + 1 → tapeIdx = wrIdx' + 1 →
             pos ≠ (if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                    else simCfg.output.head)) →
          (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
          (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) := by
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
      -- Scratch tracking
      (c.work utmScratchTape).cells = (c₁.work utmScratchTape).cells →
      (c.work utmScratchTape).head = (c₁.work utmScratchTape).head + 2 * wrIdx →
      -- Already-processed writes
      (∀ wrIdx' (_ : wrIdx' < wrIdx),
          let tapeIdx := wrIdx' + 1
          let h_target := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                          else simCfg.output.head
          let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
          (c.work utmSimTape).cells (base + 1) =
            (symToSimHi (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ ∧
          (c.work utmSimTape).cells (base + 2) =
            (symToSimLo (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ) →
      -- Preserved +1/+2 cells for non-processed
      (∀ pos tapeIdx,
          tapeIdx < n + 2 →
          (tapeIdx = 0 ∨
           ∀ wrIdx', wrIdx' < wrIdx → tapeIdx = wrIdx' + 1 →
             pos ≠ (if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                    else simCfg.output.head)) →
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) →
      ∃ steps c₂,
        (applyTransitionTM (n := n) k).reachesIn steps c c₂ ∧
        c₂.state = ApplyTransQ.rdMvHi ⟨0, by omega⟩ ∧
        (c₂.work utmSimTape).head = 1 ∧
        c₂.work utmDescTape = c₁.work utmDescTape ∧
        (c₂.work utmStateTape).cells = (c₁.work utmStateTape).cells ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output ∧
        WorkTapesWF c₂.work ∧
        (∀ i : Fin 4, (c₂.work i).head ≥ 1) ∧
        (∀ p t, (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t) =
          (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p t)) ∧
        (∀ j, j ≥ 1 → (c₂.work utmScratchTape).cells j ≠ Γ.start) ∧
        (c₂.work utmScratchTape).cells = (c₁.work utmScratchTape).cells ∧
        (c₂.work utmScratchTape).head = (c₁.work utmScratchTape).head + 2 * (n + 1) ∧
        (∀ wrIdx' (_ : wrIdx' < n + 1),
            let tapeIdx := wrIdx' + 1
            let h_target := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                            else simCfg.output.head
            let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
            (c₂.work utmSimTape).cells (base + 1) =
              (symToSimHi (decodeΓw
                ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
                ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ ∧
            (c₂.work utmSimTape).cells (base + 2) =
              (symToSimLo (decodeΓw
                ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
                ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ) ∧
        (∀ pos tapeIdx,
            tapeIdx < n + 2 →
            (tapeIdx = 0 ∨
             ∀ wrIdx', wrIdx' < n + 1 → tapeIdx = wrIdx' + 1 →
               pos ≠ (if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                      else simCfg.output.head)) →
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
              (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
              (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) by
    exact outer (n + 1) 0 (by omega) c₁ (by omega) hstate hsim_h
      (fun _ _ => rfl) hwf rfl rfl rfl rfl hheads hscratch_wf
      rfl (by omega) (by intro _ h; omega)
      (by intro pos tapeIdx _ _; exact ⟨rfl, rfl⟩)
  intro fuel
  induction fuel with
  | zero => intro wrIdx hwi c hfuel; omega
  | succ m ih =>
    intro wrIdx hwi c hfuel hst hsimh hmarkers hwf' hdesc hstatecells
      hinp_eq hout_eq hw_heads hscr_wf
      hscr_cells hscr_head hprev_writes hprev_pres
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
    -- h_target matches the expected form
    have h_target_eq : h_target = (if hw : wrIdx < n then (simCfg.work ⟨wrIdx, hw⟩).head
                                    else simCfg.output.head) := by
      by_cases hwk : wrIdx < n
      · simp only [hwk, dite_true]
        have h1 := hmarker_vals h_target; simp at h1
        have h2 := (hsim_correct.2.2.1 ⟨wrIdx, hwk⟩ h_target).1
        rw [show wrIdx + 1 = tapeIdx from rfl] at h2; rw [h1] at h2
        by_cases heq : (simCfg.work ⟨wrIdx, hwk⟩).head = h_target
        · exact heq.symm
        · simp [heq] at h2
      · simp only [hwk, dite_false]
        have h1 := hmarker_vals h_target; simp at h1
        have h2 := (hsim_correct.2.2.2 h_target).1
        rw [show n + 1 = tapeIdx from by omega] at h2; rw [h1] at h2
        by_cases heq : simCfg.output.head = h_target
        · exact heq.symm
        · simp [heq] at h2
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
        (∀ j, j ≥ 1 → (c_t.work utmScratchTape).cells j ≠ Γ.start) ∧
        -- Scratch tracking
        (c_t.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (c_t.work utmScratchTape).head = (c.work utmScratchTape).head + 2 ∧
        -- Written values at this tape's head position
        (let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
         (c_t.work utmSimTape).cells (base + 1) =
           (symToSimHi (decodeΓw
             ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
             ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1)))).toΓ ∧
         (c_t.work utmSimTape).cells (base + 2) =
           (symToSimLo (decodeΓw
             ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
             ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1)))).toΓ) ∧
        -- Preserved +1/+2 cells for other positions (only meaningful for tapeIdx' < n+2)
        (∀ pos tapeIdx',
            tapeIdx' < n + 2 →
            (tapeIdx' ≠ tapeIdx ∨ pos ≠ h_target) →
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) =
              (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) ∧
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2) =
              (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2)) by
      -- Dispatch: apply IH or finish
      obtain ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hmarkers_t, hwf_t, hdesc_t,
              hstatecells_t, hinp_t, hout_t, hheads_t, hscr_t,
              hscr_cells_t, hscr_head_t, hwritten_t, hpres_t⟩ := one_tape
      -- Compose scratch tracking
      have hscr_cells_comp : (c_t.work utmScratchTape).cells =
          (c₁.work utmScratchTape).cells := by
        rw [hscr_cells_t, hscr_cells]
      have hscr_head_comp : (c_t.work utmScratchTape).head =
          (c₁.work utmScratchTape).head + 2 * (wrIdx + 1) := by
        rw [hscr_head_t, hscr_head]; omega
      -- Compose written values: previous writes + this write
      have hprev_writes_comp : ∀ wrIdx' (_ : wrIdx' < wrIdx + 1),
          let tapeIdx' := wrIdx' + 1
          let h_t := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                      else simCfg.output.head
          let base := SuperCell.simTapeOffset (n + 2) h_t tapeIdx'
          (c_t.work utmSimTape).cells (base + 1) =
            (symToSimHi (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ ∧
          (c_t.work utmSimTape).cells (base + 2) =
            (symToSimLo (decodeΓw
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx'))
              ((c₁.work utmScratchTape).cells ((c₁.work utmScratchTape).head + 2 * wrIdx' + 1)))).toΓ := by
        intro wrIdx' hwi'
        by_cases heq : wrIdx' = wrIdx
        · -- This is the tape we just processed
          subst heq
          have hw := hwritten_t
          simp only at hw
          rw [hscr_cells, hscr_head] at hw
          convert hw using 4 <;> rw [h_target_eq]
        · -- Previously processed tape
          have hwi'' : wrIdx' < wrIdx := by omega
          have hpw := hprev_writes wrIdx' hwi''
          simp only at hpw ⊢
          -- Need to show c_t cells = c cells at this position
          set tapeIdx' := wrIdx' + 1
          set h_t := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                      else simCfg.output.head
          have hne : tapeIdx' ≠ tapeIdx ∨ h_t ≠ h_target := by
            left; omega
          have := hpres_t h_t tapeIdx' (by omega) (by tauto)
          exact ⟨by rw [this.1]; exact hpw.1, by rw [this.2]; exact hpw.2⟩
      -- Compose preservation
      have hprev_pres_comp : ∀ pos tapeIdx',
          tapeIdx' < n + 2 →
          (tapeIdx' = 0 ∨
           ∀ wrIdx', wrIdx' < wrIdx + 1 → tapeIdx' = wrIdx' + 1 →
             pos ≠ (if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                    else simCfg.output.head)) →
          (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) ∧
          (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2) =
            (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2) := by
        intro pos tapeIdx' hti_lt hcond
        -- Show c_t = c at this position (it's not the current tape's head)
        have hne : tapeIdx' ≠ tapeIdx ∨ pos ≠ h_target := by
          rcases hcond with h0 | hall
          · left; omega
          · -- hall says: for all wrIdx' < wrIdx+1, if tapeIdx' = wrIdx'+1 then pos ≠ h_target_for wrIdx'
            by_cases htieq : tapeIdx' = tapeIdx
            · -- tapeIdx' = wrIdx + 1, so wrIdx' = wrIdx satisfies tapeIdx' = wrIdx' + 1
              right; rw [h_target_eq]
              exact hall wrIdx (by omega) htieq
            · left; exact htieq
        have hpt := hpres_t pos tapeIdx' hti_lt hne
        -- Now chain c_t = c at this pos, then c = c₁ via hprev_pres
        have hpc := hprev_pres pos tapeIdx' hti_lt (by
          rcases hcond with h0 | hall
          · exact Or.inl h0
          · exact Or.inr (fun wrIdx' hwi' => hall wrIdx' (by omega)))
        exact ⟨by rw [hpt.1]; exact hpc.1, by rw [hpt.2]; exact hpc.2⟩
      by_cases hlast : wrIdx + 1 < n + 1
      · -- Not last tape: apply IH
        rw [dif_pos hlast] at hst_t
        obtain ⟨steps_rest, c₂, hreach_rest, hst₂, hsimh₂, hdesc₂, hstatecells₂,
                hinp₂, hout₂, hwf₂, hheads₂, hmarkers₂, hscr₂,
                hscr_cells₂, hscr_head₂, hprev_writes₂, hprev_pres₂⟩ :=
          ih (wrIdx + 1) hlast c_t (by omega) hst_t hsimh_t hmarkers_t hwf_t
            hdesc_t hstatecells_t hinp_t hout_t hheads_t hscr_t
            hscr_cells_comp hscr_head_comp hprev_writes_comp hprev_pres_comp
        exact ⟨steps_t + steps_rest, c₂, reachesIn_trans _ hreach_t hreach_rest,
          hst₂, hsimh₂, hdesc₂, hstatecells₂, hinp₂, hout₂, hwf₂, hheads₂, hmarkers₂, hscr₂,
          hscr_cells₂, hscr_head₂, hprev_writes₂, hprev_pres₂⟩
      · -- Last tape: done
        rw [dif_neg hlast] at hst_t
        have hwrn : wrIdx = n := by omega
        exact ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hdesc_t, hstatecells_t,
          hinp_t, hout_t, hwf_t, hheads_t, hmarkers_t, hscr_t,
          hscr_cells_comp, by rw [hscr_head_comp, hwrn],
          by convert hprev_writes_comp using 2; omega,
          by intro pos ti hlt hcond; exact hprev_pres_comp pos ti hlt (by
            rcases hcond with h0 | hall
            · exact Or.inl h0
            · exact Or.inr (fun w hw => hall w (by omega)))⟩
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
        (∀ j, j ≥ 1 → (c₁₂.work utmScratchTape).cells j ≠ Γ.start) ∧
        sHi = symToSimHi (decodeΓw
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1))) ∧
        sLo = symToSimLo (decodeΓw
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1))) ∧
        (c₁₂.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (c₁₂.work utmScratchTape).head = (c.work utmScratchTape).head + 2 := by
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
        rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · -- sHi identity
        simp only [Tape.read, hca_scr]
      · -- sLo identity
        simp only [Tape.read, hca_scr]
      · -- Scratch cells preserved
        simp [c_b]
      · -- Scratch head advanced
        simp [c_b]
    obtain ⟨c₁₂, sHi, sLo, hreach₁₂, hst₁₂, hsim₁₂, hother₁₂, hinp₁₂,
            hout₁₂, hwf₁₂, hheads₁₂, hscr₁₂,
            hsHi_eq, hsLo_eq, hscr_cells₁₂, hscr_head₁₂⟩ := hsteps_12
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
        WorkTapesWF c₄₅.work ∧
        (c₄₅.work utmSimTape).cells (offset + 1) = sHi.toΓ ∧
        (c₄₅.work utmSimTape).cells (offset + 2) = sLo.toΓ := by
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
        rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
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
      · -- Written value at offset+1 = sHi.toΓ
        simp only [c₄₅, ↓reduceIte]
        rw [Function.update_of_ne (by omega : offset + 1 ≠ offset + 2)]
        simp only [c_mid, ↓reduceIte]
        exact Function.update_self _ _ _
      · -- Written value at offset+2 = sLo.toΓ
        simp only [c₄₅, ↓reduceIte]
        exact Function.update_self _ _ _
    obtain ⟨c₄₅, hreach₄₅, hst₄₅, hsimh₄₅, hsimcells₄₅,
            hother₄₅, hinp₄₅, hout₄₅, hwf₄₅, hcells₄₅_hi, hcells₄₅_lo⟩ := hsteps_45
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
    -- ── Scratch cells preserved ──
    have hne_scr_sim : utmScratchTape ≠ utmSimTape := by decide
    have hscr_cells_end : (c_end.work utmScratchTape).cells =
        (c.work utmScratchTape).cells := by
      rw [show c_end.work utmScratchTape = c_rw.work utmScratchTape from
            hwork_end utmScratchTape,
          hother_rw utmScratchTape hne_scr_sim,
          hother₄₅ utmScratchTape hne_scr_sim, hother_s utmScratchTape hne_scr_sim]
      exact hscr_cells₁₂
    -- ── Scratch head advanced ──
    have hscr_head_end : (c_end.work utmScratchTape).head =
        (c.work utmScratchTape).head + 2 := by
      rw [show (c_end.work utmScratchTape).head = (c_rw.work utmScratchTape).head from
            congr_arg Tape.head (hwork_end utmScratchTape)]
      rw [show (c_rw.work utmScratchTape).head = (c₄₅.work utmScratchTape).head from
            congr_arg Tape.head (hother_rw utmScratchTape hne_scr_sim)]
      rw [show (c₄₅.work utmScratchTape).head = (c_s.work utmScratchTape).head from
            congr_arg Tape.head (hother₄₅ utmScratchTape hne_scr_sim)]
      rw [show (c_s.work utmScratchTape).head = (c₁₂.work utmScratchTape).head from
            congr_arg Tape.head (hother_s utmScratchTape hne_scr_sim)]
      exact hscr_head₁₂
    -- ── Written values at this tape's head position ──
    have hwritten_end : let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
        (c_end.work utmSimTape).cells (base + 1) =
          (symToSimHi (decodeΓw
            ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
            ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1)))).toΓ ∧
        (c_end.work utmSimTape).cells (base + 2) =
          (symToSimLo (decodeΓw
            ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
            ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1)))).toΓ := by
      simp only
      constructor
      · -- offset+1 = sHi.toΓ
        rw [hwork_end utmSimTape, hsimcells_rw, hcells₄₅_hi, hsHi_eq]
      · -- offset+2 = sLo.toΓ
        rw [hwork_end utmSimTape, hsimcells_rw, hcells₄₅_lo, hsLo_eq]
    -- ── Preserved +1/+2 cells for other positions ──
    have hpres_end : ∀ pos tapeIdx',
        tapeIdx' < n + 2 →
        (tapeIdx' ≠ tapeIdx ∨ pos ≠ h_target) →
        (c_end.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) =
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1) ∧
        (c_end.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2) =
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2) := by
      intro pos tapeIdx' hti_lt hne
      -- Helper: simTapeOffset expansion
      have hsto : ∀ (p t : ℕ), SuperCell.simTapeOffset (n + 2) p t =
          1 + p * (3 * (n + 2)) + 3 * t := by
        intros; simp [SuperCell.simTapeOffset, SuperCell.width]
      -- Prove all four ne's needed for hsimcells₄₅
      -- Key: if pos*(n+2) + tapeIdx' = h_target*(n+2) + tapeIdx
      -- then tapeIdx' = tapeIdx (by mod (n+2)) and pos = h_target (by div (n+2))
      -- Euclidean uniqueness helper for +1 vs +1 and +2 vs +2
      have succ_expand : ∀ x, (x + 1) * (n + 2) = x * (n + 2) + (n + 2) :=
        fun x => Nat.succ_mul x (n + 2)
      have ne_inner : pos * (n + 2) + tapeIdx' ≠ h_target * (n + 2) + tapeIdx := by
        intro heq
        rcases hne with hti | hpos
        · -- tapeIdx' ≠ tapeIdx: since both < n+2, Euclidean division gives the same remainder
          rcases Nat.lt_or_gt_of_ne hti with hlt | hgt
          · rcases le_or_gt pos h_target with hle | hgt'
            · exact absurd (by have := Nat.mul_le_mul_right (n + 2) hle; omega : tapeIdx' = tapeIdx) hti
            · have h1 := Nat.mul_le_mul_right (n + 2) (show h_target + 1 ≤ pos from hgt')
              rw [succ_expand] at h1; omega
          · rcases le_or_gt h_target pos with hle | hgt'
            · exact absurd (by have := Nat.mul_le_mul_right (n + 2) hle; omega : tapeIdx' = tapeIdx) hti
            · have h1 := Nat.mul_le_mul_right (n + 2) (show pos + 1 ≤ h_target from hgt')
              rw [succ_expand] at h1; omega
        · -- pos ≠ h_target
          rcases Nat.lt_or_gt_of_ne hpos with hlt | hgt
          · have h1 := Nat.mul_le_mul_right (n + 2) (show pos + 1 ≤ h_target from hlt)
            rw [succ_expand] at h1; omega
          · have h1 := Nat.mul_le_mul_right (n + 2) (show h_target + 1 ≤ pos from hgt)
            rw [succ_expand] at h1; omega
      have ne_offset1 : SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1 ≠ offset + 1 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        intro heq; exact ne_inner (by omega)
      have ne_offset2 : SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 1 ≠ offset + 2 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        omega
      have ne_offset3 : SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2 ≠ offset + 1 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        omega
      have ne_offset4 : SuperCell.simTapeOffset (n + 2) pos tapeIdx' + 2 ≠ offset + 2 := by
        simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
        rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm h_target 3 (n + 2)]
        intro heq; exact ne_inner (by omega)
      rw [hwork_end utmSimTape, hsimcells_rw]
      constructor
      · rw [hsimcells₄₅ _ ne_offset1 ne_offset2, hsimcells_s, hsim₁₂]
      · rw [hsimcells₄₅ _ ne_offset3 ne_offset4, hsimcells_s, hsim₁₂]
    -- ── Assembly ──
    exact ⟨_, c_end, htotal, hst_end,
      by rw [show c_end.work utmSimTape = c_rw.work utmSimTape from hwork_end utmSimTape,
             hsimh_rw],
      hmarkers_end, hwf_end, hdesc_end, hstatecells_end,
      hinp_end_c₁, hout_end_c₁, hheads_end, hscr_end,
      hscr_cells_end, hscr_head_end, hwritten_end, hpres_end⟩
-- Phase 2: move head markers on sim tape
-- ════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- Phase 2: processes n+2 tapes (input, work 0..n-1, output), moving head markers.
    Reads 2 bits per tape from scratch (the Dir3 encoding), scans sim tape for
    the head marker, clears it, steps 3*(n+2) cells in the given direction,
    and writes the new marker. -/
private theorem phase2_moveHeads {Q : Type} [DecidableEq Q]
    (c₂ : Cfg 4 (applyTransitionTM (n := n) k).Q)
    (simCfg : Cfg n Q) (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3)
    (headPos : Fin (n + 2) → ℕ)
    (newHeadPos : Fin (n + 2) → ℕ)
    (hnewHead : ∀ (ti : Fin (n + 2)),
        newHeadPos ti = match decodeDir3
          ((c₂.work utmScratchTape).cells ((c₂.work utmScratchTape).head + 2 * ti.val))
          ((c₂.work utmScratchTape).cells ((c₂.work utmScratchTape).head + 2 * ti.val + 1))
        with | .stay => headPos ti | .right => headPos ti + 1 | .left => headPos ti - 1)
    (hstate : c₂.state = ApplyTransQ.rdMvHi ⟨0, by omega⟩)
    (hwf : WorkTapesWF c₂.work)
    (hsim_h : (c₂.work utmSimTape).head = 1)
    (hheads : ∀ i : Fin 4, (c₂.work i).head ≥ 1)
    (hmarkers : ∀ (ti : Fin (n + 2)) (pos : ℕ),
        (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
        if headPos ti = pos then Γ.one else Γ.blank)
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
      (∀ i : Fin 4, (c₃.work i).head ≥ 1) ∧
      -- Symbol cells preserved through Phase 2
      (∀ pos tapeIdx,
        (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
        (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
        (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
        (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) ∧
      -- New head marker positions after Phase 2
      (∀ (ti : Fin (n + 2)) (pos : ℕ),
        (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
        if newHeadPos ti = pos then Γ.one else Γ.blank) := by
  -- Outer induction: process tapes mvIdx = 0, ..., n+1
  suffices outer : ∀ (fuel mvIdx : ℕ) (hmvi : mvIdx < n + 2)
      (c : Cfg 4 (applyTransitionTM (n := n) k).Q),
      fuel + mvIdx = n + 2 →
      c.state = ApplyTransQ.rdMvHi ⟨mvIdx, hmvi⟩ →
      (c.work utmSimTape).head = 1 →
      WorkTapesWF c.work →
      (∀ i : Fin 4, (c.work i).head ≥ 1) →
      (∀ (ti : Fin (n + 2)), ti.val ≥ mvIdx → ∀ pos,
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
          if headPos ti = pos then Γ.one else Γ.blank) →
      c.work utmDescTape = c₂.work utmDescTape →
      (c.work utmStateTape).cells = (c₂.work utmStateTape).cells →
      c.input = c₂.input → c.output = c₂.output →
      -- Symbol cells preserved from c₂
      (∀ pos tapeIdx,
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
        (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
        (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) →
      -- Scratch tape tracking
      (c.work utmScratchTape).head = (c₂.work utmScratchTape).head + 2 * mvIdx →
      (c.work utmScratchTape).cells = (c₂.work utmScratchTape).cells →
      -- Processed markers at newHeadPos
      (∀ (ti : Fin (n + 2)), ti.val < mvIdx → ∀ pos,
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
          if newHeadPos ti = pos then Γ.one else Γ.blank) →
      ∃ steps c₃,
        (applyTransitionTM (n := n) k).reachesIn steps c c₃ ∧
        c₃.state = ApplyTransQ.clrScr ∧
        (c₃.work utmSimTape).head = 1 ∧
        c₃.work utmDescTape = c₂.work utmDescTape ∧
        (c₃.work utmStateTape).cells = (c₂.work utmStateTape).cells ∧
        c₃.input = c₂.input ∧ c₃.output = c₂.output ∧
        WorkTapesWF c₃.work ∧
        (∀ i : Fin 4, (c₃.work i).head ≥ 1) ∧
        (∀ pos tapeIdx,
          (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
          (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
          (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
          (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) ∧
        (∀ (ti : Fin (n + 2)) (pos : ℕ),
          (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
          if newHeadPos ti = pos then Γ.one else Γ.blank) by
    exact outer (n + 2) 0 (by omega) c₂ (by omega) hstate hsim_h hwf hheads
      (fun ti _ pos => hmarkers ti pos) rfl rfl rfl rfl (fun pos tapeIdx => ⟨rfl, rfl⟩)
      (by simp) rfl (fun ti h => by omega)
  intro fuel
  induction fuel with
  | zero => intro mvIdx hmvi c hfuel; omega
  | succ m ih =>
    intro mvIdx hmvi c hfuel hst hsimh hwf' hw_heads hmarker_inv
      hdesc hstatecells hinp_eq hout_eq hsymcells_inv
      hscratch_head hscratch_cells hprocessed_markers
    -- Extract marker info for current tape
    set W := 3 * (n + 2) with hW_def
    set target_head := headPos ⟨mvIdx, hmvi⟩ with htarget_def
    set offset := SuperCell.simTapeOffset (n + 2) target_head mvIdx with hoffset_def
    have hoffset_pos : offset ≥ 1 := by
      simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]; omega
    have hmarker_current : ∀ pos,
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos mvIdx) =
        if target_head = pos then Γ.one else Γ.blank :=
      fun pos => hmarker_inv ⟨mvIdx, hmvi⟩ (le_refl mvIdx) pos
    -- Common helpers
    have hinp' : c.input.read ≠ Γ.start := by rw [hinp_eq]; exact hinp
    have hinp_h' : c.input.head ≥ 1 := by rw [hinp_eq]; exact hinp_h
    have hout' : c.output.read ≠ Γ.start := by rw [hout_eq]; exact hout
    have hout_h' : c.output.head ≥ 1 := by rw [hout_eq]; exact hout_h
    -- ── One-tape iteration ──
    suffices one_tape : ∃ steps_t c_t,
        (applyTransitionTM (n := n) k).reachesIn steps_t c c_t ∧
        c_t.state = (if h : mvIdx + 1 < n + 2
          then ApplyTransQ.rdMvHi ⟨mvIdx + 1, h⟩
          else ApplyTransQ.clrScr) ∧
        (c_t.work utmSimTape).head = 1 ∧
        WorkTapesWF c_t.work ∧
        (∀ i : Fin 4, (c_t.work i).head ≥ 1) ∧
        -- Markers for remaining tapes preserved
        (∀ (ti : Fin (n + 2)), ti.val ≥ mvIdx + 1 → ∀ pos,
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
            if headPos ti = pos then Γ.one else Γ.blank) ∧
        c_t.work utmDescTape = c₂.work utmDescTape ∧
        (c_t.work utmStateTape).cells = (c₂.work utmStateTape).cells ∧
        c_t.input = c₂.input ∧ c_t.output = c₂.output ∧
        -- Symbol cells preserved from input c
        (∀ pos tapeIdx,
          (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
          (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
          (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) ∧
        -- Scratch tape tracking
        (c_t.work utmScratchTape).head = (c₂.work utmScratchTape).head + 2 * (mvIdx + 1) ∧
        (c_t.work utmScratchTape).cells = (c₂.work utmScratchTape).cells ∧
        -- Processed markers at newHeadPos (including current tape)
        (∀ (ti : Fin (n + 2)), ti.val < mvIdx + 1 → ∀ pos,
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
            if newHeadPos ti = pos then Γ.one else Γ.blank) by
      -- Dispatch: apply IH or finish
      obtain ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hwf_t, hheads_t,
              hmarkers_t, hdesc_t, hstatecells_t, hinp_t, hout_t, hsymcells_t,
              hscrh_t, hscrc_t, hprocessed_t⟩ := one_tape
      by_cases hlast : mvIdx + 1 < n + 2
      · -- Not last tape: apply IH
        rw [dif_pos hlast] at hst_t
        -- Compose symbol cell preservation: c₂ → c → c_t
        have hsymcells_composed : ∀ pos tapeIdx,
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) :=
          fun pos tapeIdx => by
            rw [(hsymcells_t pos tapeIdx).1, (hsymcells_t pos tapeIdx).2,
                (hsymcells_inv pos tapeIdx).1, (hsymcells_inv pos tapeIdx).2]
            exact ⟨rfl, rfl⟩
        obtain ⟨steps_rest, c₃, hreach_rest, hst₃, hsimh₃, hdesc₃, hstatecells₃,
                hinp₃, hout₃, hwf₃, hheads₃, hsymcells₃, hnewmarkers₃⟩ :=
          ih (mvIdx + 1) hlast c_t (by omega) hst_t hsimh_t hwf_t hheads_t
            hmarkers_t hdesc_t hstatecells_t hinp_t hout_t hsymcells_composed
            hscrh_t hscrc_t hprocessed_t
        exact ⟨steps_t + steps_rest, c₃, reachesIn_trans _ hreach_t hreach_rest,
          hst₃, hsimh₃, hdesc₃, hstatecells₃, hinp₃, hout₃, hwf₃, hheads₃, hsymcells₃,
          hnewmarkers₃⟩
      · -- Last tape: done
        rw [dif_neg hlast] at hst_t
        -- Compose symbol cell preservation: c₂ → c → c_t
        have hsymcells_composed : ∀ pos tapeIdx,
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
            (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) :=
          fun pos tapeIdx => by
            rw [(hsymcells_t pos tapeIdx).1, (hsymcells_t pos tapeIdx).2,
                (hsymcells_inv pos tapeIdx).1, (hsymcells_inv pos tapeIdx).2]
            exact ⟨rfl, rfl⟩
        -- All tapes processed: mvIdx + 1 = n + 2
        have hall : mvIdx + 1 = n + 2 := by omega
        have hnewmarkers_all : ∀ (ti : Fin (n + 2)) (pos : ℕ),
            (c_t.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
            if newHeadPos ti = pos then Γ.one else Γ.blank :=
          fun ti pos => hprocessed_t ti (by omega) pos
        exact ⟨steps_t, c_t, hreach_t, hst_t, hsimh_t, hdesc_t, hstatecells_t,
          hinp_t, hout_t, hwf_t, hheads_t, hsymcells_composed, hnewmarkers_all⟩
    -- ── Prove one_tape ──
    -- ── Steps 1-2: rdMvHi → rdMvLo → scanMv (2 fixed steps) ──
    have hsteps_12 : ∃ (c₁₂ : Cfg 4 (applyTransitionTM (n := n) k).Q) (dir : Dir3),
        (applyTransitionTM (n := n) k).reachesIn 2 c c₁₂ ∧
        c₁₂.state = .scanMv ⟨mvIdx, hmvi⟩ ⟨0, by omega⟩ dir false ∧
        c₁₂.work utmSimTape = c.work utmSimTape ∧
        (∀ i, i ≠ utmScratchTape → i ≠ utmSimTape → c₁₂.work i = c.work i) ∧
        c₁₂.input = c.input ∧ c₁₂.output = c.output ∧
        WorkTapesWF c₁₂.work ∧
        (∀ i : Fin 4, (c₁₂.work i).head ≥ 1) ∧
        (c₁₂.work utmScratchTape).head = (c.work utmScratchTape).head + 2 ∧
        (c₁₂.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        dir = decodeDir3
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head))
          ((c.work utmScratchTape).cells ((c.work utmScratchTape).head + 1)) := by
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
      -- Step 1 config: rdMvHi → rdMvLo
      set c_a : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := .rdMvLo ⟨mvIdx, hmvi⟩ (c.work utmScratchTape).read
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
        exact ⟨trivial, by rw [readBackWrite_toΓ_eq (hwf'.2 utmScratchTape _ (by have := hw_heads utmScratchTape; omega))]; exact Function.update_eq_self _ _⟩
      -- Step 2 config: rdMvLo → scanMv
      set c_b : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := .scanMv ⟨mvIdx, hmvi⟩ ⟨0, by omega⟩
            (decodeDir3 (c.work utmScratchTape).read (c_a.work utmScratchTape).read) false
          input := c.input
          work := fun i => if i = utmScratchTape
            then ⟨(c.work utmScratchTape).head + 2, (c.work utmScratchTape).cells⟩
            else c.work i
          output := c.output }
      have hstep_b : (applyTransitionTM (n := n) k).step c_a = some c_b := by
        simp only [TM.step, hne_a, ↓reduceIte]
        congr 1; simp only [c_a]; simp only [applyTransitionTM, ↓reduceIte]
        simp only [c_b, c_a, decodeDir3, ↓reduceIte, Tape.read, Cfg.mk.injEq]
        refine ⟨trivial, hinp_idle, funext fun i => ?_, hout_idle⟩
        by_cases hi : i = utmScratchTape
        · subst hi; simp only [↓reduceIte]; exact hca_scr_wam
        · simp only [hi, ↓reduceIte]; exact hw_idle i
      -- Provide witnesses and prove postconditions
      refine ⟨c_b,
        decodeDir3 (c.work utmScratchTape).read (c_a.work utmScratchTape).read,
        reachesIn.step hstep_a (reachesIn.step hstep_b reachesIn.zero),
        rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
          · simp only [c_b, hi, ↓reduceIte]; exact hwf'.2 i j hj
      · -- Heads ≥ 1
        intro i; by_cases hi : i = utmScratchTape
        · subst hi; simp [c_b]
        · simp only [c_b, hi, ↓reduceIte]; exact hw_heads i
      · -- Scratch head
        simp [c_b]
      · -- Scratch cells
        simp [c_b]
      · -- Direction
        simp only [Tape.read, c_a, ↓reduceIte, c_b]
    obtain ⟨c₁₂, dir, hreach₁₂, hst₁₂, hsim₁₂, hother₁₂, hinp₁₂,
            hout₁₂, hwf₁₂, hheads₁₂, hscrh₁₂, hscrc₁₂, hdir₁₂⟩ := hsteps_12
    -- ── Step 3: scanMv loop → clearMk (variable steps) ──
    have hoffset_expand : offset - 1 = target_head * W + 3 * mvIdx := by
      simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width, hW_def]; omega
    have hsimh₁₂ : (c₁₂.work utmSimTape).head = 1 := by rw [hsim₁₂, hsimh]
    have hstep_scan : ∃ (steps_s : ℕ) (c_s : Cfg 4 (applyTransitionTM (n := n) k).Q) (posZero : Bool),
        (applyTransitionTM (n := n) k).reachesIn steps_s c₁₂ c_s ∧
        c_s.state = .clearMk ⟨mvIdx, hmvi⟩ dir posZero ∧
        (c_s.work utmSimTape).head = offset ∧
        (c_s.work utmSimTape).cells = (c₁₂.work utmSimTape).cells ∧
        (∀ i, i ≠ utmSimTape → c_s.work i = c₁₂.work i) ∧
        c_s.input = c₁₂.input ∧ c_s.output = c₁₂.output ∧
        WorkTapesWF c_s.work ∧
        (posZero = false → offset ≥ W + 1) ∧
        (posZero = true → target_head = 0) := by
      suffices loop : ∀ (rem : ℕ) (wrapped : Bool)
          (c' : Cfg 4 (applyTransitionTM (n := n) k).Q),
          (c'.work utmSimTape).head + rem = offset →
          c'.state = .scanMv ⟨mvIdx, hmvi⟩
            ⟨((c'.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ dir wrapped →
          (c'.work utmSimTape).cells = (c₁₂.work utmSimTape).cells →
          (∀ i, i ≠ utmSimTape → c'.work i = c₁₂.work i) →
          c'.input = c₁₂.input → c'.output = c₁₂.output →
          WorkTapesWF c'.work →
          (∀ i, (c'.work i).head ≥ 1) →
          (wrapped = true → (c'.work utmSimTape).head ≥ W) →
          (wrapped = false → (c'.work utmSimTape).head ≤ W) →
          ∃ (c_s : Cfg 4 (applyTransitionTM (n := n) k).Q) (pz : Bool),
            (applyTransitionTM (n := n) k).reachesIn (rem + 1) c' c_s ∧
            c_s.state = .clearMk ⟨mvIdx, hmvi⟩ dir pz ∧
            (c_s.work utmSimTape).head = offset ∧
            (c_s.work utmSimTape).cells = (c₁₂.work utmSimTape).cells ∧
            (∀ i, i ≠ utmSimTape → c_s.work i = c₁₂.work i) ∧
            c_s.input = c₁₂.input ∧ c_s.output = c₁₂.output ∧
            WorkTapesWF c_s.work ∧
            (pz = false → offset ≥ W + 1) ∧
            (pz = true → target_head = 0) by
        obtain ⟨c_s, pz, hr, hst_s, hh_s, hcells_s, ho_s, hinp_s, hout_s, hwf_s, hpz_s,
                hpz_zero⟩ :=
          loop (offset - 1) false c₁₂ (by omega)
            (by convert hst₁₂ using 2; ext; simp [hsimh₁₂])
            rfl (fun _ _ => rfl) rfl rfl hwf₁₂ (fun i => hheads₁₂ i)
            (by intro h; simp at h)
            (by intro _; rw [hsimh₁₂]; omega)
        exact ⟨offset, c_s, pz, by rwa [show offset - 1 + 1 = offset by omega] at hr,
               hst_s, hh_s, hcells_s, ho_s, hinp_s, hout_s, hwf_s, hpz_s, hpz_zero⟩
      intro rem; induction rem with
      | zero =>
        intro wrapped c' hhead hstate' hcells' ho' hinp_c' hout_c' hwf' hheads' hwrap_ge hwrap_le
        have hsim_head' : (c'.work utmSimTape).head = offset := by omega
        have hpos_val : ((c'.work utmSimTape).head - 1) % W = 3 * mvIdx := by
          rw [hsim_head']
          have h1 : offset - 1 = target_head * W + 3 * mvIdx := hoffset_expand
          rw [h1, Nat.mul_add_mod_self_right,
              Nat.mod_eq_of_lt (show 3 * mvIdx < W by omega)]
        have hread_one : (c'.work utmSimTape).read = Γ.one := by
          simp only [Tape.read, hsim_head', hcells', hsim₁₂]
          have := hmarker_current target_head
          simp only [htarget_def, ↓reduceIte] at this; exact this
        have hne : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
          rw [hstate']; simp [applyTransitionTM]
        have hw_ns_all : ∀ i, (c'.work i).read ≠ Γ.start :=
          fun i => at_read_ne_start _ (hheads' i) (hwf'.2 i)
        have hw_idle_all : ∀ i,
            (c'.work i).writeAndMove ((readBackWrite ((c'.work i).read)).toΓ)
              (idleDir ((c'.work i).read)) = c'.work i :=
          fun i => tape_idle_preserve _ (hw_ns_all i) (hheads' i)
        have hinp_idle : c'.input.move (idleDir c'.input.read) = c'.input := by
          simp only [idleDir,
            (show c'.input.read ≠ Γ.start by rw [hinp_c', hinp₁₂, hinp_eq]; exact hinp),
            ↓reduceIte, Tape.move]
        have hout_idle : c'.output.writeAndMove ((readBackWrite c'.output.read).toΓ)
            (idleDir c'.output.read) = c'.output :=
          tape_idle_preserve _
            (by rw [hout_c', hout₁₂, hout_eq]; exact hout)
            (by rw [hout_c', hout₁₂, hout_eq]; exact hout_h)
        set c_next : Cfg 4 (applyTransitionTM (n := n) k).Q :=
          { state := .clearMk ⟨mvIdx, hmvi⟩ dir (!wrapped)
            input := c'.input
            work := c'.work
            output := c'.output }
        have hstep : (applyTransitionTM (n := n) k).step c' = some c_next := by
          simp only [TM.step, hne, ↓reduceIte]
          congr 1; rw [hstate']; simp only [applyTransitionTM]
          simp only [hpos_val, ↓reduceIte, hread_one]
          simp only [c_next, Cfg.mk.injEq]
          exact ⟨trivial, hinp_idle, funext hw_idle_all, hout_idle⟩
        exact ⟨c_next, !wrapped, .step hstep .zero, rfl,
          by simp [c_next, hsim_head'],
          by simp [c_next]; exact hcells',
          fun i hi => by simp [c_next]; exact ho' i hi,
          hinp_c', hout_c', hwf',
          fun hpz => by
            have hwt : wrapped = true := by cases wrapped <;> simp_all
            have h1 := hwrap_ge hwt
            have h2 : (c'.work utmSimTape).head = offset := by omega
            rw [h2] at h1
            have h3 : offset ≠ W := by
              intro heq
              simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width, hW_def] at heq
              rw [mul_left_comm target_head 3 (n + 2)] at heq; omega
            omega,
          fun hpz => by
            have hwf' : wrapped = false := by cases wrapped <;> simp_all
            have h1 := hwrap_le hwf'
            rw [hsim_head'] at h1
            simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width, hW_def,
              htarget_def] at h1 ⊢
            by_contra hne
            have hge : headPos ⟨mvIdx, hmvi⟩ ≥ 1 := by omega
            have := Nat.mul_le_mul_right (3 * (n + 2)) hge
            omega⟩
      | succ m ihm =>
        intro wrapped c' hhead hstate' hcells' ho' hinp_c' hout_c' hwf' hheads' hwrap_ge hwrap_le
        have hhead_lt : (c'.work utmSimTape).head < offset := by omega
        have hhead_ge : (c'.work utmSimTape).head ≥ 1 := hheads' utmSimTape
        have hread_ne_start : (c'.work utmSimTape).read ≠ Γ.start :=
          at_read_ne_start _ hhead_ge (hwf'.2 utmSimTape)
        set pos := ((c'.work utmSimTape).head - 1) % W with hpos_def
        have hread_ne_one : ¬(pos = 3 * mvIdx ∧
            (c'.work utmSimTape).read = Γ.one) := by
          intro ⟨hpos_eq, hread_eq⟩
          simp only [Tape.read] at hread_eq
          rw [hcells', hsim₁₂] at hread_eq
          have hdiv := Nat.div_add_mod ((c'.work utmSimTape).head - 1) W
          have hhead_eq : (c'.work utmSimTape).head =
              SuperCell.simTapeOffset (n + 2) (((c'.work utmSimTape).head - 1) / W) mvIdx := by
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
        have hne : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
          rw [hstate']; simp [applyTransitionTM]
        have hw_ns : ∀ i, i ≠ utmSimTape → (c'.work i).read ≠ Γ.start :=
          fun i hi => at_read_ne_start _ (hheads' i) (hwf'.2 i)
        have hw_idle : ∀ i, i ≠ utmSimTape →
            (c'.work i).writeAndMove ((readBackWrite ((c'.work i).read)).toΓ)
              (idleDir ((c'.work i).read)) = c'.work i :=
          fun i hi => tape_idle_preserve _ (hw_ns i hi) (hheads' i)
        have hinp_idle : c'.input.move (idleDir c'.input.read) = c'.input := by
          simp only [idleDir,
            (show c'.input.read ≠ Γ.start by rw [hinp_c', hinp₁₂, hinp_eq]; exact hinp),
            ↓reduceIte, Tape.move]
        have hout_idle : c'.output.writeAndMove ((readBackWrite c'.output.read).toΓ)
            (idleDir c'.output.read) = c'.output :=
          tape_idle_preserve _
            (by rw [hout_c', hout₁₂, hout_eq]; exact hout)
            (by rw [hout_c', hout₁₂, hout_eq]; exact hout_h)
        have hsim_wam : (c'.work utmSimTape).writeAndMove
            ((readBackWrite ((c'.work utmSimTape).read)).toΓ) Dir3.right =
            ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩ := by
          simp only [Tape.writeAndMove, Tape.write,
            show ¬(c'.work utmSimTape).head = 0 from by have := hheads' utmSimTape; omega,
            ↓reduceIte, Tape.move]
          congr 1; rw [readBackWrite_toΓ_eq hread_ne_start]
          simp only [Tape.read, Function.update_eq_self]
        set newWrapped := wrapped || ((pos + 1) == W)
        set c_next : Cfg 4 (applyTransitionTM (n := n) k).Q :=
          { state := .scanMv ⟨mvIdx, hmvi⟩
              ⟨(pos + 1) % W, Nat.mod_lt _ (by omega)⟩ dir newWrapped
            input := c'.input
            work := fun i => if i = utmSimTape
              then ⟨(c'.work utmSimTape).head + 1, (c'.work utmSimTape).cells⟩
              else c'.work i
            output := c'.output }
        have hstep : (applyTransitionTM (n := n) k).step c' = some c_next := by
          simp only [TM.step, hne, ↓reduceIte]
          congr 1; rw [hstate']; simp only [applyTransitionTM]
          -- Both branches of the pos check produce the same tape effects
          by_cases hpeq : ((c'.work utmSimTape).head - 1) % W = 3 * mvIdx
          · have hread_ne : (c'.work utmSimTape).read ≠ Γ.one :=
              fun h => hread_ne_one ⟨hpeq, h⟩
            simp only [hpeq, ↓reduceIte, hread_ne]
            simp only [c_next, Cfg.mk.injEq]
            constructor
            · have hpos_eq_rw : (3 * mvIdx + 1) % (3 * (n + 2)) = (pos + 1) % W := by
                rw [hpos_def, hpeq, hW_def]
              congr 1
              · ext; exact hpos_eq_rw
              · congr 1; rw [hpos_def, hpeq]
            · exact ⟨hinp_idle, funext fun i => by
                by_cases hi : i = utmSimTape
                · subst hi; simp only [↓reduceIte]; exact hsim_wam
                · simp only [hi, ↓reduceIte]; exact hw_idle i hi,
              hout_idle⟩
          · simp only [hpeq, ↓reduceIte]
            simp only [c_next, Cfg.mk.injEq]
            constructor
            · congr 1 <;> simp [newWrapped, hpos_def, hW_def]
            · exact ⟨hinp_idle, funext fun i => by
                by_cases hi : i = utmSimTape
                · subst hi; simp only [↓reduceIte]; exact hsim_wam
                · simp only [hi, ↓reduceIte]; exact hw_idle i hi,
              hout_idle⟩
        have hh1 : (c_next.work utmSimTape).head = (c'.work utmSimTape).head + 1 := by
          simp [c_next]
        have hcells1 : (c_next.work utmSimTape).cells = (c'.work utmSimTape).cells := by
          simp [c_next]
        have ho1 : ∀ i, i ≠ utmSimTape → c_next.work i = c'.work i :=
          fun i hi => by simp [c_next, hi]
        have hwf1 : WorkTapesWF c_next.work := by
          constructor
          · intro i; by_cases h : i = utmSimTape
            · simp [c_next, h, hwf'.1 utmSimTape]
            · simp [c_next, h, hwf'.1 i]
          · intro i j hj; by_cases h : i = utmSimTape
            · simp [c_next, h, hwf'.2 utmSimTape j hj]
            · simp only [c_next, h, ↓reduceIte]; exact hwf'.2 i j hj
        have hheads1 : ∀ i, (c_next.work i).head ≥ 1 := by
          intro i; by_cases h : i = utmSimTape
          · rw [h, hh1]; omega
          · rw [ho1 i h]; exact hheads' i
        have hmod_step : (pos + 1) % W = (c'.work utmSimTape).head % W := by
          rw [hpos_def]
          rw [Nat.mod_add_mod, Nat.sub_add_cancel hhead_ge]
        have hstate1 : c_next.state = .scanMv ⟨mvIdx, hmvi⟩
            ⟨((c_next.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ dir newWrapped := by
          simp only [c_next]; congr 1; ext; exact hmod_step
        have hhead1 : (c_next.work utmSimTape).head + m = offset := by omega
        obtain ⟨c_f, pz, hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f, hpz_f,
                hpz_zero_f⟩ :=
          ihm newWrapped c_next hhead1 hstate1 (by rw [hcells1, hcells'])
            (by intro i hne_i; rw [ho1 i hne_i, ho' i hne_i])
            (by simp [c_next, hinp_c']) (by simp [c_next, hout_c']) hwf1 hheads1
            (fun hnw => by
              rw [hh1]
              simp only [newWrapped] at hnw
              cases hwr : wrapped <;> simp only [hwr, Bool.false_or, Bool.true_or] at hnw
              · -- wrapped = false, hnw : (pos + 1 == W) = true
                have hposeq : pos + 1 = W := by simpa using hnw
                have hdm := Nat.div_add_mod ((c'.work utmSimTape).head - 1) W
                rw [hpos_def] at hposeq
                omega
              · -- wrapped = true
                have := hwrap_ge hwr; omega)
            (fun hnwf => by
              rw [hh1]
              simp only [newWrapped, Bool.or_eq_false_iff] at hnwf
              have hwr := hnwf.1
              have hpnw : ¬(pos + 1 = W) := by simpa using hnwf.2
              have h_le := hwrap_le hwr
              have h_mod : pos = (c'.work utmSimTape).head - 1 := by
                rw [hpos_def, Nat.mod_eq_of_lt (by omega)]
              omega)
        exact ⟨c_f, pz, .step hstep hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f,
               hpz_f, hpz_zero_f⟩
    obtain ⟨steps_s, c_s, posZero, hreach_s, hst_s, hsimh_s, hsimcells_s,
            hother_s, hinp_s, hout_s, hwf_s, hpz_bound, hpz_zero⟩ := hstep_scan
    -- Derive useful facts about c_s
    have hw_heads_s : ∀ i : Fin 4, (c_s.work i).head ≥ 1 := by
      intro i; by_cases hi : i = utmSimTape
      · subst hi; rw [hsimh_s]; exact hoffset_pos
      · rw [hother_s i hi]; exact hheads₁₂ i
    -- ── Steps 4-7: clearMk → (possibly mvStep loop + setMk) → rwMv loop → rwMvR ──
    -- After clearMk we either skip movement (dir = stay or left-at-zero) or
    -- do the full clear+move+set sequence. Both paths end at rwMv, which
    -- we handle with phase2_rwMv_loop, then one more step for rwMvR.
    -- Compute the new head position for the current tape using dir
    set newHead_cur := match dir with
      | .stay => target_head | .right => target_head + 1 | .left => target_head - 1
      with hnewHead_cur_def
    have hstep_rest : ∃ (steps_r : ℕ) (c_r : Cfg 4 (applyTransitionTM (n := n) k).Q),
        (applyTransitionTM (n := n) k).reachesIn steps_r c_s c_r ∧
        c_r.state = (if h : mvIdx + 1 < n + 2
          then ApplyTransQ.rdMvHi ⟨mvIdx + 1, h⟩
          else ApplyTransQ.clrScr) ∧
        (c_r.work utmSimTape).head = 1 ∧
        -- Marker preservation for tapes with index ≠ mvIdx
        (∀ (ti : Fin (n + 2)), ti.val ≠ mvIdx → ∀ pos,
          (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
          (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val)) ∧
        (∀ i, i ≠ utmSimTape → c_r.work i = c_s.work i) ∧
        c_r.input = c_s.input ∧ c_r.output = c_s.output ∧
        WorkTapesWF c_r.work ∧
        -- Symbol cells preserved
        (∀ pos tapeIdx,
          (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
          (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
          (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
          (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) ∧
        -- Current tape marker at newHead_cur
        (∀ pos, (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos mvIdx) =
          if newHead_cur = pos then Γ.one else Γ.blank) := by
      -- The clearMk step goes to rwMv (if no movement needed) or mvStep
      -- (if movement needed). In both cases, after eventually reaching rwMv,
      -- we use phase2_rwMv_loop then one rwMvR step.
      --
      -- Key insight for marker preservation: all cell modifications happen at
      -- simTapeOffset positions for tapeIdx = mvIdx. For ti >= mvIdx + 1,
      -- simTapeOffset (n+2) pos ti uses column 3*ti which differs from
      -- column 3*mvIdx by at least 3, so those cells are untouched.
      --
      -- We break this into: reach rwMv state (with cells preserved at marker
      -- positions for ti >= mvIdx+1), then rwMv loop, then rwMvR.
      --
      -- Sub-step A: clearMk → rwMv (possibly via mvStep loop + setMk)
      have hstep_to_rwMv : ∃ (steps_a : ℕ) (c_a : Cfg 4 (applyTransitionTM (n := n) k).Q),
          (applyTransitionTM (n := n) k).reachesIn steps_a c_s c_a ∧
          c_a.state = .rwMv ⟨mvIdx, hmvi⟩ ∧
          (∀ (ti : Fin (n + 2)), ti.val ≠ mvIdx → ∀ pos,
            (c_a.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
            (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val)) ∧
          (∀ i, i ≠ utmSimTape → c_a.work i = c_s.work i) ∧
          c_a.input = c_s.input ∧ c_a.output = c_s.output ∧
          WorkTapesWF c_a.work ∧
          (∀ i : Fin 4, (c_a.work i).head ≥ 1) ∧
          -- Symbol cells (at +1 and +2 offsets) preserved
          (∀ pos tapeIdx,
            (c_a.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
            (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
            (c_a.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
            (c_s.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2)) ∧
          -- Current tape marker at newHead_cur
          (∀ pos, (c_a.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos mvIdx) =
            if newHead_cur = pos then Γ.one else Γ.blank) := by
        -- Split on whether movement is needed
        by_cases hmov : dir = Dir3.stay ∨ (dir = Dir3.left ∧ posZero = true)
        · -- Case 1: No movement needed. clearMk → rwMv in 1 step.
          have hne_s : c_s.state ≠ (applyTransitionTM (n := n) k).qhalt := by
            rw [hst_s]; simp [applyTransitionTM]
          have hw_ns_s : ∀ i, (c_s.work i).read ≠ Γ.start :=
            fun i => at_read_ne_start _ (hw_heads_s i) (hwf_s.2 i)
          have hw_idle_s : ∀ i,
              (c_s.work i).writeAndMove ((readBackWrite ((c_s.work i).read)).toΓ)
                (idleDir ((c_s.work i).read)) = c_s.work i :=
            fun i => tape_idle_preserve _ (hw_ns_s i) (hw_heads_s i)
          have hinp_idle_s : c_s.input.move (idleDir c_s.input.read) = c_s.input := by
            simp only [idleDir,
              (show c_s.input.read ≠ Γ.start by rw [hinp_s, hinp₁₂, hinp_eq]; exact hinp),
              ↓reduceIte, Tape.move]
          have hout_idle_s : c_s.output.writeAndMove
              ((readBackWrite c_s.output.read).toΓ) (idleDir c_s.output.read) = c_s.output :=
            tape_idle_preserve _
              (by rw [hout_s, hout₁₂, hout_eq]; exact hout)
              (by rw [hout_s, hout₁₂, hout_eq]; exact hout_h)
          set c_a : Cfg 4 (applyTransitionTM (n := n) k).Q :=
            { state := .rwMv ⟨mvIdx, hmvi⟩
              input := c_s.input
              work := c_s.work
              output := c_s.output }
          have hstep_a : (applyTransitionTM (n := n) k).step c_s = some c_a := by
            simp only [TM.step, hne_s, ↓reduceIte]
            congr 1; rw [hst_s]; simp only [applyTransitionTM]
            rcases hmov with h | ⟨h1, h2⟩
            · subst h; simp (config := { decide := true }) only []
              simp only [c_a, Cfg.mk.injEq]
              exact ⟨rfl, hinp_idle_s, funext hw_idle_s, hout_idle_s⟩
            · subst h1; simp only [h2]
              simp (config := { decide := true }) only []
              simp only [c_a, Cfg.mk.injEq]
              exact ⟨rfl, hinp_idle_s, funext hw_idle_s, hout_idle_s⟩
          refine ⟨1, c_a, .step hstep_a .zero, rfl,
            fun ti hti pos => by simp [c_a],
            fun i hi => by simp [c_a],
            by simp [c_a], by simp [c_a], by simp [c_a]; exact hwf_s,
            fun i => by simp [c_a]; exact hw_heads_s i,
            fun pos tapeIdx => by simp [c_a], ?_⟩
          -- Current tape marker: unchanged in Case 1 (no movement)
          intro pos; simp only [c_a]
          -- c_a.work = c_s.work, cells chain: c_s → c₁₂ → c
          rw [hsimcells_s, hsim₁₂]
          -- marker_current: cells at simTapeOffset pos mvIdx = if target_head = pos ...
          rw [hmarker_current pos]
          -- Need: newHead_cur = target_head
          have hnhc : newHead_cur = target_head := by
            rcases hmov with h | ⟨h1, h2⟩
            · subst h; simp [hnewHead_cur_def]
            · subst h1
              simp only [hnewHead_cur_def]
              have := hpz_zero h2
              rw [this]
          rw [hnhc]
        · -- Case 2: Movement needed. clearMk → mvStep → ... → setMk → rwMv.
          -- Chains: clearMk → mvStep(W) → ... → mvStep(0) → setMk → rwMv
          -- clearMk writes blank at offset, mvStep loop moves W steps,
          -- setMk writes one at new position, all entering rwMv.
          -- Marker preservation: writes only affect column 3*mvIdx,
          -- so columns 3*ti for ti ≥ mvIdx+1 are untouched
          -- (simTapeOffset positions differ mod (n+2)).
          -- Direction must be left (with posZero=false) or right
          have hdir : dir = Dir3.left ∨ dir = Dir3.right := by
            push_neg at hmov; rcases hmov with ⟨hns, hmov2⟩
            cases dir <;> simp_all
          -- goRight flag
          set goRight := (dir == Dir3.right) with hgoRight_def
          -- posZero must be false when dir = left (from hmov)
          have hpz_false : dir = Dir3.left → posZero = false := by
            intro hd; push_neg at hmov
            rcases hmov with ⟨_, h2⟩; exact Bool.eq_false_iff.mpr (h2 hd)
          -- When dir = left, offset ≥ W + 1
          have hoff_large : dir = Dir3.left → offset ≥ W + 1 := by
            intro hd; exact hpz_bound (hpz_false hd)
          -- clearMk condition is false
          have hclearMk_cond :
              (dir = Dir3.stay || (dir = Dir3.left && posZero)) = false := by
            rcases hdir with hd | hd <;> subst hd <;>
              simp (config := { decide := true }) [hpz_false]
          -- Helpers for idle tapes
          have hne_s : c_s.state ≠ (applyTransitionTM (n := n) k).qhalt := by
            rw [hst_s]; simp [applyTransitionTM]
          have hw_ns_s : ∀ i, (c_s.work i).read ≠ Γ.start :=
            fun i => at_read_ne_start _ (hw_heads_s i) (hwf_s.2 i)
          have hw_idle_s : ∀ i,
              (c_s.work i).writeAndMove ((readBackWrite ((c_s.work i).read)).toΓ)
                (idleDir ((c_s.work i).read)) = c_s.work i :=
            fun i => tape_idle_preserve _ (hw_ns_s i) (hw_heads_s i)
          have hinp_idle_s : c_s.input.move (idleDir c_s.input.read) = c_s.input := by
            simp only [idleDir,
              (show c_s.input.read ≠ Γ.start by rw [hinp_s, hinp₁₂, hinp_eq]; exact hinp),
              ↓reduceIte, Tape.move]
          have hout_idle_s : c_s.output.writeAndMove
              ((readBackWrite c_s.output.read).toΓ) (idleDir c_s.output.read) = c_s.output :=
            tape_idle_preserve _
              (by rw [hout_s, hout₁₂, hout_eq]; exact hout)
              (by rw [hout_s, hout₁₂, hout_eq]; exact hout_h)
          -- Chain A: clearMk → mvStep(W) (1 step)
          -- sim tape: write blank at offset, idle move
          -- new state: mvStep mvIdx goRight ⟨W, _⟩
          have hsim_read_s : (c_s.work utmSimTape).read = Γ.one := by
            simp only [Tape.read, hsimh_s, hsimcells_s, hsim₁₂]
            have := hmarker_current target_head
            simp only [htarget_def, ↓reduceIte] at this; exact this
          -- The sim tape write: blank at offset
          have hsim_write_s : (c_s.work utmSimTape).writeAndMove
              Γw.blank.toΓ (idleDir ((c_s.work utmSimTape).read)) =
              ⟨offset, Function.update (c_s.work utmSimTape).cells offset Γ.blank⟩ := by
            simp only [Tape.writeAndMove, Tape.write, hsimh_s,
              show ¬offset = 0 from by omega, ↓reduceIte, Tape.move,
              hsim_read_s, idleDir, show Γ.one ≠ Γ.start from by decide, ↓reduceIte]
            simp only [Γw.toΓ]
          set cells_A := Function.update (c_s.work utmSimTape).cells offset Γ.blank
          set c_A : Cfg 4 (applyTransitionTM (n := n) k).Q :=
            { state := .mvStep ⟨mvIdx, hmvi⟩ goRight ⟨W, by omega⟩
              input := c_s.input
              work := fun i => if i = utmSimTape
                then ⟨offset, cells_A⟩
                else c_s.work i
              output := c_s.output }
          have hstep_A : (applyTransitionTM (n := n) k).step c_s = some c_A := by
            simp only [TM.step, hne_s, ↓reduceIte]
            congr 1; rw [hst_s]; simp only [applyTransitionTM]
            rw [show (dir = Dir3.stay || (dir = Dir3.left && posZero)) = false from hclearMk_cond]
            simp only [Bool.false_eq_true, ↓reduceIte, c_A, Cfg.mk.injEq]
            refine ⟨?_, hinp_idle_s, funext fun i => ?_, hout_idle_s⟩
            · rfl
            · by_cases hi : i = utmSimTape
              · subst hi; simp only [↓reduceIte]; exact hsim_write_s
              · simp only [hi, ↓reduceIte]; exact hw_idle_s i
          -- Properties of c_A
          have hA_head : (c_A.work utmSimTape).head = offset := by simp [c_A]
          have hA_cells : (c_A.work utmSimTape).cells = cells_A := by simp [c_A]
          have hA_other : ∀ i, i ≠ utmSimTape → c_A.work i = c_s.work i := by
            intro i hi; simp [c_A, hi]
          have hA_inp : c_A.input = c_s.input := by simp [c_A]
          have hA_out : c_A.output = c_s.output := by simp [c_A]
          have hA_wf : WorkTapesWF c_A.work := by
            constructor
            · intro i; by_cases hi : i = utmSimTape
              · subst hi; simp only [c_A, ↓reduceIte, cells_A]
                rw [Function.update_of_ne (show (0 : ℕ) ≠ offset from by omega)]
                exact hwf_s.1 utmSimTape
              · simp [c_A, hi, hwf_s.1 i]
            · intro i j hj; by_cases hi : i = utmSimTape
              · subst hi; simp only [c_A, ↓reduceIte, cells_A]
                by_cases hjo : j = offset
                · subst hjo; simp [Function.update_self]
                · rw [Function.update_of_ne (show j ≠ offset from hjo)]
                  exact hwf_s.2 utmSimTape j hj
              · simp only [c_A, hi, ↓reduceIte]; exact hwf_s.2 i j hj
          have hA_heads : ∀ i : Fin 4, (c_A.work i).head ≥ 1 := by
            intro i; by_cases hi : i = utmSimTape
            · subst hi; rw [hA_head]; exact hoffset_pos
            · rw [hA_other i hi]; exact hw_heads_s i
          -- Chain B: mvStep loop W → setMk (W + 1 steps)
          -- After W steps, sim tape head = offset ± W
          -- The new offset = simTapeOffset (n+2) new_target mvIdx
          -- where new_target = target_head + 1 if goRight, target_head - 1 if not
          -- Prove induction: from mvStep rem to setMk in rem+1 steps
          have hmvStep_loop : ∀ (rem : ℕ) (hrem : rem ≤ W)
              (c' : Cfg 4 (applyTransitionTM (n := n) k).Q),
              c'.state = .mvStep ⟨mvIdx, hmvi⟩ goRight ⟨rem, by omega⟩ →
              (c'.work utmSimTape).head = (if goRight then offset + (W - rem) else offset - (W - rem)) →
              (c'.work utmSimTape).cells = cells_A →
              (∀ i, i ≠ utmSimTape → c'.work i = c_s.work i) →
              c'.input = c_s.input → c'.output = c_s.output →
              WorkTapesWF c'.work →
              (∀ i : Fin 4, (c'.work i).head ≥ 1) →
              ∃ (c_end : Cfg 4 (applyTransitionTM (n := n) k).Q),
                (applyTransitionTM (n := n) k).reachesIn (rem + 1) c' c_end ∧
                c_end.state = .setMk ⟨mvIdx, hmvi⟩ ∧
                (c_end.work utmSimTape).head = (if goRight then offset + W else offset - W) ∧
                (c_end.work utmSimTape).cells = cells_A ∧
                (∀ i, i ≠ utmSimTape → c_end.work i = c_s.work i) ∧
                c_end.input = c_s.input ∧ c_end.output = c_s.output ∧
                WorkTapesWF c_end.work ∧
                (∀ i : Fin 4, (c_end.work i).head ≥ 1) := by
            intro rem; induction rem with
            | zero =>
              intro hrem c' hstate' hhead' hcells' hother' hinp' hout' hwf' hheads'
              -- rem = 0: mvStep(0) → setMk in 1 step (idle)
              have hne' : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
                rw [hstate']; simp [applyTransitionTM]
              have hw_ns' : ∀ i, (c'.work i).read ≠ Γ.start :=
                fun i => at_read_ne_start _ (hheads' i) (hwf'.2 i)
              have hw_idle' : ∀ i, (c'.work i).writeAndMove
                  ((readBackWrite ((c'.work i).read)).toΓ) (idleDir ((c'.work i).read)) = c'.work i :=
                fun i => tape_idle_preserve _ (hw_ns' i) (hheads' i)
              have hinp_idle' : c'.input.move (idleDir c'.input.read) = c'.input := by
                simp only [idleDir,
                  (show c'.input.read ≠ Γ.start by rw [hinp', hinp_s, hinp₁₂, hinp_eq]; exact hinp),
                  ↓reduceIte, Tape.move]
              have hout_idle' : c'.output.writeAndMove
                  ((readBackWrite c'.output.read).toΓ) (idleDir c'.output.read) = c'.output :=
                tape_idle_preserve _
                  (by rw [hout', hout_s, hout₁₂, hout_eq]; exact hout)
                  (by rw [hout', hout_s, hout₁₂, hout_eq]; exact hout_h)
              refine ⟨{ state := .setMk ⟨mvIdx, hmvi⟩, input := c'.input,
                         work := c'.work, output := c'.output },
                      .step ?_ .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · -- step proof
                simp only [TM.step, hne', ↓reduceIte]
                congr 1; rw [hstate']; simp only [applyTransitionTM]
                simp only [ite_true]
                exact Cfg.mk.injEq .. ▸ ⟨rfl, hinp_idle', funext hw_idle', hout_idle'⟩
              · -- head
                simp only []; rw [hhead']; simp only [Nat.sub_zero]
              · exact hcells'
              · exact hother'
              · exact hinp'
              · exact hout'
              · exact hwf'
              · exact hheads'
            | succ r ihr =>
              intro hrem c' hstate' hhead' hcells' hother' hinp' hout' hwf' hheads'
              -- rem = r+1 > 0: mvStep(r+1) → mvStep(r) in 1 step, then recurse
              have hne' : c'.state ≠ (applyTransitionTM (n := n) k).qhalt := by
                rw [hstate']; simp [applyTransitionTM]
              have hw_ns' : ∀ i, (c'.work i).read ≠ Γ.start :=
                fun i => at_read_ne_start _ (hheads' i) (hwf'.2 i)
              have hw_idle' : ∀ i, i ≠ utmSimTape →
                  (c'.work i).writeAndMove ((readBackWrite ((c'.work i).read)).toΓ)
                    (idleDir ((c'.work i).read)) = c'.work i :=
                fun i hi => tape_idle_preserve _ (hw_ns' i) (hheads' i)
              have hinp_idle' : c'.input.move (idleDir c'.input.read) = c'.input := by
                simp only [idleDir,
                  (show c'.input.read ≠ Γ.start by rw [hinp', hinp_s, hinp₁₂, hinp_eq]; exact hinp),
                  ↓reduceIte, Tape.move]
              have hout_idle' : c'.output.writeAndMove
                  ((readBackWrite c'.output.read).toΓ) (idleDir c'.output.read) = c'.output :=
                tape_idle_preserve _
                  (by rw [hout', hout_s, hout₁₂, hout_eq]; exact hout)
                  (by rw [hout', hout_s, hout₁₂, hout_eq]; exact hout_h)
              -- Sim tape direction: if goRight then right else (if read = start then right else left)
              -- Since head ≥ 1 and WF, read ≠ start, so direction = if goRight then right else left
              have hsim_ns' : (c'.work utmSimTape).read ≠ Γ.start := hw_ns' utmSimTape
              -- Build the sim tape write and move
              have hsim_wam' : (c'.work utmSimTape).writeAndMove
                  ((readBackWrite ((c'.work utmSimTape).read)).toΓ)
                  (if goRight then Dir3.right else Dir3.left) =
                  ⟨if goRight then (c'.work utmSimTape).head + 1
                    else (c'.work utmSimTape).head - 1,
                   (c'.work utmSimTape).cells⟩ := by
                have hh_ne_zero : ¬(c'.work utmSimTape).head = 0 := by
                  have := hheads' utmSimTape; omega
                have hrb : (readBackWrite ((c'.work utmSimTape).read)).toΓ =
                    (c'.work utmSimTape).read :=
                  readBackWrite_toΓ_eq (hwf'.2 utmSimTape _ (hheads' utmSimTape))
                rw [hrb]
                simp only [Tape.writeAndMove, Tape.write, hh_ne_zero, ↓reduceIte,
                  Tape.read, Function.update_eq_self]
                cases goRight <;> simp [Tape.move]
              -- New head value
              set newHead := if goRight then (c'.work utmSimTape).head + 1
                  else (c'.work utmSimTape).head - 1
              set c_next : Cfg 4 (applyTransitionTM (n := n) k).Q :=
                { state := .mvStep ⟨mvIdx, hmvi⟩ goRight ⟨r, by omega⟩
                  input := c'.input
                  work := fun i => if i = utmSimTape
                    then ⟨newHead, (c'.work utmSimTape).cells⟩
                    else c'.work i
                  output := c'.output }
              -- The direction in the δ matches: after simplification both branches
              -- reduce to (if goRight then right else left) since read ≠ start
              have hstep' : (applyTransitionTM (n := n) k).step c' = some c_next := by
                simp only [TM.step, hne', ↓reduceIte]
                congr 1; rw [hstate']; simp only [applyTransitionTM]
                simp only [show (r + 1 : ℕ) ≠ 0 from by omega,
                  ↓reduceIte, hsim_ns', c_next, Cfg.mk.injEq]
                refine ⟨?_, hinp_idle', funext fun i => ?_, hout_idle'⟩
                · rfl
                · by_cases hi : i = utmSimTape
                  · subst hi; simp only [↓reduceIte]; exact hsim_wam'
                  · simp only [hi, ↓reduceIte]; exact hw_idle' i hi
              -- c_next properties
              have hn_head : (c_next.work utmSimTape).head =
                  (if goRight then offset + (W - r) else offset - (W - r)) := by
                simp only [c_next, ↓reduceIte, newHead]
                rw [hhead']; split <;> omega
              have hn_cells : (c_next.work utmSimTape).cells = cells_A := by
                simp [c_next, hcells']
              have hn_other : ∀ i, i ≠ utmSimTape → c_next.work i = c_s.work i := by
                intro i hi; simp [c_next, hi]; exact hother' i hi
              have hn_wf : WorkTapesWF c_next.work := by
                constructor
                · intro i; by_cases hi : i = utmSimTape
                  · simp [c_next, hi, hwf'.1 utmSimTape]
                  · simp [c_next, hi, hwf'.1 i]
                · intro i j hj; by_cases hi : i = utmSimTape
                  · simp only [c_next, hi, ↓reduceIte]; exact hwf'.2 utmSimTape j hj
                  · simp only [c_next, hi, ↓reduceIte]; exact hwf'.2 i j hj
              have hn_heads : ∀ i : Fin 4, (c_next.work i).head ≥ 1 := by
                intro i; by_cases hi : i = utmSimTape
                · subst hi; rw [hn_head]; split
                  · omega
                  · -- left case: need offset - (W - r) ≥ 1
                    -- goRight = false means dir = left
                    have hgl : goRight = false := by
                      rename_i hgr; exact Bool.eq_false_iff.mpr hgr
                    have : dir = Dir3.left := by
                      rcases hdir with h | h
                      · exact h
                      · exfalso; simp [hgoRight_def, h] at hgl
                    have := hoff_large this; omega
                · rw [hn_other i hi]; exact hw_heads_s i
              obtain ⟨c_end, hr, hst_end, hh_end, hc_end, ho_end, hi_end, hou_end,
                      hwf_end, hheads_end⟩ :=
                ihr (by omega) c_next
                  (by simp [c_next])
                  hn_head hn_cells hn_other
                  (by simp [c_next, hinp']) (by simp [c_next, hout'])
                  hn_wf hn_heads
              exact ⟨c_end, .step hstep' hr, hst_end, hh_end, hc_end, ho_end,
                     hi_end, hou_end, hwf_end, hheads_end⟩
          -- Apply the loop to c_A with rem = W
          obtain ⟨c_B, hreach_B, hst_B, hhead_B, hcells_B, hother_B,
                  hinp_B, hout_B, hwf_B, hheads_B⟩ :=
            hmvStep_loop W (le_refl _) c_A
              (by simp [c_A]) (by simp [c_A, hA_head]) hA_cells
              hA_other hA_inp hA_out hA_wf hA_heads
          -- Chain C: setMk → rwMv (1 step)
          have hne_B : c_B.state ≠ (applyTransitionTM (n := n) k).qhalt := by
            rw [hst_B]; simp [applyTransitionTM]
          have hw_ns_B : ∀ i, (c_B.work i).read ≠ Γ.start :=
            fun i => at_read_ne_start _ (hheads_B i) (hwf_B.2 i)
          have hw_idle_B : ∀ i, i ≠ utmSimTape →
              (c_B.work i).writeAndMove ((readBackWrite ((c_B.work i).read)).toΓ)
                (idleDir ((c_B.work i).read)) = c_B.work i :=
            fun i hi => tape_idle_preserve _ (hw_ns_B i) (hheads_B i)
          have hinp_idle_B : c_B.input.move (idleDir c_B.input.read) = c_B.input := by
            simp only [idleDir,
              (show c_B.input.read ≠ Γ.start by rw [hinp_B, hinp_s, hinp₁₂, hinp_eq]; exact hinp),
              ↓reduceIte, Tape.move]
          have hout_idle_B : c_B.output.writeAndMove
              ((readBackWrite c_B.output.read).toΓ) (idleDir c_B.output.read) = c_B.output :=
            tape_idle_preserve _
              (by rw [hout_B, hout_s, hout₁₂, hout_eq]; exact hout)
              (by rw [hout_B, hout_s, hout₁₂, hout_eq]; exact hout_h)
          -- setMk writes Γw.one at current sim tape head
          have hsim_write_B : (c_B.work utmSimTape).writeAndMove
              Γw.one.toΓ (idleDir ((c_B.work utmSimTape).read)) =
              ⟨(c_B.work utmSimTape).head,
               Function.update (c_B.work utmSimTape).cells
                 (c_B.work utmSimTape).head Γ.one⟩ := by
            simp only [Tape.writeAndMove, Tape.write,
              show ¬(c_B.work utmSimTape).head = 0 from by have := hheads_B utmSimTape; omega,
              ↓reduceIte, Tape.move]
            simp only [Γw.toΓ, idleDir, hw_ns_B utmSimTape, ↓reduceIte, Tape.move]
          set c_C : Cfg 4 (applyTransitionTM (n := n) k).Q :=
            { state := .rwMv ⟨mvIdx, hmvi⟩
              input := c_B.input
              work := fun i => if i = utmSimTape
                then ⟨(c_B.work utmSimTape).head,
                      Function.update (c_B.work utmSimTape).cells
                        (c_B.work utmSimTape).head Γ.one⟩
                else c_B.work i
              output := c_B.output }
          have hstep_C : (applyTransitionTM (n := n) k).step c_B = some c_C := by
            simp only [TM.step, hne_B, ↓reduceIte]
            congr 1; rw [hst_B]; simp only [applyTransitionTM, c_C, Cfg.mk.injEq]
            exact ⟨trivial, hinp_idle_B, funext fun i => by
              by_cases hi : i = utmSimTape
              · subst hi; simp only [↓reduceIte]; exact hsim_write_B
              · simp only [hi, ↓reduceIte]
                exact tape_idle_preserve _ (hw_ns_B i) (hheads_B i),
              hout_idle_B⟩
          -- Assembly: c_s →[1] c_A →[W+1] c_B →[1] c_C
          -- Total: 1 + (W + 1) + 1 = W + 3 steps
          refine ⟨_, c_C,
            .step hstep_A (reachesIn_trans _ hreach_B (.step hstep_C .zero)),
            rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- Marker preservation: for ti ≥ mvIdx + 1
            intro ti hti pos
            simp only [c_C, ↓reduceIte]
            -- Key arithmetic: simTapeOffset pos ti uses column 3*ti,
            -- but offset (and offset ± W) use column 3*mvIdx.
            -- Since ti ≥ mvIdx + 1 and both < n+2, 3*ti ≠ 3*mvIdx mod (3*(n+2)).
            -- Column-separation lemma: simTapeOffset _ _ ti ≠ simTapeOffset _ _ mvIdx
            -- because ti > mvIdx and both < n+2, so 3*ti mod W ≠ 3*mvIdx mod W
            have hcol_ne : ∀ (p q : ℕ),
                SuperCell.simTapeOffset (n + 2) p ti.val ≠
                SuperCell.simTapeOffset (n + 2) q mvIdx := by
              intro p q heq
              simp only [SuperCell.simTapeOffset, SuperCell.width] at heq
              -- heq : 1 + p * (3*(n+2)) + 3*ti = 1 + q * (3*(n+2)) + 3*mvIdx
              -- This means p * (3*(n+2)) + 3*ti = q * (3*(n+2)) + 3*mvIdx
              -- Taking mod (3*(n+2)): 3*ti mod W = 3*mvIdx mod W
              -- Since both < W, we get 3*ti = 3*mvIdx, contradicting ti ≥ mvIdx+1
              have h1 : (p * (3 * (n + 2)) + (1 + 3 * ti.val)) % (3 * (n + 2)) =
                  (1 + 3 * ti.val) % (3 * (n + 2)) := by
                rw [Nat.mul_comm]; exact Nat.mul_add_mod (3 * (n + 2)) p _
              have h2 : (q * (3 * (n + 2)) + (1 + 3 * mvIdx)) % (3 * (n + 2)) =
                  (1 + 3 * mvIdx) % (3 * (n + 2)) := by
                rw [Nat.mul_comm]; exact Nat.mul_add_mod (3 * (n + 2)) q _
              have heq' : p * (3 * (n + 2)) + (1 + 3 * ti.val) =
                  q * (3 * (n + 2)) + (1 + 3 * mvIdx) := by omega
              have h3 : (1 + 3 * ti.val) % (3 * (n + 2)) = (1 + 3 * mvIdx) % (3 * (n + 2)) := by
                rw [← h1, heq', h2]
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
              omega
            have hsto_ne_offset : SuperCell.simTapeOffset (n + 2) pos ti.val ≠ offset := by
              exact hcol_ne pos target_head
            have hsto_ne_head : SuperCell.simTapeOffset (n + 2) pos ti.val ≠
                (c_B.work utmSimTape).head := by
              intro heq
              -- c_B head = offset ± W. Either way, it differs from simTapeOffset pos ti
              -- because it's in column mvIdx while ti > mvIdx.
              rw [hhead_B] at heq
              split at heq
              · -- right: head = offset + W
                have hoff_add : offset + W =
                    SuperCell.simTapeOffset (n + 2) (target_head + 1) mvIdx := by
                  simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width]
                  rw [Nat.add_mul]; omega
                exact hcol_ne pos (target_head + 1) (heq.trans hoff_add)
              · -- left: head = offset - W
                have hoff_ge_W : offset ≥ W := by
                  have hgl : ¬ (goRight = true) := by rename_i h; exact h
                  have : dir = Dir3.left := by
                    rcases hdir with h | h; exact h
                    exfalso; simp [hgoRight_def, h] at hgl
                  have := hoff_large this; omega
                have hoff_sub : offset - W =
                    SuperCell.simTapeOffset (n + 2) (target_head - 1) mvIdx := by
                  have hth_pos : target_head ≥ 1 := by
                    by_contra h; push_neg at h
                    have : target_head = 0 := by omega
                    simp [this] at hoffset_expand; omega
                  simp only [SuperCell.simTapeOffset, SuperCell.width]
                  have hoff_val : offset = 1 + target_head * W + 3 * mvIdx := by omega
                  have hth_eq : target_head - 1 + 1 = target_head := Nat.sub_add_cancel hth_pos
                  have hmul : (target_head - 1) * (3 * (n + 2)) + 3 * (n + 2) =
                      target_head * (3 * (n + 2)) := by
                    conv_rhs => rw [← hth_eq, Nat.add_mul]; simp
                  rw [← hmul] at hoff_val; omega
                exact hcol_ne pos (target_head - 1) (heq.trans hoff_sub)
            rw [hcells_B, Function.update_of_ne hsto_ne_head]
            simp only [cells_A, Function.update_of_ne hsto_ne_offset]
          · -- Other tapes preserved
            intro i hi; simp [c_C, hi]; rw [hother_B i hi]
          · -- Input
            simp [c_C, hinp_B]
          · -- Output
            simp [c_C, hout_B]
          · -- WF
            constructor
            · intro i; by_cases hi : i = utmSimTape
              · subst hi; simp only [c_C, ↓reduceIte]
                rw [Function.update_of_ne (show (0 : ℕ) ≠ (c_B.work utmSimTape).head from by
                  have := hheads_B utmSimTape; omega)]
                rw [hcells_B]; simp only [cells_A]
                rw [Function.update_of_ne (show (0 : ℕ) ≠ offset from by omega)]
                exact hwf_s.1 utmSimTape
              · simp [c_C, hi, hwf_B.1 i]
            · intro i j hj; by_cases hi : i = utmSimTape
              · subst hi; simp only [c_C, ↓reduceIte]
                by_cases hj1 : j = (c_B.work utmSimTape).head
                · subst hj1; simp [Function.update_self]
                · rw [Function.update_of_ne hj1, hcells_B]
                  simp only [cells_A]
                  by_cases hj2 : j = offset
                  · subst hj2; simp [Function.update_self]
                  · rw [Function.update_of_ne hj2]
                    exact hwf_s.2 utmSimTape j hj
              · simp only [c_C, hi, ↓reduceIte]; exact hwf_B.2 i j hj
          · -- Heads ≥ 1
            intro i; by_cases hi : i = utmSimTape
            · subst hi; simp only [c_C, ↓reduceIte]
              rw [hhead_B]; split
              · omega
              · -- goRight = false means dir = left
                have hgl : goRight = false := by
                  rename_i hgr; exact Bool.eq_false_iff.mpr hgr
                have : dir = Dir3.left := by
                  rcases hdir with h | h
                  · exact h
                  · exfalso; simp [hgoRight_def, h] at hgl
                have := hoff_large this; omega
            · simp [c_C, hi]; exact hheads_B i
          · -- Symbol cells preserved (at +1 and +2 offsets)
            -- c_C.sim.cells = update (update c_s.sim.cells offset blank) c_B.head one
            -- For j = simTapeOffset + 1 or + 2: j ≠ offset and j ≠ c_B.head
            -- because offset and c_B.head are simTapeOffset positions ((j-1)%3 = 0)
            -- while +1 has (j-1)%3 = 1 and +2 has (j-1)%3 = 2.
            intro pos tapeIdx; constructor
            · -- +1 case
              simp only [c_C, ↓reduceIte]
              rw [Function.update_of_ne (show SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1 ≠
                  (c_B.work utmSimTape).head from by
                rw [hhead_B]; split
                · simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                  rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                  omega
                · simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                  rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                  omega)]
              rw [hcells_B]; simp only [cells_A]
              rw [Function.update_of_ne (show SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1 ≠
                  offset from by
                simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                omega)]
            · -- +2 case
              simp only [c_C, ↓reduceIte]
              rw [Function.update_of_ne (show SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2 ≠
                  (c_B.work utmSimTape).head from by
                rw [hhead_B]; split
                · simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                  rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                  omega
                · simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                  rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                  omega)]
              rw [hcells_B]; simp only [cells_A]
              rw [Function.update_of_ne (show SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2 ≠
                  offset from by
                simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]
                rw [Nat.mul_left_comm pos 3 (n + 2), Nat.mul_left_comm target_head 3 (n + 2)]
                omega)]
          · -- Current tape marker at newHead_cur
            intro pos; simp only [c_C, ↓reduceIte]
            -- Establish key facts: c_B.head = sto newHead_cur mvIdx, offset = sto target_head mvIdx
            -- All sim tape modifications are at offset (cleared to blank) and c_B.head (set to one).
            -- For any pos: sto pos mvIdx hits c_B.head iff pos = newHead_cur,
            --              sto pos mvIdx hits offset iff pos = target_head.
            -- Helper: simTapeOffset is injective in its position argument (for fixed tapeIdx)
            have hsto_inj : ∀ (a b : ℕ),
                SuperCell.simTapeOffset (n + 2) a mvIdx = SuperCell.simTapeOffset (n + 2) b mvIdx → a = b := by
              intro a b heq
              simp only [SuperCell.simTapeOffset, SuperCell.width] at heq
              -- heq : 1 + a * (3*(n+2)) + 3*mvIdx = 1 + b * (3*(n+2)) + 3*mvIdx
              have hmul : a * (3 * (n + 2)) = b * (3 * (n + 2)) := by omega
              by_contra hab
              have : a < b ∨ b < a := by omega
              rcases this with h | h
              · have := (Nat.mul_lt_mul_right (show 3 * (n + 2) > 0 by omega)).mpr h; omega
              · have := (Nat.mul_lt_mul_right (show 3 * (n + 2) > 0 by omega)).mpr h; omega
            -- c_B.head = sto newHead_cur mvIdx
            have hhead_is_sto : (c_B.work utmSimTape).head =
                SuperCell.simTapeOffset (n + 2) newHead_cur mvIdx := by
              rw [hhead_B]; rcases hdir with hd | hd <;> subst hd
              · -- left: goRight = false, head = offset - W, newHead_cur = target_head - 1
                have hgl : goRight = false := by simp [hgoRight_def]
                simp only [hgl, ↓reduceIte, hnewHead_cur_def]
                -- After subst (dir = left), newHead_cur reduces to target_head - 1
                have hth_pos : target_head ≥ 1 := by
                  by_contra h; push_neg at h
                  have htz : target_head = 0 := by omega
                  have hol := hoff_large (by rfl)
                  rw [hoffset_def, htz] at hol
                  simp only [SuperCell.simTapeOffset, SuperCell.width] at hol; omega
                -- Goal: offset - W = 1 + (target_head - 1) * (3 * (n + 2)) + 3 * mvIdx
                -- Rewrite (target_head - 1) + 1 = target_head
                have hth_eq : (target_head - 1) + 1 = target_head := Nat.sub_add_cancel hth_pos
                rw [hoffset_def]; simp only [SuperCell.simTapeOffset, SuperCell.width]
                -- Need: 1 + target_head * (3*(n+2)) + 3*mvIdx - 3*(n+2)
                --     = 1 + (target_head - 1) * (3*(n+2)) + 3*mvIdx
                have hmul : (target_head - 1) * (3 * (n + 2)) + 3 * (n + 2) =
                    target_head * (3 * (n + 2)) := by
                  conv_rhs => rw [← hth_eq, Nat.add_mul]; simp
                -- Goal: 1 + target_head * (3*(n+2)) + 3*mvIdx - 3*(n+2)
                --     = 1 + (target_head - 1) * (3*(n+2)) + 3*mvIdx
                -- From hmul: target_head * X = (target_head - 1) * X + X
                -- Introduce abbreviation for (target_head - 1) * (3 * (n + 2))
                set X := (target_head - 1) * (3 * (n + 2)) with hX_def
                rw [show target_head * (3 * (n + 2)) = X + 3 * (n + 2) from by rw [hX_def]; exact hmul.symm]
                -- Now goal is purely linear in X; reduce `if False`
                simp (config := { decide := true }) only []
                rw [if_neg (by trivial)]; omega
              · -- right: goRight = true, head = offset + W, newHead_cur = target_head + 1
                have hgr : goRight = true := by simp [hgoRight_def]
                simp only [hgr, ↓reduceIte, hnewHead_cur_def]
                simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width]
                rw [Nat.add_mul]; omega
            -- offset = sto target_head mvIdx (by definition)
            -- Now prove the main goal
            by_cases hpnew : newHead_cur = pos
            · -- pos = newHead_cur: cell should be Γ.one
              subst hpnew; simp only [↓reduceIte]
              rw [show SuperCell.simTapeOffset (n + 2) newHead_cur mvIdx =
                  (c_B.work utmSimTape).head from hhead_is_sto.symm]
              rw [Function.update_self]
            · -- pos ≠ newHead_cur: cell should be Γ.blank
              simp only [hpnew, ↓reduceIte]
              have hsto_ne_head : SuperCell.simTapeOffset (n + 2) pos mvIdx ≠
                  (c_B.work utmSimTape).head := by
                rw [hhead_is_sto]; intro heq; exact hpnew (hsto_inj _ _ heq.symm)
              rw [Function.update_of_ne hsto_ne_head, hcells_B]
              simp only [cells_A]
              by_cases hpo : pos = target_head
              · -- pos = target_head (old position): cleared to blank
                subst hpo; rw [Function.update_self]
              · -- pos ≠ target_head: chain to original which was already blank
                have hsto_ne_off : SuperCell.simTapeOffset (n + 2) pos mvIdx ≠ offset := by
                  rw [hoffset_def]; intro heq; exact hpo (hsto_inj _ _ heq)
                rw [Function.update_of_ne hsto_ne_off, hsimcells_s, hsim₁₂]
                have := hmarker_current pos
                simp only [show ¬(target_head = pos) from fun h => hpo h.symm, ↓reduceIte] at this
                exact this
      obtain ⟨steps_a, c_a, hreach_a, hst_a, hmarkers_a, hother_a,
              hinp_a, hout_a, hwf_a, hheads_a, hsymcells_a, hcur_marker_a⟩ := hstep_to_rwMv
      -- Sub-step B: rwMv loop (using phase2_rwMv_loop)
      have hother_heads_a : ∀ i : Fin 4, i ≠ utmSimTape → (c_a.work i).head ≥ 1 :=
        fun i hi => hheads_a i
      obtain ⟨c_rw, hreach_rw, hst_rw, hsimh_rw, hsimcells_rw,
              hother_rw, hinp_rw, hout_rw, hwf_rw⟩ :=
        phase2_rwMv_loop k ⟨mvIdx, hmvi⟩ (c_a.work utmSimTape).head c_a
          hst_a rfl hwf_a hother_heads_a
          (by rw [hinp_a, hinp_s, hinp₁₂, hinp_eq]; exact hinp)
          (by rw [hinp_a, hinp_s, hinp₁₂, hinp_eq]; exact hinp_h)
          (by rw [hout_a, hout_s, hout₁₂, hout_eq]; exact hout)
          (by rw [hout_a, hout_s, hout₁₂, hout_eq]; exact hout_h)
      -- Sub-step C: rwMvR → next state (1 step)
      have hne_rw : c_rw.state ≠ (applyTransitionTM (n := n) k).qhalt := by
        rw [hst_rw]; simp [applyTransitionTM]
      have hrw_heads : ∀ i : Fin 4, (c_rw.work i).head ≥ 1 := by
        intro i; by_cases hi : i = utmSimTape
        · rw [hi, hsimh_rw]
        · rw [hother_rw i hi]; exact hother_heads_a i hi
      have hw_ns_rw : ∀ i, (c_rw.work i).read ≠ Γ.start :=
        fun i => at_read_ne_start _ (hrw_heads i) (hwf_rw.2 i)
      have hw_idle_rw : ∀ i, (c_rw.work i).writeAndMove
          ((readBackWrite ((c_rw.work i).read)).toΓ) (idleDir ((c_rw.work i).read)) = c_rw.work i :=
        fun i => tape_idle_preserve _ (hw_ns_rw i) (hrw_heads i)
      have hinp_idle_rw : c_rw.input.move (idleDir c_rw.input.read) = c_rw.input := by
        simp only [idleDir, show c_rw.input.read ≠ Γ.start from by
          rw [hinp_rw, hinp_a, hinp_s, hinp₁₂, hinp_eq]; exact hinp, ↓reduceIte, Tape.move]
      have hout_idle_rw : c_rw.output.writeAndMove
          ((readBackWrite c_rw.output.read).toΓ) (idleDir c_rw.output.read) = c_rw.output :=
        tape_idle_preserve _
          (by rw [hout_rw, hout_a, hout_s, hout₁₂, hout_eq]; exact hout)
          (by rw [hout_rw, hout_a, hout_s, hout₁₂, hout_eq]; exact hout_h)
      set c_end : Cfg 4 (applyTransitionTM (n := n) k).Q :=
        { state := if h : mvIdx + 1 < n + 2
                    then ApplyTransQ.rdMvHi ⟨mvIdx + 1, h⟩
                    else ApplyTransQ.clrScr
          input := c_rw.input
          work := c_rw.work
          output := c_rw.output }
      have hstep_end : (applyTransitionTM (n := n) k).step c_rw = some c_end := by
        simp only [TM.step, hne_rw, ↓reduceIte]
        congr 1; rw [hst_rw]; simp only [applyTransitionTM]
        simp only [c_end, Cfg.mk.injEq]
        by_cases hw : (⟨mvIdx, hmvi⟩ : Fin (n + 2)).val + 1 < n + 2 <;>
          simp only [hw, ↓reduceDIte]
        · exact ⟨trivial, hinp_idle_rw, funext hw_idle_rw, hout_idle_rw⟩
        · exact ⟨trivial, hinp_idle_rw, funext hw_idle_rw, hout_idle_rw⟩
      -- Assembly
      refine ⟨_, c_end,
        reachesIn_trans _ hreach_a
          (reachesIn_trans _ hreach_rw (.step hstep_end .zero)),
        rfl, by simp [c_end, hsimh_rw], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- Marker preservation
        intro ti hti pos
        simp only [c_end]
        rw [hsimcells_rw]
        exact hmarkers_a ti hti pos
      · -- Other tapes
        intro i hi; simp [c_end]; rw [hother_rw i hi, hother_a i hi]
      · -- Input
        simp [c_end, hinp_rw, hinp_a]
      · -- Output
        simp [c_end, hout_rw, hout_a]
      · -- WF
        exact ⟨fun i => by simp [c_end, hwf_rw.1 i],
               fun i j hj => by simp [c_end]; exact hwf_rw.2 i j hj⟩
      · -- Symbol cells preserved: chain c_end = c_rw (cells) = c_a (rwMv) → c_s (symcells_a)
        intro pos tapeIdx; constructor
        · simp only [c_end]; rw [hsimcells_rw, (hsymcells_a pos tapeIdx).1]
        · simp only [c_end]; rw [hsimcells_rw, (hsymcells_a pos tapeIdx).2]
      · -- Current tape marker at newHead_cur
        intro pos; simp only [c_end]
        rw [hsimcells_rw]; exact hcur_marker_a pos
    obtain ⟨steps_r, c_r, hreach_r, hst_r, hsimh_r, hsimcells_r,
            hother_r, hinp_r, hout_r, hwf_r, hsymcells_r, hcur_marker_r⟩ := hstep_rest
    -- ── Assembly ──
    have htotal := reachesIn_trans _ hreach₁₂
      (reachesIn_trans _ hreach_s hreach_r)
    -- ── Marker preservation ──
    have hmarkers_end : ∀ (ti : Fin (n + 2)), ti.val ≥ mvIdx + 1 → ∀ pos,
        (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
        if headPos ti = pos then Γ.one else Γ.blank := by
      intro ti hti pos
      rw [hsimcells_r ti (by omega) pos, hsimcells_s, hsim₁₂]
      exact hmarker_inv ti (by omega) pos
    -- ── Heads ≥ 1 ──
    have hheads_end : ∀ i : Fin 4, (c_r.work i).head ≥ 1 := by
      intro i; by_cases hi : i = utmSimTape
      · rw [hi, hsimh_r]
      · rw [hother_r i hi, hother_s i hi]; exact hheads₁₂ i
    -- ── Desc tape ──
    have hdesc_end : c_r.work utmDescTape = c₂.work utmDescTape := by
      have hne_sim : utmDescTape ≠ utmSimTape := by decide
      have hne_scr : utmDescTape ≠ utmScratchTape := by decide
      rw [hother_r utmDescTape hne_sim, hother_s utmDescTape hne_sim,
          hother₁₂ utmDescTape hne_scr hne_sim, hdesc]
    -- ── State tape cells ──
    have hstatecells_end : (c_r.work utmStateTape).cells = (c₂.work utmStateTape).cells := by
      have hne_sim : utmStateTape ≠ utmSimTape := by decide
      have hne_scr : utmStateTape ≠ utmScratchTape := by decide
      rw [show (c_r.work utmStateTape).cells = (c_s.work utmStateTape).cells from
        congr_arg Tape.cells (hother_r utmStateTape hne_sim)]
      rw [hother_s utmStateTape hne_sim, hother₁₂ utmStateTape hne_scr hne_sim, hstatecells]
    -- ── Input/output ──
    have hinp_end : c_r.input = c₂.input := by
      rw [hinp_r, hinp_s, hinp₁₂, hinp_eq]
    have hout_end : c_r.output = c₂.output := by
      rw [hout_r, hout_s, hout₁₂, hout_eq]
    -- ── Symbol cells preserved ──
    have hsymcells_end : ∀ pos tapeIdx,
        (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
        (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) := by
      intro pos tapeIdx; constructor
      · rw [(hsymcells_r pos tapeIdx).1, hsimcells_s, hsim₁₂]
      · rw [(hsymcells_r pos tapeIdx).2, hsimcells_s, hsim₁₂]
    -- ── Scratch head tracking ──
    have hscrh_end : (c_r.work utmScratchTape).head = (c₂.work utmScratchTape).head + 2 * (mvIdx + 1) := by
      have hne_sim : utmScratchTape ≠ utmSimTape := by decide
      rw [show (c_r.work utmScratchTape).head = (c_s.work utmScratchTape).head from
        congr_arg Tape.head (hother_r utmScratchTape hne_sim)]
      rw [hother_s utmScratchTape hne_sim, hscrh₁₂, hscratch_head]
      omega
    -- ── Scratch cells tracking ──
    have hscrc_end : (c_r.work utmScratchTape).cells = (c₂.work utmScratchTape).cells := by
      have hne_sim : utmScratchTape ≠ utmSimTape := by decide
      rw [show (c_r.work utmScratchTape).cells = (c_s.work utmScratchTape).cells from
        congr_arg Tape.cells (hother_r utmScratchTape hne_sim)]
      rw [hother_s utmScratchTape hne_sim, hscrc₁₂, hscratch_cells]
    -- ── Processed markers: previous + current tape ──
    have hprocessed_end : ∀ (ti : Fin (n + 2)), ti.val < mvIdx + 1 → ∀ pos,
        (c_r.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
        if newHeadPos ti = pos then Γ.one else Γ.blank := by
      intro ti hti pos
      by_cases hcur : ti.val = mvIdx
      · -- Current tape: use hcur_marker_r
        have hpf : ti = ⟨mvIdx, hmvi⟩ := by ext; exact hcur
        rw [hpf]
        rw [hcur_marker_r pos]
        -- Need: newHead_cur = newHeadPos ⟨mvIdx, hmvi⟩
        -- newHead_cur = match dir with .stay => target_head | .right => target_head + 1 | .left => target_head - 1
        -- target_head = headPos ⟨mvIdx, hmvi⟩
        -- dir = decodeDir3 c.scratch.cells[c.scratch.head] c.scratch.cells[c.scratch.head + 1]
        --     = decodeDir3 c₂.scratch.cells[c₂.head + 2*mvIdx] c₂.scratch.cells[c₂.head + 2*mvIdx + 1]
        -- hnewHead says newHeadPos ⟨mvIdx, hmvi⟩ = match decoded_dir with ...
        -- Goal: newHead_cur = newHeadPos ⟨mvIdx, hmvi⟩
        -- Rewrite newHead_cur using dir = decoded direction from scratch
        rw [hnewHead ⟨mvIdx, hmvi⟩]
        simp only [Fin.val, hnewHead_cur_def, htarget_def, hdir₁₂, hscratch_cells, hscratch_head]
      · -- Previously processed tape: chain c_r → c_s → c₁₂ → c
        have hlt : ti.val < mvIdx := by omega
        -- hsimcells_r now covers all ti ≠ mvIdx
        rw [hsimcells_r ti (by omega) pos, hsimcells_s, hsim₁₂]
        exact hprocessed_markers ti hlt pos
    -- ── WF ──
    exact ⟨_, c_r, htotal, hst_r, hsimh_r, hwf_r, hheads_end,
      hmarkers_end, hdesc_end, hstatecells_end, hinp_end, hout_end, hsymcells_end,
      hscrh_end, hscrc_end, hprocessed_end⟩

-- ════════════════════════════════════════════════════════════════════════

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
private theorem encodeTransOutput_state_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (j : ℕ) (hj : j < k') :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[j]? =
      some (j == q'.val) := by
  simp [TMEncoding.encodeTransOutput, List.getElem?_append_left, hj]
  exact Fin.ext_iff

-- ════════════════════════════════════════════════════════════════════════
-- Round-trip lemmas for decodeDir3 / decodeΓw
-- ════════════════════════════════════════════════════════════════════════

/-- Extract element from flatMap of fixed-length-2 sublists over finRange. -/
private theorem flatMap_encode2_getElem' (n' : ℕ)
    (f : Fin n' → List Bool) (hlen : ∀ i, (f i).length = 2)
    (j : ℕ) (hj : j < n') (b : ℕ) (hb : b < 2) :
    ((List.finRange n').flatMap f)[2 * j + b]? =
      some ((f ⟨j, hj⟩)[b]'(by rw [hlen]; exact hb)) := by
  induction n' generalizing j with
  | zero => omega
  | succ m ih =>
    rw [List.finRange_succ, List.flatMap_cons]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [List.getElem?_append_left (by rw [hlen]; exact hb)]
      rw [show (0 : Fin (m+1)) = ⟨0, hj⟩ from Fin.ext rfl]
      exact List.getElem?_eq_getElem _
    · rw [List.getElem?_append_right (by rw [hlen]; omega)]
      rw [hlen, show 2 * j + b - 2 = 2 * (j - 1) + b from by omega]
      rw [List.flatMap_map]
      have hj' : j - 1 < m := by omega
      rw [ih (fun i => f (Fin.succ i)) (fun i => hlen _) (j - 1) hj']
      have heq : (⟨j - 1, hj'⟩ : Fin m).succ = (⟨j, hj⟩ : Fin (m+1)) := by
        ext; simp [Fin.val_mk]; omega
      simp only [heq]

/-- writeAndMove preserves cells at non-head positions. -/
private theorem Tape.writeAndMove_cells_ne (t : Tape) (g : Γ) (d : Dir3)
    (pos : ℕ) (hne : pos ≠ t.head) :
    (t.writeAndMove g d).cells pos = t.cells pos := by
  simp only [Tape.writeAndMove, Tape.write]
  split
  · simp only [Tape.move]; cases d <;> simp
  · rename_i hh0; simp only [Tape.move]; cases d <;> simp [Function.update, hne]

/-- writeAndMove at head with head ≠ 0 gives the new value. -/
private theorem Tape.writeAndMove_cells_head (t : Tape) (g : Γ) (d : Dir3)
    (hne : t.head ≠ 0) :
    (t.writeAndMove g d).cells t.head = g := by
  simp only [Tape.writeAndMove, Tape.write, hne, ite_false]
  simp only [Tape.move]; cases d <;> simp [Function.update]

private theorem decodeDir3_ofBool_encode (d : Dir3) :
    decodeDir3 (Γ.ofBool (d.encode[0]'(by cases d <;> decide)))
               (Γ.ofBool (d.encode[1]'(by cases d <;> decide))) = d := by
  cases d <;> rfl

private theorem decodeΓw_ofBool_encode (w : Γw) :
    decodeΓw (Γ.ofBool (w.encode[0]'(by cases w <;> decide)))
             (Γ.ofBool (w.encode[1]'(by cases w <;> decide))) = w := by
  cases w <;> rfl

/-- Length of encoding flatMaps (local copy to avoid import issues). -/
private theorem flatMap_Dir3_encode_length' (l : List α) (f : α → Dir3) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Dir3.encode_length, ih, List.length_cons]
    omega

private theorem flatMap_Γw_encode_length' (l : List α) (f : α → Γw) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Γw.encode_length, ih, List.length_cons]
    omega

/-- Length of `encodeTransOutput`. -/
private theorem encodeTransOutput_length' (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD).length =
      k' + 4 * n' + 6 := by
  simp only [TMEncoding.encodeTransOutput, List.length_append, List.length_map,
    List.length_finRange, Γw.encode_length, Dir3.encode_length,
    flatMap_Γw_encode_length', flatMap_Dir3_encode_length']
  omega

/-- Extract write bits: for wrIdx < n, bits at k + 2*wrIdx encode (wW wrIdx). -/
private theorem encodeTransOutput_write_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (wrIdx : ℕ) (hwi : wrIdx < n') (b : ℕ) (hb : b < 2) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[k' + 2 * wrIdx + b]? =
      some ((wW ⟨wrIdx, hwi⟩).encode[b]'(by rw [Γw.encode_length]; exact hb)) := by
  simp only [TMEncoding.encodeTransOutput]
  have hlen_q : ((List.finRange k').map (fun i => i == q')).length = k' := by simp
  have hlen_ww : ((List.finRange n').flatMap (fun i => (wW i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wW i).encode) =
        (List.finRange n').flatMap (fun i => Γw.encode (wW i)) from rfl]
    rw [flatMap_Γw_encode_length']; simp
  have hlen_wd : ((List.finRange n').flatMap (fun i => (wD i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wD i).encode) =
        (List.finRange n').flatMap (fun i => Dir3.encode (wD i)) from rfl]
    rw [flatMap_Dir3_encode_length']; simp
  have hlen_ow : oW.encode.length = 2 := Γw.encode_length _
  have hlen_id : iD.encode.length = 2 := Dir3.encode_length _
  have hlen_od : oD.encode.length = 2 := Dir3.encode_length _
  -- Skip past oD (rightmost)
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]; omega)]
  -- Skip past wD dirs
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow, hlen_id]; omega)]
  -- Skip past iD
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow]; omega)]
  -- Skip past oW
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww]; omega)]
  -- Skip past q' bits (use append_right)
  rw [List.getElem?_append_right (by simp only [hlen_q]; omega)]
  simp only [hlen_q]
  rw [show k' + 2 * wrIdx + b - k' = 2 * wrIdx + b from by omega]
  exact flatMap_encode2_getElem' n' (fun i => (wW i).encode) (fun i => Γw.encode_length _) wrIdx hwi b hb

/-- Extract output write bits: bits at k + 2*n encode oW. -/
private theorem encodeTransOutput_owrite_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (b : ℕ) (hb : b < 2) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[k' + 2 * n' + b]? =
      some (oW.encode[b]'(by rw [Γw.encode_length]; exact hb)) := by
  simp only [TMEncoding.encodeTransOutput]
  have hlen_q : ((List.finRange k').map (fun i => i == q')).length = k' := by simp
  have hlen_ww : ((List.finRange n').flatMap (fun i => (wW i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wW i).encode) =
        (List.finRange n').flatMap (fun i => Γw.encode (wW i)) from rfl]
    rw [flatMap_Γw_encode_length']; simp
  have hlen_wd : ((List.finRange n').flatMap (fun i => (wD i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wD i).encode) =
        (List.finRange n').flatMap (fun i => Dir3.encode (wD i)) from rfl]
    rw [flatMap_Dir3_encode_length']; simp
  have hlen_ow : oW.encode.length = 2 := Γw.encode_length _
  have hlen_id : iD.encode.length = 2 := Dir3.encode_length _
  -- Skip past oD, wD dirs, iD
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]; omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow, hlen_id]; omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow]; omega)]
  -- Now at (L₁ ++ L₂) ++ oW.encode, skip past L₁ ++ L₂
  rw [List.getElem?_append_right (by
    simp only [List.length_append, hlen_q, hlen_ww]; omega)]
  simp only [List.length_append, hlen_q, hlen_ww]
  rw [show k' + 2 * n' + b - (k' + 2 * n') = b from by omega]
  rw [List.getElem?_eq_getElem (by rw [hlen_ow]; exact hb)]

/-- Extract iD bits: bits at k + 2n + 2 encode iD. -/
private theorem encodeTransOutput_idir_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (b : ℕ) (hb : b < 2) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[k' + 2 * n' + 2 + b]? =
      some (iD.encode[b]'(by rw [Dir3.encode_length]; exact hb)) := by
  simp only [TMEncoding.encodeTransOutput]
  have hlen_q : ((List.finRange k').map (fun i => i == q')).length = k' := by simp
  have hlen_ww : ((List.finRange n').flatMap (fun i => (wW i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wW i).encode) =
        (List.finRange n').flatMap (fun i => Γw.encode (wW i)) from rfl]
    rw [flatMap_Γw_encode_length']; simp
  have hlen_wd : ((List.finRange n').flatMap (fun i => (wD i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wD i).encode) =
        (List.finRange n').flatMap (fun i => Dir3.encode (wD i)) from rfl]
    rw [flatMap_Dir3_encode_length']; simp
  have hlen_ow : oW.encode.length = 2 := Γw.encode_length _
  have hlen_id : iD.encode.length = 2 := Dir3.encode_length _
  have hlen_od : oD.encode.length = 2 := Dir3.encode_length _
  -- Skip past L₆ = oD.encode
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]; omega)]
  -- Skip past L₅ = flatMap wD dirs
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow, hlen_id]; omega)]
  -- Now at ((L₁ ++ L₂) ++ L₃) ++ L₄, use append_right to skip L₁++L₂++L₃
  rw [List.getElem?_append_right (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow]; omega)]
  -- Simplify the index subtraction
  simp only [List.length_append, hlen_q, hlen_ww, hlen_ow]
  rw [show k' + 2 * n' + 2 + b - (k' + 2 * n' + 2) = b from by omega]
  rw [List.getElem?_eq_getElem (by rw [hlen_id]; exact hb)]

/-- Extract work direction bits: for j < n, bits at k+2n+4+2j encode (wD j). -/
private theorem encodeTransOutput_wdir_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (j : ℕ) (hj : j < n') (b : ℕ) (hb : b < 2) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[k' + 2 * n' + 4 + 2 * j + b]? =
      some ((wD ⟨j, hj⟩).encode[b]'(by rw [Dir3.encode_length]; exact hb)) := by
  simp only [TMEncoding.encodeTransOutput]
  have hlen_q : ((List.finRange k').map (fun i => i == q')).length = k' := by simp
  have hlen_ww : ((List.finRange n').flatMap (fun i => (wW i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wW i).encode) =
        (List.finRange n').flatMap (fun i => Γw.encode (wW i)) from rfl]
    rw [flatMap_Γw_encode_length']; simp
  have hlen_wd : ((List.finRange n').flatMap (fun i => (wD i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wD i).encode) =
        (List.finRange n').flatMap (fun i => Dir3.encode (wD i)) from rfl]
    rw [flatMap_Dir3_encode_length']; simp
  have hlen_ow : oW.encode.length = 2 := Γw.encode_length _
  have hlen_id : iD.encode.length = 2 := Dir3.encode_length _
  -- Skip past L₆ = oD.encode (use append_left)
  rw [List.getElem?_append_left (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]; omega)]
  -- Skip past L₁..L₄ = q' bits ++ wW writes ++ oW ++ iD (use append_right)
  rw [List.getElem?_append_right (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_ow, hlen_id]; omega)]
  simp only [List.length_append, hlen_q, hlen_ww, hlen_ow, hlen_id]
  rw [show k' + 2 * n' + 4 + 2 * j + b - (k' + 2 * n' + 2 + 2) = 2 * j + b from by omega]
  -- Now need: flatMap[2*j+b]? = some (wD ⟨j,hj⟩).encode[b]
  exact flatMap_encode2_getElem' n' (fun i => (wD i).encode) (fun i => Dir3.encode_length _) j hj b hb

/-- Extract oD bits: bits at k+4n+4 encode oD. -/
private theorem encodeTransOutput_odir_bits (k' n' : ℕ) (q' : Fin k')
    (wW : Fin n' → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n' → Dir3) (oD : Dir3)
    (b : ℕ) (hb : b < 2) :
    (TMEncoding.encodeTransOutput k' n' q' wW oW iD wD oD)[k' + 4 * n' + 4 + b]? =
      some (oD.encode[b]'(by rw [Dir3.encode_length]; exact hb)) := by
  simp only [TMEncoding.encodeTransOutput]
  have hlen_q : ((List.finRange k').map (fun i => i == q')).length = k' := by simp
  have hlen_ww : ((List.finRange n').flatMap (fun i => (wW i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wW i).encode) =
        (List.finRange n').flatMap (fun i => Γw.encode (wW i)) from rfl]
    rw [flatMap_Γw_encode_length']; simp
  have hlen_wd : ((List.finRange n').flatMap (fun i => (wD i).encode)).length = 2 * n' := by
    rw [show (List.finRange n').flatMap (fun i => (wD i).encode) =
        (List.finRange n').flatMap (fun i => Dir3.encode (wD i)) from rfl]
    rw [flatMap_Dir3_encode_length']; simp
  have hlen_ow : oW.encode.length = 2 := Γw.encode_length _
  have hlen_id : iD.encode.length = 2 := Dir3.encode_length _
  have hlen_od : oD.encode.length = 2 := Dir3.encode_length _
  -- Use append_right to skip the entire prefix
  rw [List.getElem?_append_right (by
    simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]; omega)]
  simp only [List.length_append, hlen_q, hlen_ww, hlen_wd, hlen_ow, hlen_id]
  rw [show k' + 4 * n' + 4 + b - (k' + 2 * n' + 2 + 2 + 2 * n') = b from by omega]
  rw [List.getElem?_eq_getElem (by rw [hlen_od]; exact hb)]

-- ════════════════════════════════════════════════════════════════════════
-- Full Hoare proof
-- ════════════════════════════════════════════════════════════════════════

private theorem reachesIn_toReaches' {m : ℕ} {tm : TM m} {t : ℕ} {c c' : Cfg m tm.Q}
    (h : tm.reachesIn t c c') : tm.reaches c c' := by
  induction h with
  | zero => exact Relation.ReflTransGen.refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs ih

set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
/-- Hoare specification for `applyTransitionTM`.
    Chains four phases: writeState, write symbols, move heads, cleanup. -/
theorem applyTransitionTM_hoare_proof {tm : TM n} (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (simCfg : Cfg n tm.Q) (hNotHalted : simCfg.state ≠ tm.qhalt) :
    let e := tm.stateEquivK hk
    let iHead := simCfg.input.read
    let wHeads := fun i => (simCfg.work i).read
    let oHead := simCfg.output.read
    let (q', wW, oW, iD, wD, oD) := tm.δ simCfg.state iHead wHeads oHead
    (applyTransitionTM (n := n) k).Hoare
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
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (simCfg.work i).head ≥ 1) ∧ simCfg.output.head ≥ 1)
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
        WorkTapesWF work) := by
  intro e iHead wHeads oHead
  set δ_result := tm.δ simCfg.state iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δ_result
  intro inp work out hpre
  obtain ⟨hstateOnTape, hsuperCells, hscratchTrans, hdescOnTape, hwf,
          hstate_head, hsim_head, hdesc_head, hinp_ns, hinp_h, hout_ns, hout_h,
          hsimWork_heads, hsimOut_head⟩ := hpre
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
  obtain ⟨steps₂, c₂, hreach₂, hst₂, hsim_h₂, hdesc₂, hstatecells₂, hinp₂, hout₂, hwf₂, hheads₂,
          hmarkers₂, hscr_ns₂, hscr_cells₂, hscr_head₂, hwritten₂, hpres₂⟩ :=
    phase1_writeSymbols c₁ simCfg wW oW hst₁ hwf₁
      hc₁_sim_correct (by rw [hsim₁]; exact hsim_head)
      hsch₁ (hwf₁.2 utmScratchTape)
      (by rw [hinp₁]; exact hinp_ns) (by rw [hinp₁]; exact hinp_h)
      (by rw [hout₁]; exact hout_ns) (by rw [hout₁]; exact hout_h)
      hheads₁
  -- ──────────────────────────────────────────────────────────────────
  -- Phase 2: move head markers
  -- ──────────────────────────────────────────────────────────────────
  -- Construct headPos and marker correctness for Phase 2
  let headPos_p2 : Fin (n + 2) → ℕ := fun ti =>
    if h0 : ti.val = 0 then simCfg.input.head
    else if hw : ti.val - 1 < n then (simCfg.work ⟨ti.val - 1, hw⟩).head
    else simCfg.output.head
  have hmarkers_p2 : ∀ (ti : Fin (n + 2)) (pos : ℕ),
      (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
      if headPos_p2 ti = pos then Γ.one else Γ.blank := by
    intro ⟨ti, hti⟩ pos
    rw [hmarkers₂ pos ti, show (c₁.work utmSimTape).cells _ = (c₀.work utmSimTape).cells _ from
      by rw [hsim₁]]
    simp only [c₀, headPos_p2]
    by_cases h0 : ti = 0
    · subst h0; simp; exact (hsuperCells.2.1 pos).1
    · by_cases hw : ti - 1 < n
      · simp [h0, hw]
        have h := (hsuperCells.2.2.1 ⟨ti - 1, hw⟩ pos).1
        dsimp only [] at h
        rwa [show ti - 1 + 1 = ti from by omega] at h
      · have : ti = n + 1 := by omega
        subst this; simp [h0, hw]; exact (hsuperCells.2.2.2 pos).1
  -- Define new head positions after movement
  let newHeadPos_p2 : Fin (n + 2) → ℕ := fun ti =>
    match (if ti.val = 0 then iD
           else if h : ti.val - 1 < n then wD ⟨ti.val - 1, h⟩ else oD) with
    | .left => headPos_p2 ti - 1
    | .right => headPos_p2 ti + 1
    | .stay => headPos_p2 ti
  have hnewHead_p2 : ∀ (ti : Fin (n + 2)),
      newHeadPos_p2 ti = match decodeDir3
        ((c₂.work utmScratchTape).cells ((c₂.work utmScratchTape).head + 2 * ti.val))
        ((c₂.work utmScratchTape).cells ((c₂.work utmScratchTape).head + 2 * ti.val + 1))
      with | .stay => headPos_p2 ti | .right => headPos_p2 ti + 1 | .left => headPos_p2 ti - 1 := by
    intro ti
    -- Chain scratch cells back to original scratch tape
    have hscr_chain : (c₂.work utmScratchTape).cells = (work utmScratchTape).cells := by
      rw [hscr_cells₂, hscc₁]
    have hscr_head_val : (c₂.work utmScratchTape).head = k + 2 * n + 3 := by
      rw [hscr_head₂, hsch₁]; omega
    rw [hscr_chain, hscr_head_val]
    -- Extract tapeStoresBools
    obtain ⟨_, hbits, _⟩ := hscratchTrans.1
    set bits := TMEncoding.encodeTransOutput k n (e q') wW oW iD wD oD
    -- The direction for ti
    set d := if ti.val = 0 then iD
             else if h : ti.val - 1 < n then wD ⟨ti.val - 1, h⟩ else oD with hd_def
    -- Show cell values match d.encode via tapeStoresBools
    have hlen := encodeTransOutput_length' k n (e q') wW oW iD wD oD
    have hidx0 : k + 2 * n + 2 + 2 * ti.val < bits.length := by rw [hlen]; omega
    have hidx1 : k + 2 * n + 2 + 2 * ti.val + 1 < bits.length := by rw [hlen]; omega
    have hcell0 : (work utmScratchTape).cells (k + 2 * n + 3 + 2 * ti.val) =
        Γ.ofBool (bits[k + 2 * n + 2 + 2 * ti.val]'hidx0) := by
      rw [show k + 2 * n + 3 + 2 * ti.val = (k + 2 * n + 2 + 2 * ti.val) + 1 from by omega]
      exact hbits _ hidx0
    have hcell1 : (work utmScratchTape).cells (k + 2 * n + 3 + 2 * ti.val + 1) =
        Γ.ofBool (bits[k + 2 * n + 2 + 2 * ti.val + 1]'hidx1) := by
      rw [show k + 2 * n + 3 + 2 * ti.val + 1 = (k + 2 * n + 2 + 2 * ti.val + 1) + 1 from by omega]
      exact hbits _ hidx1
    -- Show decodeDir3 at the scratch cells equals d
    suffices hdecode : decodeDir3
        ((work utmScratchTape).cells (k + 2 * n + 3 + 2 * ti.val))
        ((work utmScratchTape).cells (k + 2 * n + 3 + 2 * ti.val + 1)) = d by
      rw [hdecode]
      simp only [newHeadPos_p2, hd_def]
      by_cases h0 : ti.val = 0
      · simp only [h0, ite_true]; cases iD <;> rfl
      · by_cases hw : ti.val - 1 < n
        · simp only [h0, ite_false, hw, dite_true]; cases wD ⟨ti.val - 1, hw⟩ <;> rfl
        · simp only [h0, ite_false, hw, dite_false]; cases oD <;> rfl
    -- Prove hdecode by showing each cell = Γ.ofBool(d.encode[b]) then round-tripping
    rw [hcell0, hcell1]
    -- Helper: extract getElem value from getElem? = some result
    have getElem_eq : ∀ {idx : ℕ} (hidx : idx < bits.length) (val : Bool),
        bits[idx]? = some val → bits[idx]'hidx = val := by
      intro idx hidx val h; rw [List.getElem?_eq_getElem hidx] at h; exact Option.some.inj h
    -- Prove each bit by cases on ti
    by_cases h0 : ti.val = 0
    · -- ti = 0: direction is iD
      simp only [hd_def, h0, ite_true]
      have hb0 := getElem_eq (show k + 2 * n + 2 + 0 < bits.length by rw [hlen]; omega)
        _ (encodeTransOutput_idir_bits k n (e q') wW oW iD wD oD 0 (by omega))
      have hb1 := getElem_eq (show k + 2 * n + 2 + 1 < bits.length by rw [hlen]; omega)
        _ (encodeTransOutput_idir_bits k n (e q') wW oW iD wD oD 1 (by omega))
      simp only [h0, show 2 * 0 = 0 from by omega, show 0 + 1 = 1 from by omega] at hb0 hb1 ⊢
      rw [hb0, hb1, decodeDir3_ofBool_encode]
    · by_cases hw : ti.val - 1 < n
      · -- ti = j+1, j < n: direction is wD j
        simp only [hd_def, h0, ite_false, hw, dite_true]
        have hb0 := getElem_eq (show k + 2 * n + 4 + 2 * (ti.val - 1) + 0 < bits.length
          by rw [hlen]; omega)
          _ (encodeTransOutput_wdir_bits k n (e q') wW oW iD wD oD (ti.val - 1) hw 0 (by omega))
        have hb1 := getElem_eq (show k + 2 * n + 4 + 2 * (ti.val - 1) + 1 < bits.length
          by rw [hlen]; omega)
          _ (encodeTransOutput_wdir_bits k n (e q') wW oW iD wD oD (ti.val - 1) hw 1 (by omega))
        have heq0 : k + 2 * n + 2 + 2 * ti.val = k + 2 * n + 4 + 2 * (ti.val - 1) + 0 := by omega
        have heq1 : k + 2 * n + 2 + 2 * ti.val + 1 = k + 2 * n + 4 + 2 * (ti.val - 1) + 1 := by omega
        simp only [heq0, heq1] at hb0 hb1 ⊢
        rw [hb0, hb1, decodeDir3_ofBool_encode]
      · -- ti = n+1: direction is oD
        have hti : ti.val = n + 1 := by omega
        simp only [hd_def, h0, ite_false, hw, dite_false]
        have hb0 := getElem_eq (show k + 4 * n + 4 + 0 < bits.length by rw [hlen]; omega)
          _ (encodeTransOutput_odir_bits k n (e q') wW oW iD wD oD 0 (by omega))
        have hb1 := getElem_eq (show k + 4 * n + 4 + 1 < bits.length by rw [hlen]; omega)
          _ (encodeTransOutput_odir_bits k n (e q') wW oW iD wD oD 1 (by omega))
        have heq0 : k + 2 * n + 2 + 2 * ti.val = k + 4 * n + 4 + 0 := by omega
        have heq1 : k + 2 * n + 2 + 2 * ti.val + 1 = k + 4 * n + 4 + 1 := by omega
        simp only [heq0, heq1] at hb0 hb1 ⊢
        rw [hb0, hb1, decodeDir3_ofBool_encode]
  obtain ⟨steps₃, c₃, hreach₃, hst₃, hsim_h₃, hdesc₃, hstatecells₃, hinp₃, hout₃, hwf₃, hheads₃,
          hsymcells₃, hmarkers₃_raw⟩ :=
    phase2_moveHeads c₂ simCfg iD wD oD headPos_p2 newHeadPos_p2 hnewHead_p2
      hst₂ hwf₂ hsim_h₂ hheads₂ hmarkers_p2
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
  -- ── superCellsCorrect simCfg' (c₄.work utmSimTape) ──
  -- Trace sim tape cells: c₄ = c₃ (hcells₄) for utmSimTape ≠ utmScratchTape
  have hsim_cells₄₃ : (c₄.work utmSimTape).cells = (c₃.work utmSimTape).cells :=
    hcells₄ utmSimTape (by decide)
  -- Need two missing pieces:
  -- (A) Phase 2 marker positions: what are c₃'s base cells?
  -- (B) Phase 1 symbol cells: what are c₂'s +1/+2 cells?
  -- Category A hypotheses (marker positions, symbol cell values, preservation)
  have hmarkers₃ : ∀ (ti : Fin (n + 2)) pos,
      (c₃.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos ti.val) =
      if (match (if (ti : Fin (n + 2)).val = 0 then iD
                 else if h : ti.val - 1 < n then wD ⟨ti.val - 1, h⟩ else oD) with
          | .left => headPos_p2 ti - 1
          | .right => headPos_p2 ti + 1
          | .stay => headPos_p2 ti) = pos then Γ.one else Γ.blank :=
    fun ti pos => hmarkers₃_raw ti pos
  have hsymcells₂ : ∀ (wrIdx' : ℕ) (hwi' : wrIdx' < n + 1),
      let tapeIdx := wrIdx' + 1
      let h_target := if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                      else simCfg.output.head
      let w := if hw : wrIdx' < n then wW ⟨wrIdx', hw⟩ else oW
      let base := SuperCell.simTapeOffset (n + 2) h_target tapeIdx
      (c₂.work utmSimTape).cells (base + 1) = (symToSimHi w).toΓ ∧
      (c₂.work utmSimTape).cells (base + 2) = (symToSimLo w).toΓ := by
    intro wrIdx' hwi'
    obtain ⟨hhi, hlo⟩ := hwritten₂ wrIdx' hwi'
    -- Chain scratch cells: c₁.scratch.cells = c₀.scratch.cells = (work utmScratchTape).cells
    have hscr_chain : (c₁.work utmScratchTape).cells = (work utmScratchTape).cells := by
      rw [hscc₁]
    have hscr_head_c1 : (c₁.work utmScratchTape).head = k + 1 := hsch₁
    rw [hscr_chain, hscr_head_c1] at hhi hlo
    -- Extract tapeStoresBools
    obtain ⟨_, hbits, _⟩ := hscratchTrans.1
    set bits := TMEncoding.encodeTransOutput k n (e q') wW oW iD wD oD
    have hlen := encodeTransOutput_length' k n (e q') wW oW iD wD oD
    -- Show the scratch cells encode w
    set w := if hw : wrIdx' < n then wW ⟨wrIdx', hw⟩ else oW with hw_def
    have getElem_eq : ∀ {idx : ℕ} (hidx : idx < bits.length) (val : Bool),
        bits[idx]? = some val → bits[idx]'hidx = val := by
      intro idx hidx val h; rw [List.getElem?_eq_getElem hidx] at h; exact Option.some.inj h
    -- scratch cell at k+1+2*wrIdx' = Γ.ofBool(bits[k + 2*wrIdx'])
    -- scratch cell at k+1+2*wrIdx'+1 = Γ.ofBool(bits[k + 2*wrIdx' + 1])
    have hidxw0 : k + 2 * wrIdx' < bits.length := by rw [hlen]; omega
    have hidxw1 : k + 2 * wrIdx' + 1 < bits.length := by rw [hlen]; omega
    have hscell0 : (work utmScratchTape).cells (k + 1 + 2 * wrIdx') =
        Γ.ofBool (bits[k + 2 * wrIdx']'hidxw0) := by
      rw [show k + 1 + 2 * wrIdx' = (k + 2 * wrIdx') + 1 from by omega]
      exact hbits _ hidxw0
    have hscell1 : (work utmScratchTape).cells (k + 1 + 2 * wrIdx' + 1) =
        Γ.ofBool (bits[k + 2 * wrIdx' + 1]'hidxw1) := by
      rw [show k + 1 + 2 * wrIdx' + 1 = (k + 2 * wrIdx' + 1) + 1 from by omega]
      exact hbits _ hidxw1
    -- Extract encoding bits for write values
    by_cases hwn : wrIdx' < n
    · -- wrIdx' < n: write is wW
      simp only [hw_def, hwn, dite_true] at hhi hlo ⊢
      have hb0 := getElem_eq hidxw0 _ (encodeTransOutput_write_bits k n (e q') wW oW iD wD oD wrIdx' hwn 0 (by omega))
      have hb1 := getElem_eq hidxw1 _ (encodeTransOutput_write_bits k n (e q') wW oW iD wD oD wrIdx' hwn 1 (by omega))
      rw [hscell0, hb0, hscell1, hb1] at hhi hlo
      rw [decodeΓw_ofBool_encode] at hhi hlo
      exact ⟨hhi, hlo⟩
    · -- wrIdx' = n: write is oW
      have heqn : wrIdx' = n := by omega
      simp only [hwn, dite_false] at hhi hlo ⊢
      have hw_oW : w = oW := by simp only [hw_def, hwn, dite_false]
      simp only [heqn, hw_oW] at hscell0 hscell1 hhi hlo hidxw0 hidxw1 ⊢
      have hb0 := getElem_eq hidxw0 _ (encodeTransOutput_owrite_bits k n (e q') wW oW iD wD oD 0 (by omega))
      have hb1 := getElem_eq hidxw1 _ (encodeTransOutput_owrite_bits k n (e q') wW oW iD wD oD 1 (by omega))
      rw [hscell0, hb0, hscell1, hb1] at hhi hlo
      rw [decodeΓw_ofBool_encode] at hhi hlo
      exact ⟨hhi, hlo⟩
  have hsymcells₂_pres : ∀ pos tapeIdx,
      tapeIdx < n + 2 →
      (tapeIdx = 0 ∨
       ∀ wrIdx', wrIdx' < n + 1 → tapeIdx = wrIdx' + 1 →
         pos ≠ (if hw : wrIdx' < n then (simCfg.work ⟨wrIdx', hw⟩).head
                else simCfg.output.head)) →
      (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 1) ∧
      (c₂.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) =
        (c₁.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + 2) := by
    intro pos tapeIdx hlt hor
    exact hpres₂ pos tapeIdx hlt hor
  -- Now prove superCellsCorrect simCfg' (c₄.work utmSimTape)
  have hsuperCells' : superCellsCorrect
      (⟨q', simCfg.input.move iD,
       fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
       simCfg.output.writeAndMove oW.toΓ oD⟩ : Cfg n tm.Q)
      (c₄.work utmSimTape) := by
    -- Unfold superCellsCorrect into its 4 components:
    -- (1) cells 0 = start, (2) input tape, (3) work tapes, (4) output tape
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (1) cells 0 = Γ.start
      rw [hsim_cells₄₃]; exact hwf₃.1 utmSimTape
    · -- (2) Input tape (tapeIdx = 0)
      intro pos; simp only [simTapeCellCorrect]
      -- Move doesn't change cells
      have hmove_cells : (simCfg.input.move iD).cells pos = simCfg.input.cells pos := by
        cases iD <;> simp [Tape.move]
      rw [hmove_cells]
      -- Symbol cells: chain c₄→c₃→c₂→c₁ for tapeIdx=0
      have hpres := hsymcells₂_pres pos 0 (by omega) (Or.inl rfl)
      -- c₁ sim cells = initial sim cells
      have hc₁_cells : ∀ j, (c₁.work utmSimTape).cells j = (work utmSimTape).cells j :=
        fun j => congr_arg (· j) (congr_arg Tape.cells hsim₁)
      -- From original superCellsCorrect: input tape cell correct
      have horig := hsuperCells.2.1 pos
      simp only [simTapeCellCorrect] at horig
      refine ⟨?_, ?_, ?_⟩
      · -- Marker: c₄.cells(base) = c₃.cells(base) via hmarkers₃ at ti=0
        rw [hsim_cells₄₃]
        have h := hmarkers₃ ⟨0, by omega⟩ pos
        simp only [headPos_p2, show (⟨0, by omega⟩ : Fin (n + 2)).val = 0 from rfl,
          dite_true] at h
        -- Reduce the match on iD
        conv at h => rw [show (if (True : Prop) then iD else
          if h : 0 - 1 < n then wD ⟨0 - 1, h⟩ else oD) = iD from by simp]
        -- Now h has: match iD with ... = pos, needs to equal (simCfg.input.move iD).head = pos
        convert h using 2
        cases iD <;> simp [Tape.move]
      · -- Hi cell: c₄ → c₃ (hsim_cells₄₃) → c₂ (hsymcells₃) → c₁ (hpres) → work (hc₁_cells)
        rw [hsim_cells₄₃, (hsymcells₃ pos 0).1, hpres.1, hc₁_cells]; exact horig.2.1
      · -- Lo cell
        rw [hsim_cells₄₃, (hsymcells₃ pos 0).2, hpres.2, hc₁_cells]; exact horig.2.2
    · -- (3) Work tapes (tapeIdx = i.val + 1)
      intro i pos; simp only [simTapeCellCorrect]
      -- c₁ sim cells = initial sim cells
      have hc₁_cells : ∀ j, (c₁.work utmSimTape).cells j = (work utmSimTape).cells j :=
        fun j => congr_arg (· j) (congr_arg Tape.cells hsim₁)
      set tapeIdx := i.val + 1 with htapeIdx_def
      refine ⟨?_, ?_, ?_⟩
      · -- Marker: same pattern as input tape but with wD i
        rw [hsim_cells₄₃]
        have h := hmarkers₃ ⟨i.val + 1, by omega⟩ pos
        simp only [show (⟨i.val + 1, by omega⟩ : Fin (n + 2)).val = i.val + 1 from rfl,
          show ¬(i.val + 1 = 0) from by omega, headPos_p2, dite_false] at h
        simp only [show i.val + 1 - 1 = i.val from by omega, i.isLt, dite_true] at h
        convert h using 2
        simp only [Tape.writeAndMove, Tape.write]
        split
        · -- head = 0
          rename_i hh0; simp only [Tape.move]; cases wD i <;> simp [Tape.move, hh0]
        · -- head ≠ 0
          rename_i hh0; cases wD i <;> simp [Tape.move]
      · -- Hi symbol cell
        rw [hsim_cells₄₃, (hsymcells₃ pos tapeIdx).1]
        have horig := (hsuperCells.2.2.1 i pos).2.1
        simp only [simTapeCellCorrect, htapeIdx_def] at horig
        by_cases hhead : pos = (simCfg.work i).head
        · subst hhead
          have hwr := (hsymcells₂ i.val (by omega)).1
          simp only [i.isLt, dite_true, htapeIdx_def] at hwr
          rw [hwr, symToSimHi_toΓ_eq]
          have := Tape.writeAndMove_cells_head (simCfg.work i) (wW i).toΓ (wD i) (by have := hsimWork_heads i; omega)
          rw [this]
        · have hpres := hsymcells₂_pres pos tapeIdx (by omega)
            (Or.inr (fun wrIdx' hwi' htie => by
              simp only [htapeIdx_def] at htie
              have : wrIdx' = i.val := by omega
              subst this
              rw [dif_pos i.isLt, show (⟨i.val, i.isLt⟩ : Fin n) = i from Fin.ext rfl]
              exact hhead))
          rw [hpres.1, hc₁_cells, horig]; congr 1; congr 1
          exact (Tape.writeAndMove_cells_ne _ _ _ _ hhead).symm
      · -- Lo symbol cell
        rw [hsim_cells₄₃, (hsymcells₃ pos tapeIdx).2]
        have horig := (hsuperCells.2.2.1 i pos).2.2
        simp only [simTapeCellCorrect, htapeIdx_def] at horig
        by_cases hhead : pos = (simCfg.work i).head
        · subst hhead
          have hwr := (hsymcells₂ i.val (by omega)).2
          simp only [i.isLt, dite_true, htapeIdx_def] at hwr
          rw [hwr, symToSimLo_toΓ_eq]
          have := Tape.writeAndMove_cells_head (simCfg.work i) (wW i).toΓ (wD i) (by have := hsimWork_heads i; omega)
          rw [this]
        · have hpres := hsymcells₂_pres pos tapeIdx (by omega)
            (Or.inr (fun wrIdx' hwi' htie => by
              simp only [htapeIdx_def] at htie
              have : wrIdx' = i.val := by omega
              subst this
              rw [dif_pos i.isLt, show (⟨i.val, i.isLt⟩ : Fin n) = i from Fin.ext rfl]
              exact hhead))
          rw [hpres.2, hc₁_cells, horig]; congr 1; congr 1
          exact (Tape.writeAndMove_cells_ne _ _ _ _ hhead).symm
    · -- (4) Output tape (tapeIdx = n + 1)
      intro pos; simp only [simTapeCellCorrect]
      have hc₁_cells : ∀ j, (c₁.work utmSimTape).cells j = (work utmSimTape).cells j :=
        fun j => congr_arg (· j) (congr_arg Tape.cells hsim₁)
      set tapeIdx := n + 1 with htapeIdx_def
      refine ⟨?_, ?_, ?_⟩
      · -- Marker
        rw [hsim_cells₄₃]
        have h := hmarkers₃ ⟨n + 1, by omega⟩ pos
        simp only [show (⟨n + 1, by omega⟩ : Fin (n + 2)).val = n + 1 from rfl,
          show ¬(n + 1 = 0) from by omega, headPos_p2, dite_false,
          show n + 1 - 1 = n from by omega, show ¬(n < n) from by omega] at h
        convert h using 2
        simp only [Tape.writeAndMove, Tape.write]
        split
        · rename_i hh0; simp only [Tape.move]; cases oD <;> simp [Tape.move, hh0]
        · rename_i hh0; cases oD <;> simp [Tape.move]
      · -- Hi symbol cell
        rw [hsim_cells₄₃, (hsymcells₃ pos tapeIdx).1]
        have horig := (hsuperCells.2.2.2 pos).2.1
        simp only [simTapeCellCorrect, htapeIdx_def] at horig
        by_cases hhead : pos = simCfg.output.head
        · subst hhead
          have hwr := (hsymcells₂ n (by omega)).1
          simp only [show ¬(n < n) from by omega, dite_false, htapeIdx_def] at hwr
          rw [hwr, symToSimHi_toΓ_eq]
          have := Tape.writeAndMove_cells_head simCfg.output oW.toΓ oD (by omega)
          rw [this]
        · have hpres := hsymcells₂_pres pos tapeIdx (by omega)
            (Or.inr (fun wrIdx' hwi' htie => by
              simp only [htapeIdx_def] at htie
              have heq : wrIdx' = n := by omega
              rw [heq, dif_neg (show ¬(n < n) from by omega)]
              exact hhead))
          rw [hpres.1, hc₁_cells, horig]; congr 1; congr 1
          exact (Tape.writeAndMove_cells_ne _ _ _ _ hhead).symm
      · -- Lo symbol cell
        rw [hsim_cells₄₃, (hsymcells₃ pos tapeIdx).2]
        have horig := (hsuperCells.2.2.2 pos).2.2
        simp only [simTapeCellCorrect, htapeIdx_def] at horig
        by_cases hhead : pos = simCfg.output.head
        · subst hhead
          have hwr := (hsymcells₂ n (by omega)).2
          simp only [show ¬(n < n) from by omega, dite_false, htapeIdx_def] at hwr
          rw [hwr, symToSimLo_toΓ_eq]
          have := Tape.writeAndMove_cells_head simCfg.output oW.toΓ oD (by omega)
          rw [this]
        · have hpres := hsymcells₂_pres pos tapeIdx (by omega)
            (Or.inr (fun wrIdx' hwi' htie => by
              simp only [htapeIdx_def] at htie
              have heq : wrIdx' = n := by omega
              rw [heq, dif_neg (show ¬(n < n) from by omega)]
              exact hhead))
          rw [hpres.2, hc₁_cells, horig]; congr 1; congr 1
          exact (Tape.writeAndMove_cells_ne _ _ _ _ hhead).symm
  refine ⟨c₄, reachesIn_toReaches' htotal, hhalted₄, ?_, hsuperCells', ?_,
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
