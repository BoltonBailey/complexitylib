import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.UTM.InitInternal.Rewind

/-!
# Init proof internals: setupSimTM

Step-by-step simulation lemmas and HoareTime proof for `setupSimTM`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem init_readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem init_tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem init_tape_read_ne_start (t : Tape) (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hns _ hh

-- ════════════════════════════════════════════════════════════════════════
-- simTapeCellCorrect lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem simTapeCellCorrect_pos0
    (simTape : Tape) (tapeIdx : ℕ) (htape : tapeIdx < n + 2)
    (hcells : ∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → simTape.cells j = Γ.one) :
    simTapeCellCorrect (n + 2) tapeIdx 0 0 Γ.start simTape := by
  simp only [simTapeCellCorrect, SuperCell.simTapeOffset, SuperCell.width, ↓reduceIte,
             SuperCell.symToCellPair]
  refine ⟨?_, ?_, ?_⟩ <;> (apply hcells <;> omega)

private theorem simTapeCellCorrect_blank_cells
    (simTape : Tape) (numTapes tapeIdx pos : ℕ) (hpos : pos > 0)
    (hbase : ∀ off, off < 3 →
      simTape.cells (SuperCell.simTapeOffset numTapes pos tapeIdx + off) = Γ.blank) :
    simTapeCellCorrect numTapes tapeIdx pos 0 Γ.blank simTape := by
  simp only [simTapeCellCorrect, SuperCell.symToCellPair]
  have hne : (0 : ℕ) ≠ pos := by omega
  simp only [hne, ↓reduceIte]
  exact ⟨hbase 0 (by omega), hbase 1 (by omega), hbase 2 (by omega)⟩

private theorem simTapeCellCorrect_input_written
    (simTape : Tape) (pos : ℕ) (b : Bool) (hpos : pos > 0)
    (hc0 : simTape.cells (SuperCell.simTapeOffset (n + 2) pos 0) = Γ.blank)
    (hc1 : simTape.cells (SuperCell.simTapeOffset (n + 2) pos 0 + 1) = Γ.zero)
    (hc2 : simTape.cells (SuperCell.simTapeOffset (n + 2) pos 0 + 2) = Γ.ofBool b) :
    simTapeCellCorrect (n + 2) 0 pos 0 (Γ.ofBool b) simTape := by
  simp only [simTapeCellCorrect, SuperCell.symToCellPair]
  have hne : (0 : ℕ) ≠ pos := by omega
  simp only [hne, ↓reduceIte]
  cases b <;> simp only [Γ.ofBool, SuperCell.symToCellPair] at * <;> exact ⟨hc0, hc1, hc2⟩

-- ════════════════════════════════════════════════════════════════════════
-- superCellsCorrect from cell values
-- ════════════════════════════════════════════════════════════════════════

private theorem superCellsCorrect_from_cells
    (tm : TM n) (x : List Bool) (simTape : Tape)
    (h0 : simTape.cells 0 = Γ.start)
    (hpos0 : ∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → simTape.cells j = Γ.one)
    (hinput : ∀ (p : ℕ) (hp : p ≥ 1) (hp2 : p ≤ x.length),
      simTape.cells (SuperCell.simTapeOffset (n + 2) p 0) = Γ.blank ∧
      simTape.cells (SuperCell.simTapeOffset (n + 2) p 0 + 1) = Γ.zero ∧
      simTape.cells (SuperCell.simTapeOffset (n + 2) p 0 + 2) =
        Γ.ofBool (x.get ⟨p - 1, by omega⟩))
    (hblank : ∀ (numTapes tapeIdx pos : ℕ),
      pos > 0 → tapeIdx < numTapes → numTapes = n + 2 →
      (tapeIdx > 0 ∨ pos > x.length) →
      ∀ off, off < 3 →
        simTape.cells (SuperCell.simTapeOffset numTapes pos tapeIdx + off) = Γ.blank) :
    superCellsCorrect (tm.initCfg x) simTape := by
  refine ⟨h0, ?_, ?_, ?_⟩
  · intro pos
    by_cases hpos0' : pos = 0
    · subst hpos0'
      simp only [TM.initCfg, Cfg.init, initTape]
      exact simTapeCellCorrect_pos0 simTape 0 (by omega) hpos0
    · have hpge : pos ≥ 1 := by omega
      simp only [TM.initCfg, Cfg.init, initTape]
      rw [if_neg hpos0']
      by_cases hle : pos ≤ x.length
      · have hlt : pos - 1 < x.length := by omega
        have hmapped : (List.map Γ.ofBool x)[pos - 1]? =
            some (Γ.ofBool (x.get ⟨pos - 1, hlt⟩)) := by
          rw [List.getElem?_map]
          simp [hlt]
        simp only [hmapped, Option.getD]
        obtain ⟨hc0, hc1, hc2⟩ := hinput pos hpge hle
        exact simTapeCellCorrect_input_written simTape pos
          (x.get ⟨pos - 1, hlt⟩) (by omega) hc0 hc1 hc2
      · have : (List.map Γ.ofBool x)[pos - 1]? = none := by
          rw [List.getElem?_eq_none]; simp; omega
        simp only [this, Option.getD]
        exact simTapeCellCorrect_blank_cells simTape (n + 2) 0 pos (by omega)
          (fun off hoff => hblank (n + 2) 0 pos (by omega) (by omega) rfl
            (Or.inr (by omega)) off hoff)
  · intro i pos
    by_cases hpos0' : pos = 0
    · subst hpos0'
      simp only [TM.initCfg, Cfg.init, initTape]
      exact simTapeCellCorrect_pos0 simTape (i.val + 1) (by omega) hpos0
    · simp only [TM.initCfg, Cfg.init, initTape]
      rw [if_neg hpos0']
      have : ([] : List Γ)[pos - 1]? = (none : Option Γ) := by
        rw [List.getElem?_eq_none]; simp
      simp only [this, Option.getD]
      exact simTapeCellCorrect_blank_cells simTape (n + 2) (i.val + 1) pos (by omega)
        (fun off hoff => hblank (n + 2) (i.val + 1) pos (by omega) (by omega) rfl
          (Or.inl (by omega)) off hoff)
  · intro pos
    by_cases hpos0' : pos = 0
    · subst hpos0'
      simp only [TM.initCfg, Cfg.init, initTape]
      exact simTapeCellCorrect_pos0 simTape (n + 1) (by omega) hpos0
    · simp only [TM.initCfg, Cfg.init, initTape]
      rw [if_neg hpos0']
      have : ([] : List Γ)[pos - 1]? = (none : Option Γ) := by
        rw [List.getElem?_eq_none]; simp
      simp only [this, Option.getD]
      exact simTapeCellCorrect_blank_cells simTape (n + 2) (n + 1) pos (by omega)
        (fun off hoff => hblank (n + 2) (n + 1) pos (by omega) (by omega) rfl
          (Or.inl (by omega)) off hoff)

-- ════════════════════════════════════════════════════════════════════════
-- Phase simulation stubs (sorry'd)
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 1 loop: write 3 ones per scratch-one.
    Induction on remaining ones (n - done). -/
private theorem phase1_loop :
    ∀ (done : ℕ) (c : Cfg 4 setupSimTM.Q),
    done ≤ n →
    c.state = .pos0Write1 →
    (c.work utmSimTape).head = 1 + 3 * done →
    (∀ j, j ≥ 1 → j ≤ 3 * done → (c.work utmSimTape).cells j = Γ.one) →
    (∀ j, j > 3 * done → (c.work utmSimTape).cells j = Γ.blank) →
    (c.work utmSimTape).cells 0 = Γ.start →
    (c.work utmScratchTape).head = 1 + done →
    (∀ j, j > done → j ≤ n → (c.work utmScratchTape).cells j = Γ.one) →
    (c.work utmScratchTape).cells (n + 1) = Γ.blank →
    (c.work utmScratchTape).cells 0 = Γ.start →
    (∀ j, j ≥ 1 → j ≤ n → (c.work utmScratchTape).cells j ≠ Γ.start) →
    WorkTapesWF c.work →
    c.input.head ≥ 1 →
    (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    c.output.head ≥ 1 →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    c.work utmDescTape = c.work utmDescTape →
    c.work utmStateTape = c.work utmStateTape →
    ∃ c',
      setupSimTM.reachesIn (3 * (n - done) + 1) c c' ∧
      c'.state = .pos0Extra1 ∧
      (c'.work utmSimTape).head = 1 + 3 * n ∧
      (∀ j, j ≥ 1 → j ≤ 3 * n → (c'.work utmSimTape).cells j = Γ.one) ∧
      (∀ j, j > 3 * n → (c'.work utmSimTape).cells j = Γ.blank) ∧
      (c'.work utmSimTape).cells 0 = Γ.start ∧
      c'.work utmDescTape = c.work utmDescTape ∧
      c'.work utmStateTape = c.work utmStateTape ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work ∧
      (c'.work utmScratchTape).head = n + 1 := by
  sorry

/-- Phase 1+2: write 3*(n+2) ones for position 0 and advance input.

    Phase 1 loop (3n+1 steps) + Phase 1 extras (6 steps) +
    Phase 2 advanceInput (1 step) = 3n+8 steps. -/
private theorem setupSim_phase12
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (hsim0 : (work utmSimTape).cells 0 = Γ.start)
    (hsim_blank : ∀ j, j ≥ 1 → (work utmSimTape).cells j = Γ.blank)
    (hsim_head : (work utmSimTape).head = 1)
    (hsc0 : (work utmScratchTape).cells 0 = Γ.start)
    (hsc_ones : ∀ j, j ≥ 1 → j ≤ n → (work utmScratchTape).cells j = Γ.one)
    (hsc_sentinel : (work utmScratchTape).cells (n + 1) = Γ.blank)
    (hsc_head : (work utmScratchTape).head = 1)
    (hinp_h : inp.head ≥ 1) (hinp_ns : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start)
    (hout_h : out.head ≥ 1) (hout_ns : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start)
    (hwf : WorkTapesWF work) :
    ∃ c',
      setupSimTM.reachesIn (3 * n + 8) ⟨.pos0Write1, inp, work, out⟩ c' ∧
      c'.state = .checkInput ∧
      (c'.work utmSimTape).cells 0 = Γ.start ∧
      (c'.work utmSimTape).head = 1 + 3 * (n + 2) ∧
      (∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → (c'.work utmSimTape).cells j = Γ.one) ∧
      (∀ j, j > 3 * (n + 2) → (c'.work utmSimTape).cells j = Γ.blank) ∧
      c'.work utmDescTape = work utmDescTape ∧
      c'.work utmStateTape = work utmStateTape ∧
      c'.input.head = inp.head + 1 ∧
      c'.input.cells = inp.cells ∧
      c'.output = out ∧
      WorkTapesWF c'.work ∧
      (∀ j, j ≥ 1 → j ≤ n → (c'.work utmScratchTape).cells j = Γ.one) ∧
      (c'.work utmScratchTape).cells (n + 1) = Γ.blank ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (c'.work utmScratchTape).head = 1 ∧
      c'.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧
      c'.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) := by
  sorry

/-- Phase 3: copy x with stride, then halt on blank.

    Each x bit takes 4n+9 steps. Final blank check takes 1 step.
    Total: x.length * (4n+9) + 1 steps. -/
private theorem setupSim_phase3
    (x : List Bool)
    (c : Cfg 4 setupSimTM.Q)
    (hstate : c.state = .checkInput)
    -- sim tape after phase 1+2
    (hsim0 : (c.work utmSimTape).cells 0 = Γ.start)
    (hsim_head : (c.work utmSimTape).head = 1 + 3 * (n + 2))
    (hpos0_ones : ∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → (c.work utmSimTape).cells j = Γ.one)
    (hsim_rest : ∀ j, j > 3 * (n + 2) → (c.work utmSimTape).cells j = Γ.blank)
    -- scratch tape
    (hsc_ones : ∀ j, j ≥ 1 → j ≤ n → (c.work utmScratchTape).cells j = Γ.one)
    (hsc_blank : (c.work utmScratchTape).cells (n + 1) = Γ.blank)
    (hsc0 : (c.work utmScratchTape).cells 0 = Γ.start)
    (hsc_head : (c.work utmScratchTape).head = 1)
    -- input tape
    (hinp_h : c.input.head ≥ 1)
    (hinp_ns : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hinp_x : ∀ (i : ℕ) (hi : i < x.length),
      c.input.cells (c.input.head + i) = Γ.ofBool (x.get ⟨i, hi⟩))
    (hinp_end : c.input.cells (c.input.head + x.length) = Γ.blank)
    -- output + wf
    (hout_h : c.output.head ≥ 1)
    (hout_ns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hwf : WorkTapesWF c.work) :
    ∃ c',
      setupSimTM.reachesIn (x.length * (4 * n + 9) + 1) c c' ∧
      setupSimTM.halted c' ∧
      (c'.work utmSimTape).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → (c'.work utmSimTape).cells j = Γ.one) ∧
      (∀ (p : ℕ) (hp : p ≥ 1) (hp2 : p ≤ x.length),
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0) = Γ.blank ∧
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 1) = Γ.zero ∧
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 2) =
          Γ.ofBool (x.get ⟨p - 1, by omega⟩)) ∧
      (∀ (numTapes tapeIdx pos : ℕ),
        pos > 0 → tapeIdx < numTapes → numTapes = n + 2 →
        (tapeIdx > 0 ∨ pos > x.length) →
        ∀ off, off < 3 →
          (c'.work utmSimTape).cells
            (SuperCell.simTapeOffset numTapes pos tapeIdx + off) = Γ.blank) ∧
      c'.work utmDescTape = c.work utmDescTape ∧
      c'.work utmStateTape = c.work utmStateTape ∧
      WorkTapesWF c'.work ∧
      (∀ i, (c'.work i).head ≥ 1) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- Full execution (proved modulo phases)
-- ════════════════════════════════════════════════════════════════════════

private def setupSimBound (n xLen : ℕ) : ℕ := 3 * n + 9 + xLen * (4 * n + 9)

private theorem setupSim_full_execution
    (x : List Bool)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    -- sim tape
    (hsim0 : (work utmSimTape).cells 0 = Γ.start)
    (hsim_blank : ∀ j, j ≥ 1 → (work utmSimTape).cells j = Γ.blank)
    (hsim_head : (work utmSimTape).head = 1)
    -- scratch tape (n ones at cells 1..n)
    (hsc_bools : tapeStoresBools (List.replicate n true) (work utmScratchTape))
    (hsc_head : (work utmScratchTape).head = 1)
    -- input tape
    (hinp_h : inp.head ≥ 1)
    (hinp_ns : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start)
    (hinp_read_blank : inp.cells inp.head = Γ.blank)
    (hinp_x : ∀ (i : ℕ) (hi : i < x.length),
      inp.cells (inp.head + 1 + i) = Γ.ofBool (x.get ⟨i, hi⟩))
    (hinp_end : inp.cells (inp.head + 1 + x.length) = Γ.blank)
    -- output tape
    (hout_h : out.head ≥ 1)
    (hout_ns : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start)
    -- work tapes WF
    (hwf : WorkTapesWF work) :
    ∃ c',
      setupSimTM.reachesIn (setupSimBound n x.length)
        ⟨.pos0Write1, inp, work, out⟩ c' ∧
      setupSimTM.halted c' ∧
      -- Position 0 ones
      (c'.work utmSimTape).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → (c'.work utmSimTape).cells j = Γ.one) ∧
      -- Input positions correctly written
      (∀ (p : ℕ) (hp : p ≥ 1) (hp2 : p ≤ x.length),
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0) = Γ.blank ∧
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 1) = Γ.zero ∧
        (c'.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 2) =
          Γ.ofBool (x.get ⟨p - 1, by omega⟩)) ∧
      -- Unwritten cells blank
      (∀ (numTapes tapeIdx pos : ℕ),
        pos > 0 → tapeIdx < numTapes → numTapes = n + 2 →
        (tapeIdx > 0 ∨ pos > x.length) →
        ∀ off, off < 3 →
          (c'.work utmSimTape).cells
            (SuperCell.simTapeOffset numTapes pos tapeIdx + off) = Γ.blank) ∧
      -- Preserved tapes
      c'.work utmDescTape = work utmDescTape ∧
      c'.work utmStateTape = work utmStateTape ∧
      WorkTapesWF c'.work ∧
      (∀ i, (c'.work i).head ≥ 1) := by
  -- Extract scratch tape properties from tapeStoresBools
  have hsc0 : (work utmScratchTape).cells 0 = Γ.start := hsc_bools.1
  have hsc_ones : ∀ j, j ≥ 1 → j ≤ n →
      (work utmScratchTape).cells j = Γ.one := by
    intro j hj1 hjn
    have hj' : j - 1 < (List.replicate n true).length := by simp; omega
    have := hsc_bools.2.1 (j - 1) hj'
    simp [List.replicate, List.getElem_replicate, Γ.ofBool] at this
    rwa [show j - 1 + 1 = j from by omega] at this
  have hsc_sentinel : (work utmScratchTape).cells (n + 1) = Γ.blank := by
    have := hsc_bools.2.2; simp at this; exact this
  -- Phase 1+2: write position-0 ones and advance input
  obtain ⟨c1, hreach1, hst1, hsim0_1, hsim_head1, hones1, hblank1,
          hdesc1, hstate1, hinp_head1, hinp_cells1, hout1, hwf1,
          hsc_ones1, hsc_blank1, hsc0_1, hsc_head1,
          hinp_h1, hinp_ns1, hout_h1, hout_ns1⟩ :=
    setupSim_phase12 inp work out hsim0 hsim_blank hsim_head
      hsc0 hsc_ones hsc_sentinel hsc_head hinp_h hinp_ns hout_h hout_ns hwf
  -- Phase 3: copy x with stride and halt
  have hinp_x1 : ∀ (i : ℕ) (hi : i < x.length),
      c1.input.cells (c1.input.head + i) = Γ.ofBool (x.get ⟨i, hi⟩) := by
    intro i hi
    rw [hinp_cells1, hinp_head1]
    exact hinp_x i hi
  have hinp_end1 : c1.input.cells (c1.input.head + x.length) = Γ.blank := by
    rw [hinp_cells1, hinp_head1]
    exact hinp_end
  obtain ⟨c2, hreach2, hhalt2, hsim0_2, hones2, hinput2, hblank2,
          hdesc2, hstate2, hwf2, hheads2⟩ :=
    setupSim_phase3 x c1 hst1 hsim0_1 hsim_head1 hones1 hblank1
      hsc_ones1 hsc_blank1 hsc0_1 hsc_head1
      hinp_h1 hinp_ns1 hinp_x1 hinp_end1 hout_h1 hout_ns1 hwf1
  -- Compose phases
  refine ⟨c2, ?_, hhalt2, hsim0_2, hones2, hinput2, hblank2,
          ?_, ?_, hwf2, hheads2⟩
  -- reachesIn composition
  · have : setupSimBound n x.length = (3 * n + 8) + (x.length * (4 * n + 9) + 1) := by
      simp [setupSimBound]; omega
    rw [this]
    exact reachesIn_trans setupSimTM hreach1 hreach2
  -- desc tape preserved
  · rw [hdesc2]; exact hdesc1
  -- state tape preserved
  · rw [hstate2]; exact hstate1

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for setupSimTM.
    Precondition: sim tape blank, scratch has n ones at head 1, input at separator.
    Postcondition: sim tape has super-cells for initCfg x. -/
theorem setupSimTM_hoareTime (tm : TM n) (k : ℕ)
    (e : tm.Q ≃ Fin k) (x : List Bool)
    (_hk : k = @Fintype.card tm.Q tm.finQ) :
    setupSimTM.HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (e tm.qstart) (work utmStateTape) ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
        (work utmScratchTape).head = 1)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (e tm.qstart) (work utmStateTape) ∧
        superCellsCorrect (tm.initCfg x) (work utmSimTape) ∧
        (work (0 : Fin 4)).head ≤ 3 * k + n + 4 ∧
        (work (1 : Fin 4)).head ≤ k + 1 ∧
        (work (2 : Fin 4)).head ≤ (x.length + 1) * 3 * (n + 2) + 1 ∧
        (work (3 : Fin 4)).head ≤ n + 1)
      (3 * n + 9 + x.length * (4 * n + 9)) := by
  sorry

end TM
