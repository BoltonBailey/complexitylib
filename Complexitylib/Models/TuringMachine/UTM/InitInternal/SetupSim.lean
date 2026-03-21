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

private theorem idle_tape_preserved {t : Tape} (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  have hread : t.read ≠ Γ.start := init_tape_read_ne_start _ hh hns
  simp only [Tape.writeAndMove, idleDir, hread, ↓reduceIte, Tape.move,
    Tape.write, show t.head ≠ 0 from by omega]
  congr 1
  rw [init_readBackWrite_toΓ_eq hread]; exact Function.update_eq_self _ _

private theorem idle_input_preserved {t : Tape} (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  have hread : t.read ≠ Γ.start := init_tape_read_ne_start _ hh hns
  simp [idleDir, hread, Tape.move]

private theorem writeAndMove_right_head {t : Tape} {w : Γw} :
    (t.writeAndMove w Dir3.right).head = t.head + 1 := by
  simp [Tape.writeAndMove, Tape.write]; split <;> simp [Tape.move]

private theorem writeAndMove_cells_at_head {t : Tape} {w : Γw} {d : Dir3}
    (hh : t.head ≠ 0) :
    (t.writeAndMove w d).cells t.head = w.toΓ := by
  simp only [Tape.writeAndMove, init_tape_move_cells, Tape.write, hh, ↓reduceIte,
    Function.update_self]

private theorem writeAndMove_cells_ne {t : Tape} {w : Γw} {d : Dir3} {j : ℕ}
    (hj : j ≠ t.head) :
    (t.writeAndMove w d).cells j = t.cells j := by
  simp only [Tape.writeAndMove, init_tape_move_cells, Tape.write]
  split
  · rfl
  · simp only [Function.update]; split
    · next h => exact absurd h hj
    · rfl

private theorem readBackWrite_cells {t : Tape} {d : Dir3}
    (hh : t.head ≥ 1) (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read) d).cells = t.cells := by
  have hread : t.read ≠ Γ.start := init_tape_read_ne_start _ hh hns
  ext j
  simp only [Tape.writeAndMove, init_tape_move_cells, Tape.write,
    show t.head ≠ 0 from by omega, ↓reduceIte]
  simp only [Function.update]
  split
  · next h => subst h; exact init_readBackWrite_toΓ_eq hread
  · rfl

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
    (c.work utmDescTape).head ≥ 1 →
    (c.work utmStateTape).head ≥ 1 →
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
      (c'.work utmScratchTape).head = n + 1 ∧
      (∀ j, j ≥ 1 → j ≤ n → (c'.work utmScratchTape).cells j = Γ.one) ∧
      (c'.work utmScratchTape).cells (n + 1) = Γ.blank ∧
      (c'.work utmScratchTape).cells 0 = Γ.start := by
  intro done
  induction h : n - done generalizing done with
  | zero =>
    intro c hdn hstate hsim_h hsim_ones hsim_blank hsim0
      hsc_h hsc_ones hsc_sentinel hsc0 hsc_ns hwf hinp_h hinp_ns hout_h hout_ns hdesc_h hst_h
    have hdn : done = n := by omega
    have hsc_read : (fun i => (c.work i).read) (3 : Fin 4) ≠ Γ.one := by
      show (c.work utmScratchTape).read ≠ Γ.one
      simp only [Tape.read, hsc_h, hdn, show 1 + n = n + 1 from by omega, hsc_sentinel]; decide
    have htape_id : ∀ (t : Tape), t.head ≥ 1 →
        (∀ j, j ≥ 1 → t.cells j ≠ Γ.start) →
        t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
      intro t hh hns
      have hns_read : t.read ≠ Γ.start := by simp only [Tape.read]; exact hns _ hh
      simp only [Tape.writeAndMove, idleDir, hns_read, ↓reduceIte, Tape.move,
        init_readBackWrite_toΓ_eq hns_read, Tape.write]
      split
      · omega
      · simp only [Tape.read, Function.update_eq_self]
    have hwk_heads : ∀ i : Fin 4, (c.work i).head ≥ 1 := fun
      | ⟨0, _⟩ => hdesc_h | ⟨1, _⟩ => hst_h
      | ⟨2, _⟩ => by show (c.work utmSimTape).head ≥ 1; omega
      | ⟨3, _⟩ => by show (c.work utmScratchTape).head ≥ 1; omega
    have hwk_id : ∀ i : Fin 4,
        (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ (idleDir (c.work i).read) = c.work i :=
      fun i => htape_id _ (hwk_heads i) (fun j hj => hwf.2 i j hj)
    have hinp_ns_read : c.input.read ≠ Γ.start := by
      simp only [Tape.read]; exact hinp_ns _ hinp_h
    have hinp_id : c.input.move (idleDir c.input.read) = c.input := by
      simp only [idleDir, hinp_ns_read, ↓reduceIte, Tape.move]
    have hout_id : c.output.writeAndMove (readBackWrite c.output.read).toΓ (idleDir c.output.read) = c.output :=
      htape_id _ hout_h (fun j hj => hout_ns j hj)
    have hstep : setupSimTM.step c = some
        { state := SetupSimPhase.pos0Extra1
          input := c.input.move (idleDir c.input.read)
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ (idleDir c.output.read) } := by
      unfold TM.step
      simp only [hstate, show SetupSimPhase.pos0Write1 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
        setupSimTM, hsc_read, setupIdle]
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hinp_id, hout_id, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only []; rw [hwk_id utmSimTape, hsim_h, hdn]
    · intro j hj1 hjn; dsimp only []; rw [hwk_id utmSimTape]; exact hsim_ones j hj1 (by omega)
    · intro j hj; dsimp only []; rw [hwk_id utmSimTape]; exact hsim_blank j (by omega)
    · dsimp only []; rw [hwk_id utmSimTape]; exact hsim0
    · exact hwk_id utmDescTape
    · exact hwk_id utmStateTape
    · exact ⟨fun i => by dsimp only []; rw [hwk_id i]; exact hwf.1 i,
             fun i j hj => by dsimp only []; rw [hwk_id i]; exact hwf.2 i j hj⟩
    · dsimp only []; rw [hwk_id utmScratchTape, hsc_h, hdn]; omega
    · intro j hj1 hjn; dsimp only []; rw [hwk_id utmScratchTape]; exact hsc_ones j hj1 hjn
    · dsimp only []; rw [hwk_id utmScratchTape]; exact hsc_sentinel
    · dsimp only []; rw [hwk_id utmScratchTape]; exact hsc0
  | succ m ih =>
    intro c hdn hstate hsim_h hsim_ones hsim_blank hsim0
      hsc_h hsc_ones hsc_sentinel hsc0 hsc_ns hwf hinp_h hinp_ns hout_h hout_ns hdesc_h hst_h
    have hlt : done < n := by omega
    have hsc_read_one : (c.work utmScratchTape).read = Γ.one := by
      simp only [Tape.read, hsc_h]; exact hsc_ones (1 + done) (by omega) (by omega)
    have hsc_is_one : (fun i => (c.work i).read) (3 : Fin 4) = Γ.one := hsc_read_one
    have hwk_heads : ∀ i : Fin 4, (c.work i).head ≥ 1 := fun
      | ⟨0, _⟩ => hdesc_h | ⟨1, _⟩ => hst_h
      | ⟨2, _⟩ => by show (c.work utmSimTape).head ≥ 1; omega
      | ⟨3, _⟩ => by show (c.work utmScratchTape).head ≥ 1; omega
    have htape_id : ∀ (t : Tape), t.head ≥ 1 →
        (∀ j, j ≥ 1 → t.cells j ≠ Γ.start) →
        t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
      intro t hh hns
      have hns_read : t.read ≠ Γ.start := by simp only [Tape.read]; exact hns _ hh
      simp only [Tape.writeAndMove, idleDir, hns_read, ↓reduceIte, Tape.move,
        init_readBackWrite_toΓ_eq hns_read, Tape.write]
      split
      · omega
      · simp only [Tape.read, Function.update_eq_self]
    have hwk_id : ∀ i : Fin 4,
        (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ (idleDir (c.work i).read) = c.work i :=
      fun i => htape_id _ (hwk_heads i) (fun j hj => hwf.2 i j hj)
    have hinp_ns_read : c.input.read ≠ Γ.start := by
      simp only [Tape.read]; exact hinp_ns _ hinp_h
    have hout_ns_read : c.output.read ≠ Γ.start := by
      simp only [Tape.read]; exact hout_ns _ hout_h
    -- Step 1: pos0Write1(scratch=one) → pos0Write2 via simWriteRight
    have hstep1 : setupSimTM.step c = some
        { state := SetupSimPhase.pos0Write2
          input := c.input.move (idleDir c.input.read)
          work := fun i => (c.work i).writeAndMove
            (if i.val = 2 then Γw.one else readBackWrite ((c.work i).read)).toΓ
            (if i.val = 2 then Dir3.right else idleDir ((c.work i).read))
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ (idleDir c.output.read) } := by
      unfold TM.step
      simp only [hstate, show SetupSimPhase.pos0Write1 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
        setupSimTM, hsc_is_one, simWriteRight]
    -- Define c₃: config after 3 steps
    let sim₃ : Tape := {
      head := 1 + 3 * done + 3
      cells := fun j =>
        if j = 1 + 3 * done then Γ.one
        else if j = 1 + 3 * done + 1 then Γ.one
        else if j = 1 + 3 * done + 2 then Γ.one
        else (c.work utmSimTape).cells j }
    let sc₃ : Tape := {
      head := (c.work utmScratchTape).head + 1
      cells := (c.work utmScratchTape).cells }
    let c₃ : Cfg 4 setupSimTM.Q := {
      state := .pos0Write1
      input := c.input
      work := fun i =>
        if i = utmSimTape then sim₃
        else if i = utmScratchTape then sc₃
        else c.work i
      output := c.output }
    -- 3-step reachesIn (sorry for now, will be filled by agent)
    have hreach3 : setupSimTM.reachesIn 3 c c₃ := by
      -- ── Idle-preservation helpers ──
      have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
        idle_input_preserved hinp_h hinp_ns
      have hout_idle : c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) = c.output := by
        rw [show (readBackWrite c.output.read).toΓ = readBackWrite c.output.read from rfl]
        exact idle_tape_preserved hout_h hout_ns
      -- Helper to show non-sim work tapes are preserved by simWriteRight-style steps
      have hwk_idle_step : ∀ (wk : Fin 4 → Tape),
          (∀ i : Fin 4, i ≠ utmSimTape → wk i = c.work i) →
          ∀ i : Fin 4, i ≠ utmSimTape →
          (wk i).writeAndMove
            (if i.val = 2 then Γw.one else readBackWrite ((wk i).read)).toΓ
            (if i.val = 2 then Dir3.right else idleDir ((wk i).read)) = c.work i := by
        intro wk hwk i hi
        have hival : ¬(i.val = 2) := fun heq => hi (Fin.ext heq)
        simp only [hival, ↓reduceIte,
          show (readBackWrite (wk i).read).toΓ = readBackWrite (wk i).read from rfl]
        rw [hwk i hi]; exact hwk_id i
      -- ── Sim tape after step 1 ──
      set sim₁ := (c.work utmSimTape).writeAndMove Γw.one.toΓ Dir3.right with sim₁_def
      have hsim1_head : sim₁.head = 1 + 3 * done + 1 := by
        rw [sim₁_def, writeAndMove_right_head, hsim_h]
      -- ── Step 2: pos0Write2 → pos0Write3 via simWriteRight ──
      -- Step 2 operates on the raw config from hstep1; we prove the step and
      -- simultaneously simplify to get our nice intermediate form
      set sim₂ := sim₁.writeAndMove Γw.one.toΓ Dir3.right with sim₂_def
      have hsim2_head : sim₂.head = 1 + 3 * done + 2 := by
        rw [sim₂_def, writeAndMove_right_head, hsim1_head]
      -- Step 2: unfold on the raw config from hstep1
      have hstep2_raw : setupSimTM.step
          { state := SetupSimPhase.pos0Write2
            input := c.input.move (idleDir c.input.read)
            work := fun i => (c.work i).writeAndMove
              (if i.val = 2 then Γw.one else readBackWrite ((c.work i).read)).toΓ
              (if i.val = 2 then Dir3.right else idleDir ((c.work i).read))
            output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
              (idleDir c.output.read) } = some
          { state := SetupSimPhase.pos0Write3
            input := c.input
            work := fun i => if i = utmSimTape then sim₂ else c.work i
            output := c.output } := by
        unfold TM.step
        simp only [show SetupSimPhase.pos0Write2 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
          setupSimTM, simWriteRight]
        congr 1
        refine Cfg.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_, ?_⟩
        · -- input: double-idle = idle
          rw [hinp_idle]; exact hinp_idle
        · -- work tapes
          funext i
          by_cases hi : i = utmSimTape
          · subst hi
            simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte, sim₂_def, sim₁_def]
          · have hival : ¬(i.val = 2) := fun heq => hi (Fin.ext heq)
            simp only [hi, ↓reduceIte, hival,
              show (readBackWrite ((c.work i).writeAndMove
                (readBackWrite (c.work i).read).toΓ
                (idleDir (c.work i).read)).read).toΓ =
                readBackWrite ((c.work i).writeAndMove
                  (readBackWrite (c.work i).read).toΓ
                  (idleDir (c.work i).read)).read from rfl]
            rw [hwk_id i]; exact hwk_id i
        · -- output: double-idle
          rw [hout_idle]; exact hout_idle
      -- ── Step 3: pos0Write3 → pos0Write1 (custom transition) ──
      -- We prove step 3 from the simplified c₂-like config
      have hstep3_raw : setupSimTM.step
          { state := .pos0Write3, input := c.input,
            work := fun i => if i = utmSimTape then sim₂ else c.work i,
            output := c.output } = some c₃ := by
        unfold TM.step
        simp only [show SetupSimPhase.pos0Write3 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
          setupSimTM]
        congr 1
        refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
        funext i
        -- Step 3 transition: sim(write one, right), scratch(readBackWrite, right), rest(idle)
        by_cases hi2 : i = utmSimTape
        · -- Sim tape: write one, move right → produces sim₃
          subst hi2
          simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte,
            show ¬((2 : Fin 4) = utmScratchTape) from by decide]
          show sim₂.writeAndMove Γw.one.toΓ Dir3.right = sim₃
          have hhead : (sim₂.writeAndMove Γw.one.toΓ Dir3.right).head = sim₃.head := by
            rw [writeAndMove_right_head, hsim2_head]
          have hcells : (sim₂.writeAndMove Γw.one.toΓ Dir3.right).cells = sim₃.cells := by
            funext j; simp only [sim₃]
            by_cases hj0 : j = 1 + 3 * done
            · subst hj0; simp only [↓reduceIte]
              rw [writeAndMove_cells_ne (by rw [hsim2_head]; omega),
                writeAndMove_cells_ne (by rw [hsim1_head]; omega)]
              conv_lhs => rw [← hsim_h]
              exact writeAndMove_cells_at_head (by omega)
            · simp only [hj0, ↓reduceIte]
              by_cases hj1 : j = 1 + 3 * done + 1
              · subst hj1; simp only [↓reduceIte]
                rw [writeAndMove_cells_ne (by rw [hsim2_head]; omega)]
                conv_lhs => rw [← hsim1_head]
                exact writeAndMove_cells_at_head (by omega)
              · simp only [hj1, ↓reduceIte]
                by_cases hj2 : j = 1 + 3 * done + 2
                · subst hj2; simp only [↓reduceIte]
                  conv_lhs => rw [← hsim2_head]
                  exact writeAndMove_cells_at_head (by omega)
                · simp only [hj2, ↓reduceIte]
                  rw [writeAndMove_cells_ne (by rw [hsim2_head]; omega),
                    writeAndMove_cells_ne (by rw [hsim1_head]; omega),
                    writeAndMove_cells_ne (by rw [hsim_h]; omega)]
          exact match sim₂.writeAndMove Γw.one.toΓ Dir3.right, sim₃, hhead, hcells with
            | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
        · by_cases hi3 : i = utmScratchTape
          · -- Scratch tape: readBackWrite + right → produces sc₃
            subst hi3
            show (c.work utmScratchTape).writeAndMove
              (readBackWrite (c.work utmScratchTape).read).toΓ Dir3.right = sc₃
            have hhead : ((c.work utmScratchTape).writeAndMove
              (readBackWrite (c.work utmScratchTape).read).toΓ Dir3.right).head = sc₃.head := by
              rw [writeAndMove_right_head]
            have hcells : ((c.work utmScratchTape).writeAndMove
              (readBackWrite (c.work utmScratchTape).read).toΓ Dir3.right).cells = sc₃.cells := by
              simp only [sc₃]
              exact readBackWrite_cells (by rw [hsc_h]; omega)
                (fun j hj => hwf.2 utmScratchTape j hj)
            exact match (c.work utmScratchTape).writeAndMove _ Dir3.right, sc₃, hhead, hcells with
              | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
          · -- Other tapes: idle (readBackWrite + idleDir)
            have hi2v : ¬(i.val = 2) := fun heq => hi2 (Fin.ext heq)
            have hi3v : ¬(i.val = 3) := fun heq => hi3 (Fin.ext heq)
            simp only [hi2, hi3, ↓reduceIte, hi2v, hi3v,
              show (readBackWrite (c.work i).read).toΓ = readBackWrite (c.work i).read from rfl,
              show ¬(i = utmScratchTape) from hi3]
            exact hwk_id i
      -- ── Combine: reachesIn 3 c c₃ ──
      -- hstep1 : step c = some raw₁
      -- hstep2_raw : step raw₁ = some {.pos0Write3, ..sim₂..}
      -- hstep3_raw : step {.pos0Write3, ..sim₂..} = some c₃
      exact .step hstep1 (.step hstep2_raw (.step hstep3_raw .zero))
    -- Apply IH
    have hih := ih (done + 1) (by omega) c₃ (by omega)
      (by show c₃.state = .pos0Write1; rfl)
      (by show sim₃.head = 1 + 3 * (done + 1); simp [sim₃]; omega)
      (by intro j hj1 hjn; show sim₃.cells j = Γ.one; simp only [sim₃]
          by_cases h1 : j = 1 + 3 * done
          · simp [h1]
          · by_cases h2 : j = 1 + 3 * done + 1
            · simp [h1, h2]
            · by_cases h3 : j = 1 + 3 * done + 2
              · simp [h1, h2, h3]
              · simp [h1, h2, h3]; exact hsim_ones j hj1 (by omega))
      (by intro j hj; show sim₃.cells j = Γ.blank; simp only [sim₃]
          have : j ≠ 1 + 3 * done := by omega
          have : j ≠ 1 + 3 * done + 1 := by omega
          have : j ≠ 1 + 3 * done + 2 := by omega
          simp [*]; exact hsim_blank j (by omega))
      (by show sim₃.cells 0 = Γ.start; simp only [sim₃]
          simp (config := { decide := true }) [show 0 ≠ 1 + 3 * done from by omega,
            show 0 ≠ 1 + 3 * done + 1 from by omega, show 0 ≠ 1 + 3 * done + 2 from by omega]
          exact hsim0)
      (by show sc₃.head = 1 + (done + 1); simp [sc₃, hsc_h]; omega)
      (by intro j hj hjn; show sc₃.cells j = Γ.one; simp only [sc₃]
          exact hsc_ones j (by omega) hjn)
      hsc_sentinel
      (by show sc₃.cells 0 = Γ.start; simp [sc₃]; exact hsc0)
      hsc_ns
      (by constructor
          · intro i; show (c₃.work i).cells 0 = Γ.start; simp only [c₃]
            by_cases h2 : i = utmSimTape
            · simp [h2, sim₃, show 0 ≠ 1 + 3 * done from by omega,
                show 0 ≠ 1 + 3 * done + 1 from by omega, show 0 ≠ 1 + 3 * done + 2 from by omega]
              exact hsim0
            · by_cases h3 : i = utmScratchTape
              · simp [h2, h3, sc₃]; exact hsc0
              · simp [h2, h3]; exact hwf.1 i
          · intro i j hj; show (c₃.work i).cells j ≠ Γ.start; simp only [c₃]
            by_cases h2 : i = utmSimTape
            · simp only [h2, ↓reduceIte, sim₃]
              by_cases h4 : j = 1 + 3 * done
              · simp [h4]
              · by_cases h5 : j = 1 + 3 * done + 1
                · simp [h4, h5]
                · by_cases h6 : j = 1 + 3 * done + 2
                  · simp [h4, h5, h6]
                  · simp [h4, h5, h6]; exact hwf.2 utmSimTape j hj
            · by_cases h3 : i = utmScratchTape
              · simp [h2, h3, sc₃]; exact hwf.2 utmScratchTape j hj
              · simp [h2, h3]; exact hwf.2 i j hj)
      hinp_h hinp_ns hout_h hout_ns
      (by show (c₃.work utmDescTape).head ≥ 1
          simp only [c₃, show utmDescTape ≠ utmSimTape from by decide,
            show utmDescTape ≠ utmScratchTape from by decide, ↓reduceIte]
          exact hdesc_h)
      (by show (c₃.work utmStateTape).head ≥ 1
          simp only [c₃, show utmStateTape ≠ utmSimTape from by decide,
            show utmStateTape ≠ utmScratchTape from by decide, ↓reduceIte]
          exact hst_h)
    obtain ⟨c', hreach_ih, hst', hsim_h', hsim_ones', hsim_blank', hsim0',
            hdesc', hstate', hinp', hout', hwf', hsc_h', hsc_ones', hsc_sent', hsc0'⟩ := hih
    refine ⟨c', ?_, hst', hsim_h', hsim_ones', hsim_blank', hsim0', ?_, ?_, ?_, ?_, hwf', hsc_h',
            hsc_ones', hsc_sent', hsc0'⟩
    · have : 3 * (m + 1) + 1 = 3 + (3 * m + 1) := by omega
      rw [this]; exact reachesIn_trans setupSimTM hreach3 hreach_ih
    · rw [hdesc']; show c₃.work utmDescTape = c.work utmDescTape
      simp only [c₃, show utmDescTape ≠ utmSimTape from by decide,
        show utmDescTape ≠ utmScratchTape from by decide, ↓reduceIte]
    · rw [hstate']; show c₃.work utmStateTape = c.work utmStateTape
      simp only [c₃, show utmStateTape ≠ utmSimTape from by decide,
        show utmStateTape ≠ utmScratchTape from by decide, ↓reduceIte]
    · rw [hinp']
    · rw [hout']

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
    (hwf : WorkTapesWF work)
    (hdesc_h : (work utmDescTape).head ≥ 1)
    (hst_h : (work utmStateTape).head ≥ 1) :
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
      (c'.work utmScratchTape).head = n + 1 ∧
      c'.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧
      c'.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) := by
  -- Phase 1: call phase1_loop with done=0
  have hsc_ns : ∀ j, j ≥ 1 → j ≤ n → (work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj1 hjn; rw [hsc_ones j hj1 hjn]; decide
  obtain ⟨c1, hreach1, hst1, hsim_h1, hsim_ones1, hsim_blank1, hsim0_1,
          hdesc1, hstate1, hinp1, hout1, hwf1, hsc_h1, hsc_ones1, hsc_sent1, hsc0_1⟩ :=
    phase1_loop 0 ⟨.pos0Write1, inp, work, out⟩
      (by omega) rfl
      (by simp [hsim_head])
      (by intro j hj1 hj0; omega)
      (by intro j hj; exact hsim_blank j (by omega))
      hsim0
      (by simp [hsc_head])
      (by intro j hj hjn; exact hsc_ones j (by omega) hjn)
      hsc_sentinel hsc0 hsc_ns hwf hinp_h hinp_ns hout_h hout_ns hdesc_h hst_h
  -- c1: state = pos0Extra1, sim has ones at 1..3n, head at 1+3n
  -- Now we need 6 simWriteRight steps + 1 advanceInput step
  -- Idle-preservation helpers for c1
  have hinp1_h : c1.input.head ≥ 1 := by rw [hinp1]; exact hinp_h
  have hinp1_ns : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
    intro j hj; rw [show c1.input.cells = inp.cells from congrArg Tape.cells hinp1]; exact hinp_ns j hj
  have hout1_h : c1.output.head ≥ 1 := by rw [hout1]; exact hout_h
  have hout1_ns : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by
    intro j hj; rw [show c1.output.cells = out.cells from congrArg Tape.cells hout1]; exact hout_ns j hj
  have hdesc1_h : (c1.work utmDescTape).head ≥ 1 := by rw [hdesc1]; exact hdesc_h
  have hst1_h : (c1.work utmStateTape).head ≥ 1 := by rw [hstate1]; exact hst_h
  -- Helper: all work tape heads ≥ 1
  have hwk1_heads : ∀ i : Fin 4, (c1.work i).head ≥ 1 := fun
    | ⟨0, _⟩ => hdesc1_h | ⟨1, _⟩ => hst1_h
    | ⟨2, _⟩ => by show (c1.work utmSimTape).head ≥ 1; omega
    | ⟨3, _⟩ => by show (c1.work utmScratchTape).head ≥ 1; omega
  -- Helper: idle preservation for work tapes
  have hwk1_id : ∀ i : Fin 4,
      (c1.work i).writeAndMove (readBackWrite (c1.work i).read) (idleDir (c1.work i).read) = c1.work i :=
    fun i => idle_tape_preserved (hwk1_heads i) (fun j hj => hwf1.2 i j hj)
  -- Helper: idle input preservation
  have hinp1_idle : c1.input.move (idleDir c1.input.read) = c1.input :=
    idle_input_preserved hinp1_h hinp1_ns
  -- Helper: idle output preservation
  have hout1_idle : c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read) = c1.output :=
    idle_tape_preserved hout1_h hout1_ns
  -- Define the sim tape after each extra write
  -- Each simWriteRight step writes Γ.one at sim head and moves right
  -- Start: sim head at 1+3*n, need to write at positions 1+3*n, 1+3*n+1, ..., 1+3*n+5
  -- After 6 writes: head at 1+3*n+6 = 1+3*(n+2)
  -- Helper for a single simWriteRight step
  -- For simWriteRight steps, the non-sim work tapes are idle
  have hwk1_simwrite_idle : ∀ i : Fin 4, i ≠ utmSimTape →
      (c1.work i).writeAndMove
        (if i.val = 2 then Γw.one else readBackWrite ((c1.work i).read)).toΓ
        (if i.val = 2 then Dir3.right else idleDir ((c1.work i).read)) = c1.work i := by
    intro i hi
    have hival : ¬(i.val = 2) := fun heq => hi (Fin.ext heq)
    simp only [hival, ↓reduceIte,
      show (readBackWrite (c1.work i).read).toΓ = readBackWrite (c1.work i).read from rfl]
    exact hwk1_id i
  -- Define sim tape state after k extra writes (k = 0..6)
  -- sim_k has head at 1+3*n+k and ones written at 1+3*n .. 1+3*n+k-1
  -- We define the final sim tape after 6 writes
  let simE : ℕ → Tape
    | 0 => c1.work utmSimTape
    | k + 1 => (simE k).writeAndMove Γw.one Dir3.right
  -- Key properties of simE
  have simE_head : ∀ k, (simE k).head = 1 + 3 * n + k := by
    intro k; induction k with
    | zero => exact hsim_h1
    | succ k ih => simp only [simE]; rw [writeAndMove_right_head, ih]
  have simE_cells_new : ∀ k j, j ≥ 1 + 3 * n → j < 1 + 3 * n + k →
      (simE k).cells j = Γ.one := by
    intro k; induction k with
    | zero => intro j hj1 hj2; omega
    | succ k ih =>
      intro j hj1 hj2
      simp only [simE]
      by_cases hj : j = (simE k).head
      · rw [hj]; exact writeAndMove_cells_at_head (by rw [simE_head]; omega)
      · rw [writeAndMove_cells_ne hj]
        exact ih j hj1 (by rw [simE_head] at hj; omega)
  have simE_cells_old : ∀ k j, j < 1 + 3 * n →
      (simE k).cells j = (c1.work utmSimTape).cells j := by
    intro k; induction k with
    | zero => intro j _; rfl
    | succ k ih =>
      intro j hj
      simp only [simE]
      rw [writeAndMove_cells_ne (by rw [simE_head]; omega)]
      exact ih j hj
  have simE_cells_future : ∀ k j, j ≥ 1 + 3 * n + k →
      (simE k).cells j = (c1.work utmSimTape).cells j := by
    intro k; induction k with
    | zero => intro j _; rfl
    | succ k ih =>
      intro j hj
      simp only [simE]
      rw [writeAndMove_cells_ne (by rw [simE_head]; omega)]
      exact ih j (by omega)
  -- 6 simWriteRight steps: pos0Extra1 → pos0Extra2 → ... → pos0Extra6 → advanceInput
  -- We prove each step produces a config with the next state and simE (k+1)
  -- Step function for simWriteRight: given a config with state s, sim tape = simE k,
  -- input/output/other work tapes = c1's, produces a config with next state, simE (k+1)
  have simWriteRight_step : ∀ (s next : SetupSimPhase)
      (k : ℕ) (hk : k < 6)
      (htrans : ∀ iHead wHeads oHead,
        setupSimTM.δ s iHead wHeads oHead = simWriteRight next .one iHead wHeads oHead),
      setupSimTM.step
        { state := s, input := c1.input,
          work := fun i => if i = utmSimTape then simE k else c1.work i,
          output := c1.output } = some
        { state := next, input := c1.input,
          work := fun i => if i = utmSimTape then simE (k + 1) else c1.work i,
          output := c1.output } := by
    intro s next k hk htrans
    unfold TM.step
    simp only [show s ≠ SetupSimPhase.done from by intro h; cases s <;> simp_all [SetupSimPhase.done],
      ↓reduceIte]
    -- The δ for this state is simWriteRight next .one
    -- We need to show the read heads and resulting config match
    have hsim_read : (fun i => (if i = utmSimTape then simE k else c1.work i).read) =
        fun i => if i = utmSimTape then (simE k).read else (c1.work i).read := by
      funext i; split <;> simp_all
    conv_lhs => rw [show (if (utmSimTape : Fin 4) = utmSimTape then simE k else c1.work utmSimTape).read =
      (simE k).read from by simp]
    rw [htrans]
    simp only [simWriteRight]
    congr 1
    refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp1_idle, ?_, hout1_idle⟩
    funext i
    by_cases hi : i = utmSimTape
    · subst hi; simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte, simE,
        show Γw.toΓ Γw.one = Γ.one from rfl]
    · have hival : ¬(i.val = 2) := fun heq => hi (Fin.ext heq)
      simp only [hi, ↓reduceIte, hival,
        show (readBackWrite (if i = utmSimTape then simE k else c1.work i).read).toΓ =
          readBackWrite (c1.work i).read from by simp [hi, show (readBackWrite _).toΓ = readBackWrite _ from rfl]]
      exact hwk1_id i
  -- Now chain the 6 steps
  have hstepE1 := simWriteRight_step .pos0Extra1 .pos0Extra2 0 (by omega) (by intro _ _ _; rfl)
  have hstepE2 := simWriteRight_step .pos0Extra2 .pos0Extra3 1 (by omega) (by intro _ _ _; rfl)
  have hstepE3 := simWriteRight_step .pos0Extra3 .pos0Extra4 2 (by omega) (by intro _ _ _; rfl)
  have hstepE4 := simWriteRight_step .pos0Extra4 .pos0Extra5 3 (by omega) (by intro _ _ _; rfl)
  have hstepE5 := simWriteRight_step .pos0Extra5 .pos0Extra6 4 (by omega) (by intro _ _ _; rfl)
  have hstepE6 := simWriteRight_step .pos0Extra6 .advanceInput 5 (by omega) (by intro _ _ _; rfl)
  -- The config after 6 extras: state = advanceInput, sim = simE 6
  -- c1 has state = pos0Extra1, so the starting config for extras is:
  -- { state := pos0Extra1, input := c1.input, work := fun i => if i = utmSimTape then simE 0 else c1.work i, output := c1.output }
  -- But simE 0 = c1.work utmSimTape, so this equals c1
  have hc1_eq : c1 = { state := SetupSimPhase.pos0Extra1, input := c1.input,
      work := fun i => if i = utmSimTape then simE 0 else c1.work i,
      output := c1.output } := by
    cases c1; simp only [hst1, simE]; congr 1; funext i; simp
  -- 6-step reachesIn for extras
  have hreach_extras : setupSimTM.reachesIn 6 c1
      { state := .advanceInput, input := c1.input,
        work := fun i => if i = utmSimTape then simE 6 else c1.work i,
        output := c1.output } := by
    conv_lhs => rw [hc1_eq]
    exact .step hstepE1 (.step hstepE2 (.step hstepE3 (.step hstepE4 (.step hstepE5 (.step hstepE6 .zero)))))
  -- advanceInput step: input moves right, rest idle
  -- State: advanceInput → checkInput
  -- Input: move right (Dir3.right)
  -- Work: idleDir for all
  -- Output: idleDir
  let cAdv : Cfg 4 setupSimTM.Q :=
    { state := .advanceInput, input := c1.input,
      work := fun i => if i = utmSimTape then simE 6 else c1.work i,
      output := c1.output }
  have hstepAdv : setupSimTM.step cAdv = some
      { state := .checkInput,
        input := c1.input.move Dir3.right,
        work := fun i => if i = utmSimTape then simE 6 else c1.work i,
        output := c1.output } := by
    unfold TM.step
    simp only [show SetupSimPhase.advanceInput ≠ SetupSimPhase.done from nofun, ↓reduceIte,
      setupSimTM, cAdv]
    congr 1
    refine Cfg.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_, hout1_idle⟩
    funext i
    by_cases hi : i = utmSimTape
    · subst hi; simp only [utmSimTape, ↓reduceIte]
      exact hwk1_id utmSimTape
    · simp only [hi, ↓reduceIte]
      exact hwk1_id i
  -- Total: 6 + 1 = 7 more steps
  have hreach_adv : setupSimTM.reachesIn 7 c1
      { state := .checkInput,
        input := c1.input.move Dir3.right,
        work := fun i => if i = utmSimTape then simE 6 else c1.work i,
        output := c1.output } := by
    have : (7 : ℕ) = 6 + 1 := by omega
    rw [this]
    exact reachesIn_trans setupSimTM hreach_extras (.step hstepAdv .zero)
  -- Compose phase1 + extras+advance: (3*n+1) + 7 = 3*n+8
  let cFinal : Cfg 4 setupSimTM.Q :=
    { state := .checkInput,
      input := c1.input.move Dir3.right,
      work := fun i => if i = utmSimTape then simE 6 else c1.work i,
      output := c1.output }
  have hreach_total : setupSimTM.reachesIn (3 * n + 8)
      ⟨.pos0Write1, inp, work, out⟩ cFinal := by
    have : 3 * n + 8 = (3 * (n - 0) + 1) + 7 := by omega
    rw [this]
    exact reachesIn_trans setupSimTM hreach1 hreach_adv
  -- Now prove all the postconditions about cFinal
  refine ⟨cFinal, hreach_total, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- sim cells 0 = start
  · show (simE 6).cells 0 = Γ.start
    rw [simE_cells_old 6 0 (by omega)]; exact hsim0_1
  -- sim head = 1 + 3*(n+2)
  · show (simE 6).head = 1 + 3 * (n + 2)
    rw [simE_head]; ring
  -- sim ones at 1..3*(n+2)
  · intro j hj1 hjn
    show (simE 6).cells j = Γ.one
    by_cases hlt : j < 1 + 3 * n
    · rw [simE_cells_old 6 j hlt]; exact hsim_ones1 j hj1 (by omega)
    · exact simE_cells_new 6 j (by omega) (by omega)
  -- sim blanks after 3*(n+2)
  · intro j hj
    show (simE 6).cells j = Γ.blank
    rw [simE_cells_future 6 j (by omega)]
    exact hsim_blank1 j (by omega)
  -- desc tape preserved
  · show (if utmDescTape = utmSimTape then simE 6 else c1.work utmDescTape) = work utmDescTape
    simp only [show utmDescTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hdesc1
  -- state tape preserved
  · show (if utmStateTape = utmSimTape then simE 6 else c1.work utmStateTape) = work utmStateTape
    simp only [show utmStateTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hstate1
  -- input head = inp.head + 1
  · show (c1.input.move Dir3.right).head = inp.head + 1
    simp only [Tape.move, hinp1]; ring
  -- input cells = inp.cells
  · show (c1.input.move Dir3.right).cells = inp.cells
    simp only [Tape.move]; rw [show c1.input.cells = inp.cells from congrArg Tape.cells hinp1]
  -- output = out
  · exact hout1
  -- WorkTapesWF
  · constructor
    · intro i
      show (if i = utmSimTape then simE 6 else c1.work i).cells 0 = Γ.start
      by_cases hi : i = utmSimTape
      · simp only [hi, ↓reduceIte]; rw [simE_cells_old 6 0 (by omega)]; exact hsim0_1
      · simp only [hi, ↓reduceIte]; exact hwf1.1 i
    · intro i j hj
      show (if i = utmSimTape then simE 6 else c1.work i).cells j ≠ Γ.start
      by_cases hi : i = utmSimTape
      · simp only [hi, ↓reduceIte]
        by_cases hlt : j < 1 + 3 * n
        · rw [simE_cells_old 6 j hlt]; exact hwf1.2 utmSimTape j hj
        · by_cases hlt2 : j < 1 + 3 * n + 6
          · rw [simE_cells_new 6 j (by omega) hlt2]; decide
          · rw [simE_cells_future 6 j (by omega)]; exact hwf1.2 utmSimTape j hj
      · simp only [hi, ↓reduceIte]; exact hwf1.2 i j hj
  -- scratch ones
  · intro j hj1 hjn
    show (if utmScratchTape = utmSimTape then simE 6 else c1.work utmScratchTape).cells j = Γ.one
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hsc_ones1 j hj1 hjn
  -- scratch sentinel
  · show (if utmScratchTape = utmSimTape then simE 6 else c1.work utmScratchTape).cells (n + 1) = Γ.blank
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hsc_sent1
  -- scratch cells 0
  · show (if utmScratchTape = utmSimTape then simE 6 else c1.work utmScratchTape).cells 0 = Γ.start
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hsc0_1
  -- scratch head
  · show (if utmScratchTape = utmSimTape then simE 6 else c1.work utmScratchTape).head = n + 1
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hsc_h1
  -- input head ≥ 1
  · show (c1.input.move Dir3.right).head ≥ 1
    simp [Tape.move, hinp1]; omega
  -- input cells ≠ start
  · intro j hj
    show (c1.input.move Dir3.right).cells j ≠ Γ.start
    simp only [Tape.move]; rw [show c1.input.cells = inp.cells from congrArg Tape.cells hinp1]
    exact hinp_ns j hj
  -- output head ≥ 1
  · exact hout1_h
  -- output cells ≠ start
  · exact hout1_ns

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
    (hsc_head : (c.work utmScratchTape).head = n + 1)
    -- input tape
    (hinp_h : c.input.head ≥ 1)
    (hinp_ns : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hinp_x : ∀ (i : ℕ) (hi : i < x.length),
      c.input.cells (c.input.head + i) = Γ.ofBool (x.get ⟨i, hi⟩))
    (hinp_end : c.input.cells (c.input.head + x.length) = Γ.blank)
    -- output + wf
    (hout_h : c.output.head ≥ 1)
    (hout_ns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hwf : WorkTapesWF c.work)
    (hdesc_h : (c.work utmDescTape).head ≥ 1)
    (hst_h : (c.work utmStateTape).head ≥ 1) :
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
    (hwf : WorkTapesWF work)
    (hdesc_h : (work utmDescTape).head ≥ 1)
    (hst_h : (work utmStateTape).head ≥ 1) :
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
      hdesc_h hst_h
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
      (by rw [hdesc1]; exact hdesc_h) (by rw [hstate1]; exact hst_h)
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
