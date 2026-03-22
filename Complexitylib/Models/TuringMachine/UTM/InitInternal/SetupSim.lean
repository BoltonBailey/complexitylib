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
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells := by
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
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hinp_id, hout_id, ?_, ?_, ?_⟩
    · dsimp only []; rw [hwk_id utmSimTape, hsim_h, hdn]
    · intro j hj1 hjn; dsimp only []; rw [hwk_id utmSimTape]; exact hsim_ones j hj1 (by omega)
    · intro j hj; dsimp only []; rw [hwk_id utmSimTape]; exact hsim_blank j (by omega)
    · dsimp only []; rw [hwk_id utmSimTape]; exact hsim0
    · exact hwk_id utmDescTape
    · exact hwk_id utmStateTape
    · exact ⟨fun i => by dsimp only []; rw [hwk_id i]; exact hwf.1 i,
             fun i j hj => by dsimp only []; rw [hwk_id i]; exact hwf.2 i j hj⟩
    · dsimp only []; rw [hwk_id utmScratchTape, hsc_h, hdn]; omega
    · dsimp only []; exact congrArg Tape.cells (hwk_id utmScratchTape)
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
            hdesc', hstate', hinp', hout', hwf', hsc_h', hsc_cells'⟩ := hih
    refine ⟨c', ?_, hst', hsim_h', hsim_ones', hsim_blank', hsim0', ?_, ?_, ?_, ?_, hwf', hsc_h', ?_⟩
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
    · rw [hsc_cells']; show sc₃.cells = (c.work utmScratchTape).cells; rfl

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
  -- ── Scratch tape: cells ≥ 1 are not start ──
  have hsc_ns : ∀ j, j ≥ 1 → j ≤ n → (work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj hjn; rw [hsc_ones j hj hjn]; decide
  -- ── Phase 1: invoke phase1_loop at done=0 ──
  obtain ⟨c1, hreach1, hst1, hsim_head1, hsim_ones1, hsim_blank1, hsim0_1,
          hdesc1, hstate1, hinp1, hout1, hwf1, hsc_head1, hsc_cells1⟩ :=
    phase1_loop 0 ⟨.pos0Write1, inp, work, out⟩ (by omega) rfl
      (by simp [hsim_head]) (by intro j hj hjn; omega)
      (fun j _ => hsim_blank j (by omega)) hsim0
      (by simp [hsc_head]) (fun j hj hjn => hsc_ones j (by omega) hjn)
      hsc_sentinel hsc0 hsc_ns hwf hinp_h hinp_ns hout_h hout_ns hdesc_h hst_h
  -- c1: state=pos0Extra1, sim head=1+3n, ones at 1..3n, blanks after
  -- c1.input = inp, c1.output = out, desc/state preserved, scratch head=n+1
  -- ── Idle helpers for c1 ──
  have hinp_h1 : c1.input.head ≥ 1 := by rw [hinp1]; exact hinp_h
  have hinp_ns1 : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by rw [hinp1]; exact hinp_ns
  have hout_h1 : c1.output.head ≥ 1 := by rw [hout1]; exact hout_h
  have hout_ns1 : ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start := by rw [hout1]; exact hout_ns
  -- Non-sim work tapes: head ≥ 1, no start at ≥ 1
  have hwk_nonsim_h : ∀ (i : Fin 4), i ≠ utmSimTape → (c1.work i).head ≥ 1 := by
    intro ⟨iv, hiv⟩ hi
    have : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · show (c1.work utmDescTape).head ≥ 1; rw [hdesc1]; exact hdesc_h
    · show (c1.work utmStateTape).head ≥ 1; rw [hstate1]; exact hst_h
    · exact absurd rfl hi
    · show (c1.work utmScratchTape).head ≥ 1; rw [hsc_head1]; omega
  -- ── Phase 1 extras: 6 simWriteRight steps ──
  let s0 := c1.work utmSimTape
  let s1 := s0.writeAndMove Γw.one Dir3.right
  let s2 := s1.writeAndMove Γw.one Dir3.right
  let s3 := s2.writeAndMove Γw.one Dir3.right
  let s4 := s3.writeAndMove Γw.one Dir3.right
  let s5 := s4.writeAndMove Γw.one Dir3.right
  let s6 := s5.writeAndMove Γw.one Dir3.right
  have s0_head : s0.head = 1 + 3 * n := hsim_head1
  have s1_head : s1.head = 1 + 3 * n + 1 := by
    show (s0.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s0_head]
  have s2_head : s2.head = 1 + 3 * n + 2 := by
    show (s1.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s1_head]
  have s3_head : s3.head = 1 + 3 * n + 3 := by
    show (s2.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s2_head]
  have s4_head : s4.head = 1 + 3 * n + 4 := by
    show (s3.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s3_head]
  have s5_head : s5.head = 1 + 3 * n + 5 := by
    show (s4.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s4_head]
  have s6_head : s6.head = 1 + 3 * n + 6 := by
    show (s5.writeAndMove _ _).head = _; rw [writeAndMove_right_head, s5_head]
  -- Cells outside [1+3n, 1+3n+6) unchanged
  have cells_old : ∀ j, (j < 1 + 3 * n ∨ j ≥ 1 + 3 * n + 6) → s6.cells j = s0.cells j := by
    intro j hj; show (s5.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s5_head]; omega)]
    show (s4.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s4_head]; omega)]
    show (s3.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s3_head]; omega)]
    show (s2.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s2_head]; omega)]
    show (s1.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s1_head]; omega)]
    show (s0.writeAndMove _ _).cells j = _
    rw [writeAndMove_cells_ne (by rw [s0_head]; omega)]
  -- Ones in [1+3n, 1+3n+6)
  have wam_at_head : ∀ (t : Tape) (hh : t.head ≠ 0),
      (t.writeAndMove Γw.one Dir3.right).cells t.head = Γ.one :=
    fun t hh => @writeAndMove_cells_at_head t Γw.one Dir3.right hh
  have cells_new : ∀ j, j ≥ 1 + 3 * n → j < 1 + 3 * n + 6 → s6.cells j = Γ.one := by
    intro j hj hjlt; show (s5.writeAndMove _ _).cells j = _
    by_cases h5 : j = 1 + 3 * n + 5
    · rw [h5, ← s5_head]; exact wam_at_head s5 (by rw [s5_head]; omega)
    · rw [writeAndMove_cells_ne (by rw [s5_head]; omega)]
      show (s4.writeAndMove _ _).cells j = _
      by_cases h4 : j = 1 + 3 * n + 4
      · rw [h4, ← s4_head]; exact wam_at_head s4 (by rw [s4_head]; omega)
      · rw [writeAndMove_cells_ne (by rw [s4_head]; omega)]
        show (s3.writeAndMove _ _).cells j = _
        by_cases h3 : j = 1 + 3 * n + 3
        · rw [h3, ← s3_head]; exact wam_at_head s3 (by rw [s3_head]; omega)
        · rw [writeAndMove_cells_ne (by rw [s3_head]; omega)]
          show (s2.writeAndMove _ _).cells j = _
          by_cases h2 : j = 1 + 3 * n + 2
          · rw [h2, ← s2_head]; exact wam_at_head s2 (by rw [s2_head]; omega)
          · rw [writeAndMove_cells_ne (by rw [s2_head]; omega)]
            show (s1.writeAndMove _ _).cells j = _
            by_cases h1 : j = 1 + 3 * n + 1
            · rw [h1, ← s1_head]; exact wam_at_head s1 (by rw [s1_head]; omega)
            · rw [writeAndMove_cells_ne (by rw [s1_head]; omega)]
              show (s0.writeAndMove _ _).cells j = _
              have : j = 1 + 3 * n := by omega
              rw [this, ← s0_head]; exact wam_at_head s0 (by rw [s0_head]; omega)
  have s6_all_ones : ∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → s6.cells j = Γ.one := by
    intro j hj hjn
    by_cases hjlt : j < 1 + 3 * n
    · rw [cells_old j (Or.inl hjlt)]; exact hsim_ones1 j hj (by omega)
    · exact cells_new j (by omega) (by omega)
  have s6_blanks : ∀ j, j > 3 * (n + 2) → s6.cells j = Γ.blank := by
    intro j hj; rw [cells_old j (Or.inr (by omega))]; exact hsim_blank1 j (by omega)
  have s6_cell0 : s6.cells 0 = Γ.start := by
    rw [cells_old 0 (Or.inl (by omega))]; exact hsim0_1
  -- No start at ≥ 1 for s0..s6
  have s0_ns : ∀ j, j ≥ 1 → s0.cells j ≠ Γ.start := hwf1.2 utmSimTape
  have wam_ns : ∀ (t : Tape), t.head ≥ 1 → (∀ j, j ≥ 1 → t.cells j ≠ Γ.start) →
      ∀ j, j ≥ 1 → (t.writeAndMove Γw.one Dir3.right).cells j ≠ Γ.start := by
    intro t ht hns j hj
    by_cases heq : j = t.head
    · subst heq; rw [wam_at_head t (by omega)]; decide
    · rw [writeAndMove_cells_ne heq]; exact hns j hj
  have s1_ns : ∀ j, j ≥ 1 → s1.cells j ≠ Γ.start := wam_ns s0 (by omega) s0_ns
  have s2_ns : ∀ j, j ≥ 1 → s2.cells j ≠ Γ.start := wam_ns s1 (by omega) s1_ns
  have s3_ns : ∀ j, j ≥ 1 → s3.cells j ≠ Γ.start := wam_ns s2 (by omega) s2_ns
  have s4_ns : ∀ j, j ≥ 1 → s4.cells j ≠ Γ.start := wam_ns s3 (by omega) s3_ns
  have s5_ns : ∀ j, j ≥ 1 → s5.cells j ≠ Γ.start := wam_ns s4 (by omega) s4_ns
  have s6_ns : ∀ j, j ≥ 1 → s6.cells j ≠ Γ.start := wam_ns s5 (by omega) s5_ns
  -- ── Generic simWriteRight step ──
  have simwr_step : ∀ (phase_in phase_out : SetupSimPhase) (st : Tape),
      st.head ≥ 1 → (∀ j, j ≥ 1 → st.cells j ≠ Γ.start) →
      (∀ iHead (wHeads : Fin 4 → Γ) oHead,
        setupSimTM.δ phase_in iHead wHeads oHead =
          simWriteRight phase_out .one iHead wHeads oHead) →
      phase_in ≠ .done →
      setupSimTM.step
        { state := phase_in, input := c1.input,
          work := fun i => if i = utmSimTape then st else c1.work i,
          output := c1.output } =
      some { state := phase_out, input := c1.input,
             work := fun i => if i = utmSimTape then st.writeAndMove Γw.one Dir3.right
                              else c1.work i,
             output := c1.output } := by
    intro phase_in phase_out st hst_h hst_ns hδ hne
    simp only [TM.step, show setupSimTM.qhalt = SetupSimPhase.done from rfl, hne, ↓reduceIte]
    have hδ' := hδ c1.input.read
      (fun i => ((if i = utmSimTape then st else c1.work i) : Tape).read) c1.output.read
    simp only [hδ', simWriteRight]
    congr 1
    refine Cfg.mk.injEq .. |>.mpr ⟨rfl, ?_, ?_, ?_⟩
    · exact idle_input_preserved hinp_h1 hinp_ns1
    · funext i
      by_cases hi : i = utmSimTape
      · subst hi; simp only [show (utmSimTape : Fin 4).val = 2 from rfl, ↓reduceIte]
      · have hival : ¬((i : Fin 4).val = 2) := fun h => hi (Fin.ext h)
        simp only [hi, hival, ↓reduceIte]
        rw [show (readBackWrite (c1.work i).read).toΓ = readBackWrite (c1.work i).read from rfl]
        exact idle_tape_preserved (hwk_nonsim_h i hi) (hwf1.2 i)
    · rw [show (readBackWrite c1.output.read).toΓ = readBackWrite c1.output.read from rfl]
      exact idle_tape_preserved hout_h1 hout_ns1
  -- Chain 6 steps
  have hstep_e1 := simwr_step .pos0Extra1 .pos0Extra2 s0 (by omega) s0_ns (by intros; rfl) (by decide)
  have hstep_e2 := simwr_step .pos0Extra2 .pos0Extra3 s1 (by omega) s1_ns (by intros; rfl) (by decide)
  have hstep_e3 := simwr_step .pos0Extra3 .pos0Extra4 s2 (by omega) s2_ns (by intros; rfl) (by decide)
  have hstep_e4 := simwr_step .pos0Extra4 .pos0Extra5 s3 (by omega) s3_ns (by intros; rfl) (by decide)
  have hstep_e5 := simwr_step .pos0Extra5 .pos0Extra6 s4 (by omega) s4_ns (by intros; rfl) (by decide)
  have hstep_e6 := simwr_step .pos0Extra6 .advanceInput s5 (by omega) s5_ns (by intros; rfl) (by decide)
  have hreach_extras : setupSimTM.reachesIn 6
      { state := .pos0Extra1, input := c1.input,
        work := fun i => if i = utmSimTape then s0 else c1.work i,
        output := c1.output }
      { state := .advanceInput, input := c1.input,
        work := fun i => if i = utmSimTape then s6 else c1.work i,
        output := c1.output } :=
    .step hstep_e1 (.step hstep_e2 (.step hstep_e3
      (.step hstep_e4 (.step hstep_e5 (.step hstep_e6 .zero)))))
  -- Rewrite starting config to use c1.work
  have hwork0 : (fun i => if i = utmSimTape then s0 else c1.work i) = c1.work := by
    funext i; show (if i = utmSimTape then c1.work utmSimTape else c1.work i) = _
    split <;> simp_all
  rw [hwork0] at hreach_extras
  -- ── Phase 2: advanceInput ──
  have hstep_adv : setupSimTM.step
      { state := .advanceInput, input := c1.input,
        work := fun i => if i = utmSimTape then s6 else c1.work i,
        output := c1.output } =
    some { state := .checkInput, input := c1.input.move Dir3.right,
           work := fun i => if i = utmSimTape then s6 else c1.work i,
           output := c1.output } := by
    simp only [TM.step, show SetupSimPhase.advanceInput ≠ SetupSimPhase.done from nofun,
      ↓reduceIte, setupSimTM]
    congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_, ?_⟩
    · funext i
      by_cases hi : i = utmSimTape
      · subst hi; simp only [↓reduceIte,
          show (readBackWrite (Tape.read s6)).toΓ = readBackWrite s6.read from rfl]
        exact idle_tape_preserved (by rw [s6_head]; omega) s6_ns
      · simp only [hi, ↓reduceIte,
          show (readBackWrite (c1.work i).read).toΓ = readBackWrite (c1.work i).read from rfl]
        exact idle_tape_preserved (hwk_nonsim_h i hi) (fun j hj => hwf1.2 i j hj)
    · exact idle_tape_preserved hout_h1 hout_ns1
  have hreach_67 : setupSimTM.reachesIn 7
      ⟨.pos0Extra1, c1.input, c1.work, c1.output⟩
      ⟨.checkInput, c1.input.move Dir3.right,
        fun i => if i = utmSimTape then s6 else c1.work i, c1.output⟩ := by
    have : (7 : ℕ) = 6 + 1 := by omega
    rw [this]; exact reachesIn_trans setupSimTM hreach_extras (.step hstep_adv .zero)
  have hc1_eq : (⟨.pos0Extra1, c1.input, c1.work, c1.output⟩ : Cfg 4 setupSimTM.Q) = c1 := by
    cases c1; simp only [Cfg.mk.injEq]; exact ⟨hst1.symm, trivial, trivial, trivial⟩
  rw [hc1_eq] at hreach_67
  -- ── Combine: 3n+1 + 7 = 3n+8 ──
  let cfinal : Cfg 4 setupSimTM.Q :=
    { state := .checkInput, input := c1.input.move Dir3.right,
      work := fun i => if i = utmSimTape then s6 else c1.work i, output := c1.output }
  have hreach_all : setupSimTM.reachesIn (3 * n + 8)
      ⟨.pos0Write1, inp, work, out⟩ cfinal := by
    have : 3 * n + 8 = (3 * (n - 0) + 1) + 7 := by omega
    rw [this]; exact reachesIn_trans setupSimTM hreach1 hreach_67
  -- ── Witness ──
  refine ⟨cfinal, hreach_all, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact s6_cell0
  · show s6.head = 1 + 3 * (n + 2); rw [s6_head]; omega
  · intro j hj hjn; exact s6_all_ones j hj hjn
  · intro j hj; exact s6_blanks j hj
  · show (if utmDescTape = utmSimTape then s6 else c1.work utmDescTape) = work utmDescTape
    simp only [show utmDescTape ≠ utmSimTape from by decide, ↓reduceIte]; exact hdesc1
  · show (if utmStateTape = utmSimTape then s6 else c1.work utmStateTape) = work utmStateTape
    simp only [show utmStateTape ≠ utmSimTape from by decide, ↓reduceIte]; exact hstate1
  · show (c1.input.move Dir3.right).head = inp.head + 1
    rw [hinp1]; simp [Tape.move]
  · show (c1.input.move Dir3.right).cells = inp.cells
    rw [hinp1]; simp [Tape.move]
  · exact hout1
  · constructor
    · intro i; show (cfinal.work i).cells 0 = Γ.start
      by_cases hi : i = utmSimTape
      · show (if i = utmSimTape then s6 else c1.work i).cells 0 = _; simp [hi]; exact s6_cell0
      · show (if i = utmSimTape then s6 else c1.work i).cells 0 = _; simp [hi]; exact hwf1.1 i
    · intro i j hj; show (cfinal.work i).cells j ≠ Γ.start
      by_cases hi : i = utmSimTape
      · show (if i = utmSimTape then s6 else c1.work i).cells j ≠ _; simp [hi]; exact s6_ns j hj
      · show (if i = utmSimTape then s6 else c1.work i).cells j ≠ _; simp [hi]; exact hwf1.2 i j hj
  · intro j hj hjn
    show (if utmScratchTape = utmSimTape then s6 else c1.work utmScratchTape).cells j = Γ.one
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    rw [hsc_cells1]; exact hsc_ones j hj hjn
  · show (if utmScratchTape = utmSimTape then s6 else c1.work utmScratchTape).cells (n + 1) = Γ.blank
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    rw [hsc_cells1]; exact hsc_sentinel
  · show (if utmScratchTape = utmSimTape then s6 else c1.work utmScratchTape).cells 0 = Γ.start
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    exact hwf1.1 utmScratchTape
  · show (if utmScratchTape = utmSimTape then s6 else c1.work utmScratchTape).head = n + 1
    simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]; exact hsc_head1
  · show (c1.input.move Dir3.right).head ≥ 1
    rw [hinp1]; simp [Tape.move]
  · show ∀ j, j ≥ 1 → (c1.input.move Dir3.right).cells j ≠ Γ.start
    rw [hinp1]; intro j hj; simp [Tape.move]; exact hinp_ns j hj
  · show c1.output.head ≥ 1; rw [hout1]; exact hout_h
  · show ∀ j, j ≥ 1 → c1.output.cells j ≠ Γ.start; rw [hout1]; exact hout_ns

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3 helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind scratch tape from head h to ▷, reaching `.bounceScratch` with head 1 in h+1 steps.
    All tapes except scratch are preserved; scratch cells unchanged. -/
private theorem rewindScratch_loop :
    ∀ (h : ℕ) (c : Cfg 4 setupSimTM.Q),
    c.state = .rewindScratch →
    (c.work utmScratchTape).head = h →
    WorkTapesWF c.work →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    (∀ i : Fin 4, i ≠ utmScratchTape → (c.work i).head ≥ 1) →
    ∃ c',
      setupSimTM.reachesIn (h + 1) c c' ∧
      c'.state = .bounceScratch ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work ∧
      (∀ i : Fin 4, (c'.work i).head ≥ 1) := by
  intro h
  -- Common idle helper used in both cases
  have htape_id_gen : ∀ (t : Tape), t.head ≥ 1 → (∀ j, j ≥ 1 → t.cells j ≠ Γ.start) →
      t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t :=
    fun t hh hns => idle_tape_preserved hh hns
  induction h with
  | zero =>
    intro c hstate hsc_head hwf hinp_h hinp_ns hout_h hout_ns hwk_nonscratch
    have hsc_read : (fun i => (c.work i).read) (3 : Fin 4) = Γ.start := by
      show (c.work utmScratchTape).read = Γ.start
      simp only [Tape.read, hsc_head]; exact hwf.1 utmScratchTape
    have hwk_id : ∀ i : Fin 4, i ≠ utmScratchTape →
        (c.work i).writeAndMove (readBackWrite (c.work i).read) (idleDir (c.work i).read) = c.work i :=
      fun i hi => htape_id_gen _ (hwk_nonscratch i hi) (fun j hj => hwf.2 i j hj)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
      idle_input_preserved hinp_h hinp_ns
    have hout_idle : c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) = c.output :=
      idle_tape_preserved hout_h hout_ns
    -- Define target config
    let sc' : Tape := ⟨1, (c.work utmScratchTape).cells⟩
    let c' : Cfg 4 setupSimTM.Q :=
      { state := .bounceScratch, input := c.input,
        work := fun i => if i = utmScratchTape then sc' else c.work i,
        output := c.output }
    have hstep : setupSimTM.step c = some c' := by
      unfold TM.step
      simp only [hstate, show SetupSimPhase.rewindScratch ≠ SetupSimPhase.done from nofun,
        ↓reduceIte, setupSimTM, hsc_read]
      congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
      funext i; by_cases hi : i = utmScratchTape
      · subst hi
        show (c.work utmScratchTape).writeAndMove _ Dir3.right = sc'
        simp only [show (utmScratchTape : Fin 4).val = 3 from rfl, ↓reduceIte, sc']
        simp only [Tape.writeAndMove, Tape.write, Tape.move, hsc_head, ↓reduceIte,
          init_tape_move_cells, Tape.read]
      · show _ = (if i = utmScratchTape then sc' else c.work i)
        simp only [hi, ↓reduceIte]
        have hival : ¬((i : Fin 4).val = 3) := fun h => hi (Fin.ext h)
        simp only [hival, ↓reduceIte]; exact hwk_id i hi
    refine ⟨c', .step hstep .zero, rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · dsimp only [c']; simp only [↓reduceIte, sc']
    · dsimp only [c']; simp only [↓reduceIte, sc']
    · intro i hi; dsimp only [c']; simp only [hi, ↓reduceIte]
    · constructor
      · intro i; show (c'.work i).cells 0 = Γ.start
        by_cases hi : i = utmScratchTape
        · simp only [c', hi, ↓reduceIte, sc']; exact hwf.1 utmScratchTape
        · simp only [c', hi, ↓reduceIte]; exact hwf.1 i
      · intro i j hj; show (c'.work i).cells j ≠ Γ.start
        by_cases hi : i = utmScratchTape
        · simp only [c', hi, ↓reduceIte, sc']; exact hwf.2 utmScratchTape j hj
        · simp only [c', hi, ↓reduceIte]; exact hwf.2 i j hj
    · intro i; show (c'.work i).head ≥ 1
      by_cases hi : i = utmScratchTape
      · simp only [c', hi, ↓reduceIte, sc']; omega
      · simp only [c', hi, ↓reduceIte]; exact hwk_nonscratch i hi
  | succ h ih =>
    intro c hstate hsc_head hwf hinp_h hinp_ns hout_h hout_ns hwk_nonscratch
    have hsc_read_ne : (fun i => (c.work i).read) (3 : Fin 4) ≠ Γ.start := by
      show (c.work utmScratchTape).read ≠ Γ.start
      simp only [Tape.read, hsc_head]; exact hwf.2 utmScratchTape _ (by omega)
    have hwk_id : ∀ i : Fin 4, i ≠ utmScratchTape →
        (c.work i).writeAndMove (readBackWrite (c.work i).read) (idleDir (c.work i).read) = c.work i :=
      fun i hi => htape_id_gen _ (hwk_nonscratch i hi) (fun j hj => hwf.2 i j hj)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
      idle_input_preserved hinp_h hinp_ns
    have hout_idle : c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) = c.output :=
      idle_tape_preserved hout_h hout_ns
    have hsc_ns : (c.work utmScratchTape).read ≠ Γ.start := by
      simp only [Tape.read, hsc_head]; exact hwf.2 utmScratchTape _ (by omega)
    let sc₁ : Tape := ⟨h, (c.work utmScratchTape).cells⟩
    let c₁ : Cfg 4 setupSimTM.Q :=
      { state := .rewindScratch, input := c.input,
        work := fun i => if i = utmScratchTape then sc₁ else c.work i,
        output := c.output }
    have hstep : setupSimTM.step c = some c₁ := by
      unfold TM.step
      simp only [hstate, show SetupSimPhase.rewindScratch ≠ SetupSimPhase.done from nofun,
        ↓reduceIte, setupSimTM, hsc_read_ne]
      congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
      funext i; by_cases hi : i = utmScratchTape
      · subst hi
        show (c.work utmScratchTape).writeAndMove _ Dir3.left = sc₁
        simp only [show (utmScratchTape : Fin 4).val = 3 from rfl, ↓reduceIte, sc₁]
        have hne_start : (c.work utmScratchTape).cells (h + 1) ≠ Γ.start :=
          hwf.2 utmScratchTape _ (by omega)
        simp only [Tape.writeAndMove, Tape.write, Tape.move, hsc_head,
          show h + 1 ≠ 0 from by omega, ↓reduceIte,
          init_tape_move_cells, show h + 1 - 1 = h from by omega, Tape.read]
        congr 1
        rw [show (c.work (3 : Fin 4)) = c.work utmScratchTape from rfl,
          init_readBackWrite_toΓ_eq hne_start, Function.update_eq_self]
      · show _ = (if i = utmScratchTape then sc₁ else c.work i)
        simp only [hi, ↓reduceIte]
        have hival : ¬((i : Fin 4).val = 3) := fun h => hi (Fin.ext h)
        simp only [hival, ↓reduceIte]; exact hwk_id i hi
    -- Apply IH
    have hih := ih c₁ rfl (by show sc₁.head = h; rfl)
      (by constructor
          · intro i; show (c₁.work i).cells 0 = Γ.start
            by_cases hi : i = utmScratchTape
            · simp only [c₁, hi, ↓reduceIte, sc₁]; exact hwf.1 utmScratchTape
            · simp only [c₁, hi, ↓reduceIte]; exact hwf.1 i
          · intro i j hj; show (c₁.work i).cells j ≠ Γ.start
            by_cases hi : i = utmScratchTape
            · simp only [c₁, hi, ↓reduceIte, sc₁]; exact hwf.2 utmScratchTape j hj
            · simp only [c₁, hi, ↓reduceIte]; exact hwf.2 i j hj)
      hinp_h hinp_ns hout_h hout_ns
      (fun i hi => by
        show (c₁.work i).head ≥ 1
        simp only [c₁, show i ≠ utmScratchTape from hi, ↓reduceIte]
        exact hwk_nonscratch i hi)
    obtain ⟨c', hreach_ih, hst', hsc_head', hsc_cells', hwk_other', hinp', hout', hwf', hwk_heads'⟩ := hih
    refine ⟨c', ?_, hst', hsc_head', ?_, ?_, hinp', hout', hwf', hwk_heads'⟩
    · have : h + 1 + 1 = 1 + (h + 1) := by omega
      rw [this]; exact reachesIn_trans setupSimTM (.step hstep .zero) hreach_ih
    · rw [hsc_cells']; show sc₁.cells = _; rfl
    · intro i hi; rw [hwk_other' i hi]
      show (if i = utmScratchTape then sc₁ else c.work i) = c.work i; simp [hi]

/-- Stride loop: from `.stride1` at scratch head 1+done, advance sim by 3*(n-done)+1 cells,
    reaching `.strideExtra2` in 3*(n-done)+1 steps. Scratch ends at head n+1.
    Sim and scratch cells are both preserved (readBackWrite writes). -/
private theorem stride_loop :
    ∀ (done : ℕ) (c : Cfg 4 setupSimTM.Q),
    done ≤ n →
    c.state = .stride1 →
    (c.work utmScratchTape).head = 1 + done →
    (∀ j, j > done → j ≤ n → (c.work utmScratchTape).cells j = Γ.one) →
    (c.work utmScratchTape).cells (n + 1) = Γ.blank →
    (c.work utmScratchTape).cells 0 = Γ.start →
    WorkTapesWF c.work →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    (∀ i : Fin 4, (c.work i).head ≥ 1) →
    ∃ c',
      setupSimTM.reachesIn (3 * (n - done) + 1) c c' ∧
      c'.state = .strideExtra2 ∧
      (c'.work utmSimTape).head = (c.work utmSimTape).head + 3 * (n - done) + 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c'.work utmScratchTape).head = n + 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmSimTape → i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work ∧
      (∀ i : Fin 4, (c'.work i).head ≥ 1) := by
  intro done
  induction h : n - done generalizing done with
  | zero =>
    intro c hdn hstate hsc_head hsc_ones hsc_sentinel hsc0 hwf
      hinp_h hinp_ns hout_h hout_ns hwk_heads
    have hdn_eq : done = n := by omega
    -- Scratch reads blank at position n+1
    have hsc_read_ne : ¬((fun i => (c.work i).read) (3 : Fin 4) = Γ.one) := by
      show (c.work utmScratchTape).read ≠ Γ.one
      simp only [Tape.read, hsc_head, hdn_eq, show 1 + n = n + 1 from by omega, hsc_sentinel]; decide
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
      idle_input_preserved hinp_h hinp_ns
    have hout_idle : c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) = c.output :=
      idle_tape_preserved hout_h hout_ns
    -- Simplified next config
    let sim' : Tape := ⟨(c.work utmSimTape).head + 1, (c.work utmSimTape).cells⟩
    let c' : Cfg 4 setupSimTM.Q := {
      state := .strideExtra2, input := c.input,
      work := fun i => if i = utmSimTape then sim' else c.work i,
      output := c.output }
    have hstep : setupSimTM.step c = some c' := by
      unfold TM.step
      simp only [hstate, show SetupSimPhase.stride1 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
        setupSimTM, hsc_read_ne, simAdvanceRight, simWriteRight]
      congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
      funext i; by_cases hi : i = utmSimTape
      · subst hi; simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte, c', sim']
        have hh := @writeAndMove_right_head (c.work utmSimTape) (readBackWrite (c.work utmSimTape).read)
        have hc := readBackWrite_cells (hwk_heads utmSimTape) (fun j hj => hwf.2 utmSimTape j hj)
          (d := Dir3.right)
        exact match (c.work utmSimTape).writeAndMove _ Dir3.right, hh, hc with
          | ⟨_, _⟩, rfl, rfl => rfl
      · have hival : ¬((i : Fin 4).val = 2) := fun heq => hi (Fin.ext heq)
        simp only [hival, ↓reduceIte, hi, c']
        exact idle_tape_preserved (hwk_heads i) (fun j hj => hwf.2 i j hj)
    refine ⟨c', .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · show sim'.head = _; simp only [sim']
    · show sim'.cells = _; rfl
    · show (c.work utmScratchTape).head = n + 1; rw [hsc_head, hdn_eq]; omega
    · show (c.work utmScratchTape).cells = _; rfl
    · intro i hi1 _; show (if i = utmSimTape then sim' else c.work i) = c.work i; simp [hi1]
    · constructor
      · intro i; show (c'.work i).cells 0 = Γ.start; simp only [c']
        split
        · simp only [sim']; exact hwf.1 utmSimTape
        · exact hwf.1 _
      · intro i j hj; show (c'.work i).cells j ≠ Γ.start; simp only [c']
        split
        · simp only [sim']; exact hwf.2 utmSimTape j hj
        · exact hwf.2 _ j hj
    · intro i; show (c'.work i).head ≥ 1; simp only [c']
      split
      · simp only [sim']; have := hwk_heads utmSimTape; omega
      · exact hwk_heads _
  | succ m ih =>
    intro c hdn hstate hsc_head hsc_ones hsc_sentinel hsc0 hwf
      hinp_h hinp_ns hout_h hout_ns hwk_heads
    have hlt : done < n := by omega
    -- Scratch reads one at position done+1
    have hsc_read_one : (fun i => (c.work i).read) (3 : Fin 4) = Γ.one := by
      show (c.work utmScratchTape).read = Γ.one
      simp only [Tape.read, hsc_head]; exact hsc_ones (1 + done) (by omega) (by omega)
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
      idle_input_preserved hinp_h hinp_ns
    have hout_idle : c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) = c.output :=
      idle_tape_preserved hout_h hout_ns
    -- readBackWrite preserves sim cells
    have hsim_rb : ∀ (t : Tape), t.cells = (c.work utmSimTape).cells → t.head ≥ 1 →
        (t.writeAndMove (readBackWrite t.read) Dir3.right).cells = (c.work utmSimTape).cells := by
      intro t htc hth
      rw [← htc]; exact readBackWrite_cells hth (fun j hj => htc ▸ hwf.2 utmSimTape j hj)
    -- Define c₃: config after 3 steps (stride1→stride2→stride3→stride1)
    -- Sim: head +3, cells preserved. Scratch: head +1, cells preserved. Rest: preserved.
    let c₃ : Cfg 4 setupSimTM.Q := {
      state := .stride1
      input := c.input
      work := fun i =>
        if i = utmSimTape then ⟨(c.work utmSimTape).head + 3, (c.work utmSimTape).cells⟩
        else if i = utmScratchTape then ⟨(c.work utmScratchTape).head + 1, (c.work utmScratchTape).cells⟩
        else c.work i
      output := c.output }
    -- ── 3-step reachesIn ──
    have hreach3 : setupSimTM.reachesIn 3 c c₃ := by
      -- Step 1: stride1(one) → stride2 via simAdvanceRight
      have hstep1 : setupSimTM.step c = some
          { state := SetupSimPhase.stride2
            input := c.input.move (idleDir c.input.read)
            work := fun i => (c.work i).writeAndMove
              ((if (i : Fin 4).val = 2 then readBackWrite (c.work utmSimTape).read
                else readBackWrite (c.work i).read) : Γw)
              (if (i : Fin 4).val = 2 then Dir3.right else idleDir (c.work i).read)
            output := c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) } := by
        unfold TM.step
        simp only [hstate, show SetupSimPhase.stride1 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
          setupSimTM, hsc_read_one, simAdvanceRight, simWriteRight]
      -- Simplify c₁: sim head +1, cells preserved, rest idle
      set sim₁ := (c.work utmSimTape).writeAndMove (readBackWrite (c.work utmSimTape).read) Dir3.right
      have hsim1_head : sim₁.head = (c.work utmSimTape).head + 1 := writeAndMove_right_head
      have hsim1_cells : sim₁.cells = (c.work utmSimTape).cells :=
        hsim_rb _ rfl (hwk_heads utmSimTape)
      -- Step 2: stride2 → stride3 via simAdvanceRight (on simplified c₁)
      have hstep2 : setupSimTM.step
          { state := SetupSimPhase.stride2, input := c.input,
            work := fun i => if i = utmSimTape then sim₁ else c.work i,
            output := c.output } = some
          { state := SetupSimPhase.stride3, input := c.input,
            work := fun i => if i = utmSimTape then
              ⟨(c.work utmSimTape).head + 2, (c.work utmSimTape).cells⟩ else c.work i,
            output := c.output } := by
        unfold TM.step
        simp only [show SetupSimPhase.stride2 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
          setupSimTM, simAdvanceRight, simWriteRight]
        congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
        funext i; by_cases hi : i = utmSimTape
        · subst hi
          simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte]
          have hhead : (sim₁.writeAndMove (readBackWrite sim₁.read) Dir3.right).head =
              (c.work utmSimTape).head + 2 := by
            rw [writeAndMove_right_head, hsim1_head]
          have hcells : (sim₁.writeAndMove (readBackWrite sim₁.read) Dir3.right).cells =
              (c.work utmSimTape).cells := hsim_rb sim₁ hsim1_cells (by omega)
          exact match sim₁.writeAndMove _ Dir3.right, hhead, hcells with
            | ⟨_, _⟩, rfl, rfl => rfl
        · have hival : ¬((i : Fin 4).val = 2) := fun heq => hi (Fin.ext heq)
          simp only [hival, ↓reduceIte, hi]
          exact idle_tape_preserved (hwk_heads i) (fun j hj => hwf.2 i j hj)
      -- Step 3: stride3 → stride1 (both sim and scratch advance right)
      set sim₂ : Tape := ⟨(c.work utmSimTape).head + 2, (c.work utmSimTape).cells⟩
      have hstep3 : setupSimTM.step
          { state := SetupSimPhase.stride3, input := c.input,
            work := fun i => if i = utmSimTape then sim₂ else c.work i,
            output := c.output } = some c₃ := by
        unfold TM.step
        simp only [show SetupSimPhase.stride3 ≠ SetupSimPhase.done from nofun, ↓reduceIte,
          setupSimTM]
        congr 1; refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
        funext i; by_cases hi2 : i = utmSimTape
        · -- Sim tape: readBackWrite + right
          subst hi2
          simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte,
            show ¬((2 : Fin 4) = utmScratchTape) from by decide, c₃]
          have hh : (sim₂.writeAndMove (readBackWrite sim₂.read) Dir3.right).head =
              (c.work utmSimTape).head + 3 := by rw [writeAndMove_right_head]
          have hc : (sim₂.writeAndMove (readBackWrite sim₂.read) Dir3.right).cells =
              (c.work utmSimTape).cells := hsim_rb sim₂ rfl (by simp only [sim₂]; have := hwk_heads utmSimTape; omega)
          exact match sim₂.writeAndMove _ Dir3.right, hh, hc with
            | ⟨_, _⟩, rfl, rfl => rfl
        · by_cases hi3 : i = utmScratchTape
          · -- Scratch tape: readBackWrite + right
            subst hi3
            simp only [show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte,
              show (utmScratchTape : Fin 4).val = 3 from rfl,
              show ¬((3 : Nat) = 2) from by decide, c₃]
            have hhead : ((c.work utmScratchTape).writeAndMove
                (readBackWrite (c.work utmScratchTape).read) Dir3.right).head =
                (c.work utmScratchTape).head + 1 := writeAndMove_right_head
            have hcells : ((c.work utmScratchTape).writeAndMove
                (readBackWrite (c.work utmScratchTape).read) Dir3.right).cells =
                (c.work utmScratchTape).cells :=
              readBackWrite_cells (hwk_heads utmScratchTape)
                (fun j hj => hwf.2 utmScratchTape j hj)
            exact match (c.work utmScratchTape).writeAndMove _ Dir3.right, hhead, hcells with
              | ⟨_, _⟩, rfl, rfl => rfl
          · -- Other tapes: idle
            have hival2 : ¬((i : Fin 4).val = 2) := fun heq => hi2 (Fin.ext heq)
            have hival3 : ¬((i : Fin 4).val = 3) := fun heq => hi3 (Fin.ext heq)
            simp only [hi2, hi3, ↓reduceIte, hival2, hival3, c₃]
            exact idle_tape_preserved (hwk_heads i) (fun j hj => hwf.2 i j hj)
      -- Need step 1 result = simplified form for chaining step 2
      have hstep1_simp : setupSimTM.step c = some
          { state := SetupSimPhase.stride2, input := c.input,
            work := fun i => if i = utmSimTape then sim₁ else c.work i,
            output := c.output } := by
        rw [hstep1]; congr 1
        refine Cfg.mk.injEq .. |>.mpr ⟨rfl, hinp_idle, ?_, hout_idle⟩
        funext i; by_cases hi : i = utmSimTape
        · subst hi; simp only [utmSimTape, show (2 : Fin 4).val = 2 from rfl, ↓reduceIte, sim₁]
        · have hival : ¬((i : Fin 4).val = 2) := fun heq => hi (Fin.ext heq)
          simp only [hival, ↓reduceIte, hi]
          exact idle_tape_preserved (hwk_heads i) (fun j hj => hwf.2 i j hj)
      exact .step hstep1_simp (.step hstep2 (.step hstep3 .zero))
    -- Apply IH
    have hih := ih (done + 1) (by omega) c₃ (by omega)
      (by show c₃.state = .stride1; rfl)
      (by show (c₃.work utmScratchTape).head = 1 + (done + 1)
          simp only [c₃, show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte, hsc_head]
          omega)
      (by intro j hj hjn; show (c₃.work utmScratchTape).cells j = Γ.one
          simp only [c₃, show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
          exact hsc_ones j (by omega) hjn)
      (by show (c₃.work utmScratchTape).cells (n + 1) = Γ.blank
          simp only [c₃, show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
          exact hsc_sentinel)
      (by show (c₃.work utmScratchTape).cells 0 = Γ.start
          simp only [c₃, show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
          exact hsc0)
      (by constructor
          · intro i; show (c₃.work i).cells 0 = Γ.start; simp only [c₃]
            by_cases h2 : i = utmSimTape
            · simp [h2]; exact hwf.1 utmSimTape
            · by_cases h3 : i = utmScratchTape
              · simp [h2, h3]; exact hwf.1 utmScratchTape
              · simp [h2, h3]; exact hwf.1 i
          · intro i j hj; show (c₃.work i).cells j ≠ Γ.start; simp only [c₃]
            by_cases h2 : i = utmSimTape
            · simp [h2]; exact hwf.2 utmSimTape j hj
            · by_cases h3 : i = utmScratchTape
              · simp [h2, h3]; exact hwf.2 utmScratchTape j hj
              · simp [h2, h3]; exact hwf.2 i j hj)
      hinp_h hinp_ns hout_h hout_ns
      (by intro i; show (c₃.work i).head ≥ 1
          simp only [c₃]; split
          · simp only []; have := hwk_heads utmSimTape; omega
          · split
            · simp only []; have := hwk_heads utmScratchTape; omega
            · exact hwk_heads i)
    obtain ⟨c', hreach_ih, hst', hsim_h', hsim_c', hsc_h', hsc_c', hwk_other', hinp', hout', hwf', hwk_heads'⟩ := hih
    refine ⟨c', ?_, hst', ?_, ?_, hsc_h', ?_, ?_, hinp', hout', hwf', hwk_heads'⟩
    · -- reachesIn composition
      have : 3 * (m + 1) + 1 = 3 + (3 * m + 1) := by omega
      rw [this]; exact reachesIn_trans setupSimTM hreach3 hreach_ih
    · -- sim head
      rw [hsim_h']; show (c₃.work utmSimTape).head + 3 * m + 1 = _
      simp only [c₃, ↓reduceIte]; omega
    · -- sim cells
      rw [hsim_c']; show (c₃.work utmSimTape).cells = _
      simp only [c₃, ↓reduceIte]
    · -- scratch cells
      rw [hsc_c']; show (c₃.work utmScratchTape).cells = _
      simp only [c₃, show utmScratchTape ≠ utmSimTape from by decide, ↓reduceIte]
    · -- other tapes
      intro i hi1 hi2
      rw [hwk_other' i hi1 hi2]; show c₃.work i = c.work i
      simp only [c₃, hi1, hi2, ↓reduceIte]

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
  -- Generalized induction with processed counter.
  -- We add explicit p < x.length bounds so that by omega inside the type works.
  suffices h_gen : ∀ (processed : ℕ) (xs : List Bool) (c : Cfg 4 setupSimTM.Q)
      (hlen_g : processed + xs.length = x.length)
      (hple_g : processed ≤ x.length),
      c.state = .checkInput →
      (c.work utmSimTape).cells 0 = Γ.start →
      (c.work utmSimTape).head = 1 + (processed + 1) * (3 * (n + 2)) →
      (∀ j, j ≥ 1 → j ≤ 3 * (n + 2) → (c.work utmSimTape).cells j = Γ.one) →
      (∀ j, j > (processed + 1) * (3 * (n + 2)) → (c.work utmSimTape).cells j = Γ.blank) →
      (∀ (p : ℕ) (_hp1 : p ≥ 1) (_hp2 : p ≤ processed),
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0) = Γ.blank ∧
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 1) = Γ.zero ∧
        (c.work utmSimTape).cells (SuperCell.simTapeOffset (n + 2) p 0 + 2) =
          Γ.ofBool (x.get ⟨p - 1, by omega⟩)) →
      (∀ (tapeIdx pos : ℕ),
        pos ≥ 1 → pos ≤ processed →
        tapeIdx ≥ 1 → tapeIdx < n + 2 →
        ∀ off, off < 3 →
          (c.work utmSimTape).cells
            (SuperCell.simTapeOffset (n + 2) pos tapeIdx + off) = Γ.blank) →
      (∀ j, j ≥ 1 → j ≤ n → (c.work utmScratchTape).cells j = Γ.one) →
      (c.work utmScratchTape).cells (n + 1) = Γ.blank →
      (c.work utmScratchTape).cells 0 = Γ.start →
      (c.work utmScratchTape).head = n + 1 →
      c.input.head ≥ 1 →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ (i : ℕ) (hi : i < xs.length),
        c.input.cells (c.input.head + i) = Γ.ofBool (xs.get ⟨i, hi⟩)) →
      c.input.cells (c.input.head + xs.length) = Γ.blank →
      (∀ (i : ℕ) (hi : i < xs.length), xs.get ⟨i, hi⟩ = x.get ⟨processed + i, by omega⟩) →
      c.output.head ≥ 1 →
      (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      WorkTapesWF c.work →
      (c.work utmDescTape).head ≥ 1 →
      (c.work utmStateTape).head ≥ 1 →
      ∃ c',
        setupSimTM.reachesIn (xs.length * (4 * n + 9) + 1) c c' ∧
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
        (∀ i, (c'.work i).head ≥ 1) by
    exact h_gen 0 x c (by omega) (by omega)
      hstate hsim0
      (by convert hsim_head using 2; omega)
      hpos0_ones
      (by intro j hj; exact hsim_rest j (by omega))
      (by intro p _ hp2; omega)
      (by intro _ pos _ hp2; omega)
      hsc_ones hsc_blank hsc0 hsc_head
      hinp_h hinp_ns hinp_x hinp_end
      (by intro i hi; simp)
      hout_h hout_ns hwf hdesc_h hst_h
  -- Proof of h_gen by induction on xs
  intro processed xs
  induction xs generalizing processed with
  | nil =>
    intro c hlen hproc_le hstate' hsim0' hsim_head' hones' hsim_rest'
      hinput_written hblank_written hsc_ones' hsc_blank' hsc0' hsc_head'
      hinp_h' hinp_ns' hinp_xs' hinp_end' hxs_eq hout_h' hout_ns' hwf' hdesc_h' hst_h'
    have hproc : processed = x.length := by simp at hlen; exact hlen
    -- Input reads blank
    have hinp_blank : c.input.read = Γ.blank := by
      simp only [Tape.read]; simpa using hinp_end'
    have hinp_idle : c.input.move (idleDir c.input.read) = c.input :=
      idle_input_preserved hinp_h' hinp_ns'
    have hout_idle : c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read) = c.output :=
      idle_tape_preserved hout_h' hout_ns'
    have hwk_heads : ∀ i : Fin 4, (c.work i).head ≥ 1 := fun
      | ⟨0, _⟩ => hdesc_h' | ⟨1, _⟩ => hst_h'
      | ⟨2, _⟩ => by show (c.work utmSimTape).head ≥ 1; omega
      | ⟨3, _⟩ => by show (c.work utmScratchTape).head ≥ 1; rw [hsc_head']; omega
    -- checkInput with blank → setupIdle .done → all tapes preserved
    let c' : Cfg 4 setupSimTM.Q :=
      { state := .done, input := c.input, work := c.work, output := c.output }
    have hstep : setupSimTM.step c = some c' := by
      simp only [TM.step, hstate', setupSimTM, hinp_blank, setupIdle, c',
        show SetupSimPhase.checkInput ≠ SetupSimPhase.done from nofun, ↓reduceIte,
        hinp_idle, hout_idle]
      congr 1
      refine Cfg.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_, rfl⟩
      funext i; exact idle_tape_preserved (hwk_heads i) (fun j hj => hwf'.2 i j hj)
    have hreach : setupSimTM.reachesIn (([] : List Bool).length * (4 * n + 9) + 1) c c' := by
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]; exact .step hstep .zero
    exact ⟨c', hreach,
      show c'.state = setupSimTM.qhalt from rfl,
      hsim0', hones',
      fun p hp hp2 => hinput_written p hp (by omega),
      (by intro numTapes tapeIdx pos hpos htape hnt hor off hoff; subst hnt
          rcases hor with htgt0 | hpgt
          · by_cases hple : pos ≤ processed
            · exact hblank_written tapeIdx pos (by omega) hple (by omega) htape off hoff
            · apply hsim_rest'
              have := Nat.mul_le_mul_right (3 * (n + 2)) (show processed + 1 ≤ pos from by omega)
              simp only [SuperCell.simTapeOffset, SuperCell.width]; omega
          · apply hsim_rest'
            have := Nat.mul_le_mul_right (3 * (n + 2)) (show processed + 1 ≤ pos from by omega)
            simp only [SuperCell.simTapeOffset, SuperCell.width]; omega),
      rfl, rfl, hwf', hwk_heads⟩
  | cons b rest ih =>
    intro c hlen hproc_le hstate' hsim0' hsim_head' hones' hsim_rest'
      hinput_written hblank_written hsc_ones' hsc_blank' hsc0' hsc_head'
      hinp_h' hinp_ns' hinp_xs' hinp_end' hxs_eq hout_h' hout_ns' hwf' hdesc_h' hst_h'
    -- Apply IH with processed+1 and rest
    -- First we need to show the one-bit cycle (4n+9 steps) produces a config
    -- satisfying the IH preconditions, then compose.
    -- For now, sorry — this requires ~250 lines of step-tracing.
    -- The cycle: checkInput→writeSymHi→writeSymLo→rewindScratch(n+2)→bounce(1)→stride(3n+1)→extra(2)
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
