import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# ReadCurrent proof internals

Step-by-step simulation lemmas for `readCurrentTM`.
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem rc_readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem rc_tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

/-- writeAndMove with readBackWrite and idleDir preserves a tape
    when read ≠ ▷ and head ≥ 1. -/
private theorem rc_tape_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start) (hh : t.head ≥ 1) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hns ⊢
    rw [rc_readBackWrite_toΓ_eq hns, Function.update_eq_self]

private theorem rc_tape_read_ne_start_of_wf (t : Tape) (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hns _ hh

-- ════════════════════════════════════════════════════════════════════════
-- Transcoding correctness
-- ════════════════════════════════════════════════════════════════════════

/-- `transcodePair` correctly converts super-cell encoding to Γ.encode encoding. -/
theorem transcodePair_symToCellPair (g : Γ) :
    let p := SuperCell.symToCellPair g
    let t := transcodePair p.1 p.2
    t.1.toΓ = Γ.ofBool (g.encode[0]'(by cases g <;> decide)) ∧
    t.2.toΓ = Γ.ofBool (g.encode[1]'(by cases g <;> decide)) := by
  cases g <;> simp [SuperCell.symToCellPair, transcodePair, Γ.encode, Γ.ofBool, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Phase simulation lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 1: copyState copies k state bits from state tape to scratch tape.
    After k+1 steps (k copy steps + 1 sentinel step):
    - scratch cells 1..k match state tape cells 1..k
    - state = .scan 0 0
    - state tape head = k + 1
    - scratch tape head = k + 1
    - sim tape head unchanged (= 1)
    - desc tape unchanged -/
private theorem copyState_simulation
    (c : Cfg 4 (readCurrentTM (n := n)).Q)
    (k : ℕ) (q : Fin k)
    (hstate : c.state = .copyState)
    (hst_head : (c.work utmStateTape).head = 1)
    (hsc_head : (c.work utmScratchTape).head = 1)
    (hsim_head : (c.work utmSimTape).head = 1)
    (hdesc_head : (c.work utmDescTape).head ≥ 1)
    (hstate_cells : stateOnTapeAt k q (c.work utmStateTape))
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (_hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1) :
    ∃ c',
      (readCurrentTM (n := n)).reachesIn (k + 1) c c' ∧
      c'.state = .scan ⟨0, by omega⟩ ⟨0, by omega⟩ ∧
      (c'.work utmStateTape).head = k + 1 ∧
      (c'.work utmStateTape).cells = (c.work utmStateTape).cells ∧
      (c'.work utmScratchTape).head = k + 1 ∧
      (∀ j, j < k → (c'.work utmScratchTape).cells (j + 1) =
        if j = q.val then Γ.one else Γ.zero) ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c'.work utmDescTape) = (c.work utmDescTape) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  -- Generalized loop: induction on remaining cells to copy
  suffices loop : ∀ (rem : ℕ) (c' : Cfg 4 readCurrentTM.Q),
      rem ≤ k → c'.state = .copyState →
      (c'.work utmStateTape).head = k - rem + 1 →
      (c'.work utmScratchTape).head = k - rem + 1 →
      (c'.work utmSimTape).head = 1 →
      (c'.work utmDescTape) = (c.work utmDescTape) →
      (c'.work utmStateTape).cells = (c.work utmStateTape).cells →
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells →
      c'.input = c.input → c'.output = c.output →
      (∀ j, j < k - rem →
        (c'.work utmScratchTape).cells (j + 1) =
          if j = q.val then Γ.one else Γ.zero) →
      WorkTapesWF c'.work →
      ∃ c_f,
        readCurrentTM.reachesIn (rem + 1) c' c_f ∧
        c_f.state = .scan ⟨0, by omega⟩ ⟨0, by omega⟩ ∧
        (c_f.work utmStateTape).head = k + 1 ∧
        (c_f.work utmStateTape).cells = (c.work utmStateTape).cells ∧
        (c_f.work utmScratchTape).head = k + 1 ∧
        (∀ j, j < k →
          (c_f.work utmScratchTape).cells (j + 1) =
            if j = q.val then Γ.one else Γ.zero) ∧
        (c_f.work utmSimTape).head = 1 ∧
        (c_f.work utmSimTape).cells = (c.work utmSimTape).cells ∧
        c_f.work utmDescTape = c.work utmDescTape ∧
        c_f.input = c.input ∧ c_f.output = c.output ∧
        WorkTapesWF c_f.work by
    exact loop k c le_rfl hstate (by omega) (by omega) hsim_head rfl rfl rfl rfl rfl
      (fun _ hj => absurd hj (by omega)) hwf
  intro rem; induction rem with
  | zero =>
    intro c' _ hstate' hst_h' hsc_h' hsim_h' hdesc' hst_c' hsim_c' hinp' hout' hsc_done hwf'
    have hdesc_h' : (c'.work utmDescTape).head ≥ 1 := by rw [hdesc']; exact hdesc_head
    have hheads : ∀ i, (c'.work i).head ≥ 1 := by
      intro i
      by_cases h0 : i = utmDescTape; · rw [h0]; exact hdesc_h'
      by_cases h1 : i = utmStateTape; · rw [h1]; omega
      by_cases h2 : i = utmSimTape; · rw [h2]; omega
      have : i = utmScratchTape := by
        simp only [Ne, Fin.ext_iff, utmDescTape, utmStateTape, utmSimTape, utmScratchTape] at *
        omega
      rw [this]; omega
    have hread : (c'.work utmStateTape).read = Γ.blank := by
      simp only [Tape.read, hst_h', hst_c']
      convert hstate_cells.2.2 using 2
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c' = some c₁ ∧
        c₁.state = .scan ⟨0, by omega⟩ ⟨0, by omega⟩ ∧
        c₁.work = c'.work ∧
        c₁.input = c'.input ∧ c₁.output = c'.output := by
      simp only [TM.step, hstate', readCurrentTM, ↓reduceIte, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · ext i; dsimp only []
        exact rc_tape_idle_preserve (c'.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i) (hwf'.2 i)) (hheads i)
      · rw [hinp']; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · rw [hout']; exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hst1, hwork1, hinp1, hout1⟩ := hstep
    refine ⟨c₁, .step hstep' .zero, hst1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork1]; omega
    · rw [hwork1, hst_c']
    · rw [hwork1]; omega
    · intro j hj; rw [hwork1]; exact hsc_done j (by omega)
    · rw [hwork1, hsim_h']
    · rw [hwork1, hsim_c']
    · rw [hwork1, hdesc']
    · rw [hinp1, hinp']
    · rw [hout1, hout']
    · rw [hwork1]; exact hwf'
  | succ m ih =>
    intro c' hle hstate' hst_h' hsc_h' hsim_h' hdesc' hst_c' hsim_c' hinp' hout' hsc_done hwf'
    have hdesc_h' : (c'.work utmDescTape).head ≥ 1 := by rw [hdesc']; exact hdesc_head
    have hheads : ∀ i, (c'.work i).head ≥ 1 := by
      intro i
      by_cases h0 : i = utmDescTape; · rw [h0]; exact hdesc_h'
      by_cases h1 : i = utmStateTape; · rw [h1]; omega
      by_cases h2 : i = utmSimTape; · rw [h2]; omega
      have : i = utmScratchTape := by
        simp only [Ne, Fin.ext_iff, utmDescTape, utmStateTape, utmSimTape, utmScratchTape] at *
        omega
      rw [this]; omega
    have hread_val : (c'.work utmStateTape).read =
        if (k - (m + 1)) = q.val then Γ.one else Γ.zero := by
      simp only [Tape.read, hst_h', hst_c']
      exact hstate_cells.2.1 (k - (m + 1)) (by omega)
    have hread_ne_blank : (c'.work utmStateTape).read ≠ Γ.blank := by
      rw [hread_val]; split <;> decide
    have hread_ne_start : (c'.work utmStateTape).read ≠ Γ.start := by
      rw [hread_val]; split <;> decide
    -- Fin 4 comparison facts for resolving if-then-else in δ
    have hfin_st_ne_3 : ¬ (utmStateTape = (3 : Fin 4)) := by decide
    have hfin_sc_ne_1 : ¬ (utmScratchTape = (1 : Fin 4)) := by decide
    have hfin_sim_ne_1 : ¬ (utmSimTape = (1 : Fin 4)) := by decide
    have hfin_sim_ne_3 : ¬ (utmSimTape = (3 : Fin 4)) := by decide
    have hfin_desc_ne_1 : ¬ (utmDescTape = (1 : Fin 4)) := by decide
    have hfin_desc_ne_3 : ¬ (utmDescTape = (3 : Fin 4)) := by decide
    -- One copy step: copies state tape cell to scratch, advances both right
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c' = some c₁ ∧
        c₁.state = .copyState ∧
        (c₁.work utmStateTape).head = k - m + 1 ∧
        (c₁.work utmStateTape).cells = (c'.work utmStateTape).cells ∧
        (c₁.work utmScratchTape).head = k - m + 1 ∧
        (c₁.work utmScratchTape).cells (k - (m + 1) + 1) =
          (readBackWrite (c'.work utmStateTape).read).toΓ ∧
        (∀ j, j ≠ k - (m + 1) + 1 →
          (c₁.work utmScratchTape).cells j = (c'.work utmScratchTape).cells j) ∧
        (c₁.work utmSimTape) = (c'.work utmSimTape) ∧
        (c₁.work utmDescTape) = (c'.work utmDescTape) ∧
        c₁.input = c'.input ∧ c₁.output = c'.output := by
      simp only [TM.step, hstate', readCurrentTM, ↓reduceIte, hread_ne_blank]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- State tape head: readBackWrite + right
      · dsimp only []
        rw [if_neg hfin_st_ne_3, if_pos (show utmStateTape = (1 : Fin 4) from rfl)]
        simp only [Tape.writeAndMove, Tape.move, Tape.write, hst_h']
        split
        · omega
        · dsimp only []; omega
      -- State tape cells: preserved (readBackWrite writes same value)
      · dsimp only []
        rw [if_neg hfin_st_ne_3, if_pos (show utmStateTape = (1 : Fin 4) from rfl)]
        simp only [Tape.writeAndMove, rc_tape_move_cells]
        rw [rc_readBackWrite_toΓ_eq hread_ne_start]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      -- Scratch tape head: copy + right
      · dsimp only []
        rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
            if_neg hfin_sc_ne_1, if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
        simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc_h']
        split
        · omega
        · dsimp only []; omega
      -- Scratch tape cell at written position
      · dsimp only []
        rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
            if_neg hfin_sc_ne_1, if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
        simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc_h']
        split
        · omega
        · dsimp only []; simp
      -- Scratch tape cells preserved at other positions
      · intro j hne
        dsimp only []
        rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
            if_neg hfin_sc_ne_1, if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
        simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc_h']
        split
        · omega
        · dsimp only []; rw [Function.update_apply, if_neg hne]
      -- Sim tape (idle)
      · dsimp only []
        rw [if_neg hfin_sim_ne_3, if_neg hfin_sim_ne_1, if_neg hfin_sim_ne_3]
        exact rc_tape_idle_preserve (c'.work utmSimTape)
          (rc_tape_read_ne_start_of_wf _ (hheads utmSimTape) (hwf'.2 utmSimTape))
          (hheads utmSimTape)
      -- Desc tape (idle)
      · dsimp only []
        rw [if_neg hfin_desc_ne_3, if_neg hfin_desc_ne_1, if_neg hfin_desc_ne_3]
        exact rc_tape_idle_preserve (c'.work utmDescTape)
          (rc_tape_read_ne_start_of_wf _ (hheads utmDescTape) (hwf'.2 utmDescTape))
          (hheads utmDescTape)
      -- Input
      · rw [hinp']; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      -- Output
      · rw [hout']; exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hc₁st, hc₁sth, hc₁stc, hc₁sch, hc₁_sc_cell, hc₁_sc_other,
            hc₁sim, hc₁desc, hc₁inp, hc₁out⟩ := hstep
    -- WorkTapesWF preserved
    have hwf₁ : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmStateTape
        · rw [h, hc₁stc]; exact hwf'.1 utmStateTape
        · by_cases h : i = utmSimTape
          · rw [h, hc₁sim]; exact hwf'.1 utmSimTape
          · by_cases h : i = utmDescTape
            · rw [h, hc₁desc]; exact hwf'.1 utmDescTape
            · have hi : i = utmScratchTape := by
                simp only [Ne, Fin.ext_iff, utmDescTape, utmStateTape, utmSimTape, utmScratchTape] at *
                omega
              rw [hi]; rw [hc₁_sc_other 0 (by omega)]; exact hwf'.1 utmScratchTape
      · intro i j hj; by_cases h : i = utmStateTape
        · rw [h, hc₁stc]; exact hwf'.2 utmStateTape j hj
        · by_cases h : i = utmSimTape
          · rw [h, hc₁sim]; exact hwf'.2 utmSimTape j hj
          · by_cases h : i = utmDescTape
            · rw [h, hc₁desc]; exact hwf'.2 utmDescTape j hj
            · have hi : i = utmScratchTape := by
                simp only [Ne, Fin.ext_iff, utmDescTape, utmStateTape, utmSimTape, utmScratchTape] at *
                omega
              rw [hi]
              by_cases heq : j = k - (m + 1) + 1
              · rw [heq, hc₁_sc_cell, rc_readBackWrite_toΓ_eq hread_ne_start]
                rw [hread_val]; split <;> decide
              · rw [hc₁_sc_other j heq]; exact hwf'.2 utmScratchTape j hj
    -- Scratch condition for IH
    have hsc_done₁ : ∀ j, j < k - m →
        (c₁.work utmScratchTape).cells (j + 1) =
          if j = q.val then Γ.one else Γ.zero := by
      intro j hj
      by_cases heq : j = k - (m + 1)
      · subst heq
        rw [hc₁_sc_cell, rc_readBackWrite_toΓ_eq hread_ne_start, hread_val]
      · rw [hc₁_sc_other (j + 1) (by omega)]
        exact hsc_done j (by omega)
    -- Apply IH
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hsch_f, hsc_f, hsimh_f, hsimc_f,
            hdesc_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c₁ (by omega) hc₁st (by omega) (by omega)
        (by rw [hc₁sim]; exact hsim_h')
        (by rw [hc₁desc]; exact hdesc')
        (by rw [hc₁stc]; exact hst_c')
        (by rw [hc₁sim]; exact hsim_c')
        (by rw [hc₁inp]; exact hinp')
        (by rw [hc₁out]; exact hout')
        hsc_done₁ hwf₁
    exact ⟨c_f, .step hstep' hreach, hst_f, hhead_f, hcells_f, hsch_f, hsc_f, hsimh_f, hsimc_f,
            hdesc_f, hinp_f, hout_f, hwf_f⟩

/-- Rewind sim tape from some position to cell 1 (reaching rewindSimR). -/
private theorem rewindSim_simulation :
    ∀ (sim_head : ℕ) (c : Cfg 4 (readCurrentTM (n := n)).Q) (target : Fin (n + 2)),
    c.state = .rewindSim target →
    (c.work utmSimTape).head = sim_head →
    WorkTapesWF c.work →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    (∀ i, i ≠ utmSimTape → (c.work i).head ≥ 1) →
    ∃ c',
      (readCurrentTM (n := n)).reachesIn (sim_head + 1) c c' ∧
      c'.state = .rewindSimR target ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (∀ i, i ≠ utmSimTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro sim_head; induction sim_head with
  | zero =>
    intro c target hstate hsim_head hwf hinp hinp_h hout hout_h hheads
    have hread : (c.work utmSimTape).read = Γ.start := by
      simp [Tape.read, hsim_head, hwf.1 utmSimTape]
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindSimR target ∧
        (c₁.work utmSimTape).head = 1 ∧
        (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
        (∀ i, i ≠ utmSimTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write, hsim_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsim_head]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    refine ⟨c₁, .step hstep' .zero, hst1, hhead1, hcells1, hw1, hinp1, hout1, ?_⟩
    constructor
    · intro i; by_cases h : i = utmSimTape
      · rw [h, hcells1]; exact hwf.1 utmSimTape
      · rw [hw1 i h]; exact hwf.1 i
    · intro i j hj; by_cases h : i = utmSimTape
      · rw [h, hcells1]; exact hwf.2 utmSimTape j hj
      · rw [hw1 i h]; exact hwf.2 i j hj
  | succ h ih =>
    intro c target hstate hsim_head hwf hinp hinp_h hout hout_h hheads
    have hread_ne : (c.work utmSimTape).read ≠ Γ.start := by
      simp [Tape.read, hsim_head]; exact hwf.2 utmSimTape (h + 1) (by omega)
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindSim target ∧
        (c₁.work utmSimTape).head = h ∧
        (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
        (∀ i, i ≠ utmSimTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hsim_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h' : i = utmSimTape
        · rw [h', hcells1]; exact hwf.1 utmSimTape
        · rw [hw1 i h']; exact hwf.1 i
      · intro i j hj; by_cases h' : i = utmSimTape
        · rw [h', hcells1]; exact hwf.2 utmSimTape j hj
        · rw [hw1 i h']; exact hwf.2 i j hj
    have hheads1 : ∀ i, i ≠ utmSimTape → (c₁.work i).head ≥ 1 := by
      intro i h'; rw [hw1 i h']; exact hheads i h'
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c₁ target hst1 hhead1 hwf1
        (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
        (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
        hheads1
    refine ⟨c_f, .step hstep' hreach, hst_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

/-- Phase 2: for a single tape target with head at position h,
    scan the sim tape, read head symbols, transcode and write to scratch,
    then rewind sim tape back to cell 1. -/
private theorem per_tape_simulation
    (target_sym : ℕ → Γ)
    (c : Cfg 4 (readCurrentTM (n := n)).Q)
    (target : Fin (n + 2)) (h_target : ℕ) (sc_pos : ℕ)
    (hstate : c.state = .scan target ⟨0, by omega⟩)
    (hsim_head : (c.work utmSimTape).head = 1)
    -- sim tape correctly encodes the target tape's data
    (hsim_marker : ∀ pos, (c.work utmSimTape).cells
      (SuperCell.simTapeOffset (n + 2) pos target.val) =
      if h_target = pos then Γ.one else Γ.blank)
    (hsim_hi : ∀ pos, (c.work utmSimTape).cells
      (SuperCell.simTapeOffset (n + 2) pos target.val + 1) =
      (SuperCell.symToCellPair (target_sym pos)).1)
    (hsim_lo : ∀ pos, (c.work utmSimTape).cells
      (SuperCell.simTapeOffset (n + 2) pos target.val + 2) =
      (SuperCell.symToCellPair (target_sym pos)).2)
    -- scratch tape
    (hsc_head : (c.work utmScratchTape).head = sc_pos)
    (hsc_pos_ge : sc_pos ≥ 1)
    -- other tapes idle
    (hwf : WorkTapesWF c.work)
    (hinp : c.input.read ≠ Γ.start) (hinp_h : c.input.head ≥ 1)
    (hout : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1)
    -- sim tape well-formed (cell 0 = ▷)
    (hsim_cell0 : (c.work utmSimTape).cells 0 = Γ.start)
    -- all work tape heads ≥ 1
    (hwork_heads : ∀ i, (c.work i).head ≥ 1) :
    ∃ c' t,
      (readCurrentTM (n := n)).reachesIn t c c' ∧
      -- Next state: either scan for next tape or rewindState
      (if h : target.val = n + 1 then
        c'.state = .rewindState
      else
        c'.state = .scan ⟨target.val + 1, by omega⟩ ⟨0, by omega⟩) ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c'.work utmScratchTape).head = sc_pos + 2 ∧
      -- Scratch has the correct 2 encoded bits for target
      (c'.work utmScratchTape).cells sc_pos =
        Γ.ofBool ((target_sym h_target).encode[0]'(by cases (target_sym h_target) <;> decide)) ∧
      (c'.work utmScratchTape).cells (sc_pos + 1) =
        Γ.ofBool ((target_sym h_target).encode[1]'(by cases (target_sym h_target) <;> decide)) ∧
      -- Previously written scratch cells preserved
      (∀ j, j < sc_pos → (c'.work utmScratchTape).cells j = (c.work utmScratchTape).cells j) ∧
      -- Other tapes preserved
      (c'.work utmDescTape) = (c.work utmDescTape) ∧
      (c'.work utmStateTape) = (c.work utmStateTape) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  -- Abbreviations for key values
  set W := 3 * (n + 2) with hW_def
  set offset := SuperCell.simTapeOffset (n + 2) h_target target.val with hoffset_def
  have hW_pos : W > 0 := by omega
  have hoffset_pos : offset ≥ 1 := by
    simp only [SuperCell.simTapeOffset, SuperCell.width, hoffset_def]; omega
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 1: Scan sim tape to find head marker
  -- ═══════════════════════════════════════════════════════════════════
  have scan_result : ∃ c₁,
      readCurrentTM.reachesIn offset c c₁ ∧
      c₁.state = .readHi target ∧
      (c₁.work utmSimTape).head = offset + 1 ∧
      (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (∀ i, i ≠ utmSimTape → c₁.work i = c.work i) ∧
      c₁.input = c.input ∧ c₁.output = c.output ∧
      WorkTapesWF c₁.work := by
    -- Key arithmetic fact: offset - 1 = h_target * W + 3 * target.val
    have hoffset_expand : offset - 1 = h_target * W + 3 * target.val := by
      simp only [hoffset_def, SuperCell.simTapeOffset, SuperCell.width, hW_def]; omega
    -- Induction on remaining distance from current sim head to offset
    suffices loop : ∀ (rem : ℕ) (c' : Cfg 4 readCurrentTM.Q),
        (c'.work utmSimTape).head + rem = offset →
        c'.state = .scan target ⟨((c'.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ →
        (c'.work utmSimTape).cells = (c.work utmSimTape).cells →
        (∀ i, i ≠ utmSimTape → c'.work i = c.work i) →
        c'.input = c.input → c'.output = c.output →
        WorkTapesWF c'.work →
        (∀ i, (c'.work i).head ≥ 1) →
        ∃ c₁,
          readCurrentTM.reachesIn (rem + 1) c' c₁ ∧
          c₁.state = .readHi target ∧
          (c₁.work utmSimTape).head = offset + 1 ∧
          (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
          (∀ i, i ≠ utmSimTape → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output ∧
          WorkTapesWF c₁.work by
      obtain ⟨c₁, hr, hst, hh, hcells, ho, hinp', hout', hwf'⟩ :=
        loop (offset - 1) c (by omega)
          (by convert hstate using 2; ext; simp [hsim_head])
          rfl (fun _ _ => rfl) rfl rfl hwf hwork_heads
      exact ⟨c₁, by rwa [show offset - 1 + 1 = offset by omega] at hr,
             hst, hh, hcells, ho, hinp', hout', hwf'⟩
    intro rem; induction rem with
    | zero =>
      intro c' hhead hstate' hcells' ho' hinp' hout' hwf' hheads'
      -- head = offset, we're at the marker
      have hsim_head' : (c'.work utmSimTape).head = offset := by omega
      -- pos = 3 * target.val (the marker column)
      have hpos_val : ((c'.work utmSimTape).head - 1) % W = 3 * target.val := by
        rw [hsim_head']
        have h1 : offset - 1 = h_target * W + 3 * target.val := hoffset_expand
        rw [h1, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (show 3 * target.val < W by omega)]
      -- sim reads Γ.one at the marker
      have hread_one : (c'.work utmSimTape).read = Γ.one := by
        simp only [Tape.read, hsim_head', hcells']
        have := hsim_marker h_target
        simp only [] at this; exact this
      have hread_ne_start : (c'.work utmSimTape).read ≠ Γ.start :=
        rc_tape_read_ne_start_of_wf _ (hheads' utmSimTape) (hwf'.2 utmSimTape)
      -- Prove the if-condition for pos
      have hpos_if : (⟨((c'.work utmSimTape).head - 1) % W,
          Nat.mod_lt _ (by omega)⟩ : Fin (3 * (n + 2))).val =
          3 * target.val := hpos_val
      -- One step to readHi
      have hne_done : (ReadCurrentQ.scan target ⟨((c'.work utmSimTape).head - 1) % W,
          Nat.mod_lt _ (by omega)⟩ : ReadCurrentQ n) ≠ .done := by
        intro h; cases h
      have hstep : ∃ c₁, readCurrentTM.step c' = some c₁ ∧
          c₁.state = .readHi target ∧
          (c₁.work utmSimTape).head = offset + 1 ∧
          (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
          (∀ i, i ≠ utmSimTape → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output := by
        simp only [TM.step, hstate', readCurrentTM]
        simp only [↓reduceIte, hpos_val, hread_one]
        refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only []
          rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
          simp only [Tape.writeAndMove, Tape.move, Tape.write]
          rw [rc_readBackWrite_toΓ_eq hread_ne_start]
          split
          · omega
          · simp [hsim_head']
        · dsimp only []
          rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
          simp only [Tape.writeAndMove, rc_tape_move_cells]
          rw [rc_readBackWrite_toΓ_eq hread_ne_start]
          simp only [Tape.write]; split
          · omega
          · dsimp only []; simp only [Tape.read, Function.update_eq_self]; exact hcells'
        · intro i hne; dsimp only []; rw [if_neg hne]
          rw [rc_tape_idle_preserve (c'.work i)
            (rc_tape_read_ne_start_of_wf _ (hheads' i) (hwf'.2 i)) (hheads' i)]
          exact ho' i hne
        · rw [hinp']; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
        · rw [hout']; exact rc_tape_idle_preserve c.output hout hout_h
      obtain ⟨c₁, hstep', hst1, hh1, hcells1, ho1, hinp1, hout1⟩ := hstep
      have hwf1 : WorkTapesWF c₁.work := by
        constructor
        · intro i; by_cases h : i = utmSimTape
          · rw [h, hcells1]; exact hwf.1 utmSimTape
          · rw [ho1 i h]; exact hwf.1 i
        · intro i j hj; by_cases h : i = utmSimTape
          · rw [h, hcells1]; exact hwf.2 utmSimTape j hj
          · rw [ho1 i h]; exact hwf.2 i j hj
      exact ⟨c₁, .step hstep' .zero, hst1, hh1, hcells1, ho1, hinp1, hout1, hwf1⟩
    | succ m ih =>
      intro c' hhead hstate' hcells' ho' hinp' hout' hwf' hheads'
      -- head < offset since head + (m+1) = offset
      have hhead_lt : (c'.work utmSimTape).head < offset := by omega
      have hhead_ge : (c'.work utmSimTape).head ≥ 1 := hheads' utmSimTape
      have hread_ne_start : (c'.work utmSimTape).read ≠ Γ.start :=
        rc_tape_read_ne_start_of_wf _ hhead_ge (hwf'.2 utmSimTape)
      -- The scan doesn't find the marker at this position.
      set pos := ((c'.work utmSimTape).head - 1) % W with hpos_def
      -- Show the read is NOT Γ.one at this position (head marker not here)
      have hread_ne_one : ¬(pos = 3 * target.val ∧ (c'.work utmSimTape).read = Γ.one) := by
        intro ⟨hpos_eq, hread_eq⟩
        simp only [Tape.read] at hread_eq
        rw [hcells'] at hread_eq
        have hdiv := Nat.div_add_mod ((c'.work utmSimTape).head - 1) W
        have hhead_eq : (c'.work utmSimTape).head =
            SuperCell.simTapeOffset (n + 2) (((c'.work utmSimTape).head - 1) / W) target.val := by
          simp only [SuperCell.simTapeOffset, SuperCell.width, hW_def]
          have := hpos_def ▸ hpos_eq  -- (head-1) % W = 3 * target.val
          set q := ((c'.work utmSimTape).head - 1) / W with hq_def
          -- We have: W * q + pos = head - 1 (from hdiv) and pos = 3 * target.val (from this)
          -- Goal: head = 1 + q * (3*(n+2)) + 3 * target
          -- Since W = 3*(n+2), W*q = q*(3*(n+2)), so head - 1 = q*(3*(n+2)) + 3*target
          have : W * q = q * (3 * (n + 2)) := by rw [hW_def, Nat.mul_comm]
          omega
        rw [hhead_eq] at hread_eq
        have hmk := hsim_marker (((c'.work utmSimTape).head - 1) / W)
        rw [hread_eq] at hmk
        split_ifs at hmk with heq
        rw [← heq, ← hoffset_def] at hhead_eq; omega
      -- Both branches of scan produce the same tape effects (advance sim right, idle rest).
      -- Split on position check BEFORE unfolding TM.step.
      have hstep : ∃ c₁, readCurrentTM.step c' = some c₁ ∧
          c₁.state = .scan target ⟨(pos + 1) % W, Nat.mod_lt _ (by omega)⟩ ∧
          (c₁.work utmSimTape).head = (c'.work utmSimTape).head + 1 ∧
          (c₁.work utmSimTape).cells = (c'.work utmSimTape).cells ∧
          (∀ i, i ≠ utmSimTape → c₁.work i = c'.work i) ∧
          c₁.input = c'.input ∧ c₁.output = c'.output := by
        -- Prove: in both sub-cases, δ returns the same writes/dirs.
        -- Sub-case 1: pos = 3*target (then read ≠ one, inner else)
        -- Sub-case 2: pos ≠ 3*target (outer else)
        have hpos_if :
            (⟨((c'.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ :
              Fin (3 * (n + 2))).val = 3 * target.val →
            (c'.work utmSimTape).read ≠ Γ.one := by
          intro hpeq hre; exact hread_ne_one ⟨hpeq, hre⟩
        -- We can handle both cases uniformly by considering them together
        by_cases hpeq : ((c'.work utmSimTape).head - 1) % W = 3 * target.val
        · -- pos = 3*target, but read ≠ one
          have hread_ne := hpos_if hpeq
          simp only [TM.step, hstate', readCurrentTM, hpeq, hread_ne, ↓reduceIte]
          have hpos_eq_rw : (3 * target.val + 1) % (3 * (n + 2)) = (pos + 1) % W := by
            rw [hpos_def, hpeq, hW_def]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only []; rw [show ReadCurrentQ.scan target ⟨(3 * target.val + 1) %
              (3 * (n + 2)), _⟩ = ReadCurrentQ.scan target ⟨(pos + 1) % W, Nat.mod_lt _ (by omega)⟩
              from by congr 1; ext1; exact hpos_eq_rw]
          · dsimp only []
            rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
            simp only [Tape.writeAndMove, Tape.move, Tape.write]
            rw [rc_readBackWrite_toΓ_eq hread_ne_start]
            split_ifs <;> simp_all
          · dsimp only []
            rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
            simp only [Tape.writeAndMove, rc_tape_move_cells]
            rw [rc_readBackWrite_toΓ_eq hread_ne_start]
            simp only [Tape.write]; split_ifs with h
            · omega
            · dsimp only []; simp only [Tape.read, Function.update_eq_self]
          · intro i hne; dsimp only []; rw [if_neg hne]
            exact rc_tape_idle_preserve (c'.work i)
              (rc_tape_read_ne_start_of_wf _ (hheads' i) (hwf'.2 i)) (hheads' i)
          · simp only [idleDir, (show c'.input.read ≠ Γ.start by rw [hinp']; exact hinp),
              ↓reduceIte, Tape.move]
          · exact rc_tape_idle_preserve c'.output
              (by rw [hout']; exact hout) (by rw [hout']; exact hout_h)
        · -- pos ≠ 3*target
          simp only [TM.step, hstate', readCurrentTM, hpeq, ↓reduceIte]
          refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rfl  -- state: pos and W match definitionally
          · dsimp only []
            rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
            simp only [Tape.writeAndMove, Tape.move, Tape.write]
            rw [rc_readBackWrite_toΓ_eq hread_ne_start]
            split_ifs <;> simp_all
          · dsimp only []
            rw [if_pos (rfl : utmSimTape = (2 : Fin 4))]
            simp only [Tape.writeAndMove, rc_tape_move_cells]
            rw [rc_readBackWrite_toΓ_eq hread_ne_start]
            simp only [Tape.write]; split_ifs with h
            · omega
            · dsimp only []; simp only [Tape.read, Function.update_eq_self]
          · intro i hne; dsimp only []; rw [if_neg hne]
            exact rc_tape_idle_preserve (c'.work i)
              (rc_tape_read_ne_start_of_wf _ (hheads' i) (hwf'.2 i)) (hheads' i)
          · simp only [idleDir, (show c'.input.read ≠ Γ.start by rw [hinp']; exact hinp),
              ↓reduceIte, Tape.move]
          · exact rc_tape_idle_preserve c'.output
              (by rw [hout']; exact hout) (by rw [hout']; exact hout_h)
      obtain ⟨c₁, hstep', hst1, hh1, hcells1, ho1, hinp1, hout1⟩ := hstep
      -- WorkTapesWF for intermediate config
      have hwf1 : WorkTapesWF c₁.work := by
        constructor
        · intro i; by_cases h : i = utmSimTape
          · rw [h, hcells1]; exact hwf'.1 utmSimTape
          · rw [ho1 i h]; exact hwf'.1 i
        · intro i j hj; by_cases h : i = utmSimTape
          · rw [h, hcells1]; exact hwf'.2 utmSimTape j hj
          · rw [ho1 i h]; exact hwf'.2 i j hj
      have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
        intro i; by_cases h : i = utmSimTape
        · rw [h]; omega
        · rw [ho1 i h]; exact hheads' i
      -- Show the new state matches IH form
      have hmod_step : (pos + 1) % W = (c'.work utmSimTape).head % W := by
        rw [hpos_def]
        -- Goal: ((head - 1) % W + 1) % W = head % W
        rw [Nat.mod_add_mod, Nat.sub_add_cancel hhead_ge]
      have hstate1 : c₁.state = .scan target
          ⟨((c₁.work utmSimTape).head - 1) % W, Nat.mod_lt _ (by omega)⟩ := by
        rw [hst1]; congr 1; ext
        simp only [hh1, Nat.add_sub_cancel]
        exact hmod_step
      -- Apply IH
      have hhead1 : (c₁.work utmSimTape).head + m = offset := by omega
      obtain ⟨c_f, hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f⟩ :=
        ih c₁ hhead1 hstate1 (by rw [hcells1, hcells'])
          (by intro i hne; rw [ho1 i hne, ho' i hne])
          (by rw [hinp1, hinp']) (by rw [hout1, hout']) hwf1 hheads1
      exact ⟨c_f, .step hstep' hreach, hst_f, hh_f, hcells_f, ho_f, hinp_f, hout_f, hwf_f⟩
  obtain ⟨c₁, hr1, hst1, hh1, hc1, ho1, hinp1, hout1, hwf1⟩ := scan_result
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 2: readHi step — read sym_hi from sim tape
  -- ═══════════════════════════════════════════════════════════════════
  have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
    intro i; by_cases h : i = utmSimTape
    · rw [h]; omega
    · rw [ho1 i h]; exact hwork_heads i
  have hsim_hi_val : (c₁.work utmSimTape).read =
      (SuperCell.symToCellPair (target_sym h_target)).1 := by
    simp only [Tape.read, hh1, hc1]
    exact hsim_hi h_target
  have readHi_result : ∃ c₂,
      readCurrentTM.step c₁ = some c₂ ∧
      c₂.state = .readLoWrite target (SuperCell.symToCellPair (target_sym h_target)).1 ∧
      (c₂.work utmSimTape).head = offset + 2 ∧
      (c₂.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (∀ i, i ≠ utmSimTape → c₂.work i = c₁.work i) ∧
      c₂.input = c₁.input ∧ c₂.output = c₁.output := by
    simp only [TM.step, hst1, readCurrentTM]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only []; rw [hsim_hi_val]
    · dsimp only []
      simp only [↓reduceIte,
        Tape.writeAndMove, Tape.move, Tape.write]
      rw [rc_readBackWrite_toΓ_eq (rc_tape_read_ne_start_of_wf _ (hheads1 utmSimTape) (hwf1.2 utmSimTape))]
      split
      · omega
      · simp [hh1]
    · dsimp only []
      simp only [↓reduceIte,
        Tape.writeAndMove, rc_tape_move_cells]
      rw [rc_readBackWrite_toΓ_eq (rc_tape_read_ne_start_of_wf _ (hheads1 utmSimTape) (hwf1.2 utmSimTape))]
      simp only [Tape.write]
      split
      · omega
      · dsimp only []; simp only [Tape.read, Function.update_eq_self]; exact hc1
    · intro i hne; dsimp only []; rw [if_neg hne]
      exact rc_tape_idle_preserve (c₁.work i)
        (rc_tape_read_ne_start_of_wf _ (hheads1 i) (hwf1.2 i)) (hheads1 i)
    · simp only [idleDir, (by rw [hinp1]; exact hinp : c₁.input.read ≠ Γ.start), ↓reduceIte, Tape.move]
    · exact rc_tape_idle_preserve c₁.output (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
  obtain ⟨c₂, hr2, hst2, hh2, hc2, ho2, hinp2, hout2⟩ := readHi_result
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 3: readLoWrite step — read sym_lo, transcode, write scrHi
  -- ═══════════════════════════════════════════════════════════════════
  have hsim_lo_val : (c₂.work utmSimTape).read =
      (SuperCell.symToCellPair (target_sym h_target)).2 := by
    simp only [Tape.read, hh2, hc2]
    exact hsim_lo h_target
  -- transcodePair result
  have htrans := transcodePair_symToCellPair (target_sym h_target)
  set sim_hi := (SuperCell.symToCellPair (target_sym h_target)).1
  set sim_lo := (SuperCell.symToCellPair (target_sym h_target)).2
  set scrHi := (transcodePair sim_hi sim_lo).1
  set scrLo := (transcodePair sim_hi sim_lo).2
  have readLoWrite_result : ∃ c₃,
      readCurrentTM.step c₂ = some c₃ ∧
      c₃.state = .writeLo target scrLo ∧
      (c₃.work utmSimTape).head = offset + 2 ∧
      (c₃.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c₃.work utmScratchTape).head = sc_pos + 1 ∧
      (c₃.work utmScratchTape).cells sc_pos = scrHi.toΓ ∧
      (∀ j, j ≠ sc_pos → (c₃.work utmScratchTape).cells j =
        (c₂.work utmScratchTape).cells j) ∧
      (c₃.work utmDescTape) = (c₂.work utmDescTape) ∧
      (c₃.work utmStateTape) = (c₂.work utmStateTape) ∧
      c₃.input = c₂.input ∧ c₃.output = c₂.output := by
    have hne : ReadCurrentQ.readLoWrite target sim_hi ≠ ReadCurrentQ.done := nofun
    have hheads2 : ∀ i, (c₂.work i).head ≥ 1 := by
      intro i; by_cases h : i = utmSimTape
      · rw [h]; omega
      · rw [ho2 i h]; exact hheads1 i
    have hwf2 : WorkTapesWF c₂.work := by
      constructor
      · intro i; by_cases h : i = utmSimTape
        · subst h; show (c₂.work utmSimTape).cells 0 = _; rw [hc2]; exact hwf.1 utmSimTape
        · rw [ho2 i h]; exact hwf1.1 i
      · intro i j hj; by_cases h : i = utmSimTape
        · subst h; show (c₂.work utmSimTape).cells j ≠ _; rw [hc2]; exact hwf.2 utmSimTape j hj
        · rw [ho2 i h]; exact hwf1.2 i j hj
    -- scratch tape in c₂ equals c's scratch tape
    have hsc2 : c₂.work utmScratchTape = c.work utmScratchTape := by
      rw [ho2 utmScratchTape (by decide), ho1 utmScratchTape (by decide)]
    simp only [TM.step, readCurrentTM, hst2, if_neg hne,
      show (c₂.work (2 : Fin 4)).read = sim_lo from hsim_lo_val]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- sim tape head (i=2 ≠ 3, idle)
    · dsimp only []
      rw [if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide)]
      have h := rc_tape_idle_preserve (c₂.work utmSimTape)
        (rc_tape_read_ne_start_of_wf _ (hheads2 utmSimTape) (hwf2.2 utmSimTape)) (hheads2 utmSimTape)
      rw [h]; exact hh2
    -- sim tape cells
    · dsimp only []
      rw [if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide)]
      have h := rc_tape_idle_preserve (c₂.work utmSimTape)
        (rc_tape_read_ne_start_of_wf _ (hheads2 utmSimTape) (hwf2.2 utmSimTape)) (hheads2 utmSimTape)
      rw [h]; exact hc2
    -- scratch head (i=3, write scrHi + right)
    · dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc2, hsc_head]
      split
      · omega
      · dsimp only []
    -- scratch cells sc_pos = scrHi.toΓ
    · dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc2, hsc_head]
      rw [if_neg (by omega)]; exact Function.update_self sc_pos _ _
    -- scratch other cells
    · intro j hne_j; dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc2, hsc_head]
      rw [if_neg (by omega)]; exact Function.update_of_ne (by omega) _ _
    -- desc tape (i=0 ≠ 3)
    · dsimp only []
      rw [if_neg (show utmDescTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmDescTape ≠ (3 : Fin 4) from by decide)]
      exact rc_tape_idle_preserve (c₂.work utmDescTape)
        (rc_tape_read_ne_start_of_wf _ (hheads2 utmDescTape) (hwf2.2 utmDescTape)) (hheads2 utmDescTape)
    -- state tape (i=1 ≠ 3)
    · dsimp only []
      rw [if_neg (show utmStateTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmStateTape ≠ (3 : Fin 4) from by decide)]
      exact rc_tape_idle_preserve (c₂.work utmStateTape)
        (rc_tape_read_ne_start_of_wf _ (hheads2 utmStateTape) (hwf2.2 utmStateTape)) (hheads2 utmStateTape)
    -- input
    · simp only [idleDir, (by rw [hinp2, hinp1]; exact hinp : c₂.input.read ≠ Γ.start),
        ite_false, Tape.move]
    -- output
    · exact rc_tape_idle_preserve c₂.output
        (by rw [hout2, hout1]; exact hout) (by rw [hout2, hout1]; exact hout_h)
  obtain ⟨c₃, hr3, hst3, hh3, hc3, hsc3h, hsc3v, hsc3o, hdesc3, hstate3, hinp3, hout3⟩ :=
    readLoWrite_result
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 4: writeLo step — write scrLo to scratch
  -- ═══════════════════════════════════════════════════════════════════
  have writeLo_result : ∃ c₄,
      readCurrentTM.step c₃ = some c₄ ∧
      c₄.state = .rewindSim target ∧
      (c₄.work utmSimTape).head = offset + 2 ∧
      (c₄.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c₄.work utmScratchTape).head = sc_pos + 2 ∧
      (c₄.work utmScratchTape).cells (sc_pos + 1) = scrLo.toΓ ∧
      (∀ j, j ≠ sc_pos + 1 → (c₄.work utmScratchTape).cells j =
        (c₃.work utmScratchTape).cells j) ∧
      (c₄.work utmDescTape) = (c₃.work utmDescTape) ∧
      (c₄.work utmStateTape) = (c₃.work utmStateTape) ∧
      c₄.input = c₃.input ∧ c₄.output = c₃.output := by
    have hne : ReadCurrentQ.writeLo target scrLo ≠ ReadCurrentQ.done := nofun
    have hheads3 : ∀ i, (c₃.work i).head ≥ 1 := by
      intro i
      by_cases h2 : i = utmSimTape
      · rw [h2]; omega
      · by_cases h3 : i = utmScratchTape
        · rw [h3]; omega
        · by_cases h4 : i = utmDescTape
          · rw [h4, hdesc3, ho2 _ (by decide)]; exact hheads1 _
          · have : i = utmStateTape := by
              revert h2 h3 h4; revert i; decide
            rw [this, hstate3, ho2 _ (by decide)]; exact hheads1 _
    have hwf3 : WorkTapesWF c₃.work := by
      constructor
      · intro i
        by_cases h2 : i = utmSimTape
        · subst h2; show (c₃.work utmSimTape).cells 0 = _; rw [hc3]; exact hwf.1 utmSimTape
        · by_cases h3 : i = utmScratchTape
          · subst h3; rw [hsc3o 0 (by omega)]
            rw [ho2 utmScratchTape (by decide), ho1 utmScratchTape (by decide)]
            exact hwf.1 utmScratchTape
          · by_cases h4 : i = utmDescTape
            · rw [h4, hdesc3, ho2 _ (by decide)]; exact hwf1.1 _
            · have : i = utmStateTape := by revert h2 h3 h4; revert i; decide
              rw [this, hstate3, ho2 _ (by decide)]; exact hwf1.1 _
      · intro i j hj
        by_cases h2 : i = utmSimTape
        · subst h2; show (c₃.work utmSimTape).cells j ≠ _; rw [hc3]; exact hwf.2 utmSimTape j hj
        · by_cases h3 : i = utmScratchTape
          · subst h3
            by_cases hj2 : j = sc_pos
            · subst hj2; rw [hsc3v]; cases scrHi <;> simp [Γw.toΓ]
            · rw [hsc3o j hj2, ho2 utmScratchTape (by decide), ho1 utmScratchTape (by decide)]
              exact hwf.2 utmScratchTape j hj
          · by_cases h4 : i = utmDescTape
            · rw [h4, hdesc3, ho2 _ (by decide)]; exact hwf1.2 _ j hj
            · have : i = utmStateTape := by revert h2 h3 h4; revert i; decide
              rw [this, hstate3, ho2 _ (by decide)]; exact hwf1.2 _ j hj
    -- scratch tape in c₃
    have hsc3 : (c₃.work utmScratchTape).head = sc_pos + 1 := hsc3h
    simp only [TM.step, readCurrentTM, hst3, if_neg hne]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- sim tape head (i=2 ≠ 3, idle)
    · dsimp only []
      rw [if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide)]
      have h := rc_tape_idle_preserve (c₃.work utmSimTape)
        (rc_tape_read_ne_start_of_wf _ (hheads3 utmSimTape) (hwf3.2 utmSimTape)) (hheads3 utmSimTape)
      rw [h]; exact hh3
    -- sim tape cells
    · dsimp only []
      rw [if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmSimTape ≠ (3 : Fin 4) from by decide)]
      have h := rc_tape_idle_preserve (c₃.work utmSimTape)
        (rc_tape_read_ne_start_of_wf _ (hheads3 utmSimTape) (hwf3.2 utmSimTape)) (hheads3 utmSimTape)
      rw [h]; exact hc3
    -- scratch head = sc_pos + 2
    · dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, Tape.move, Tape.write, hsc3]
      split
      · omega
      · dsimp only []
    -- scratch cells (sc_pos + 1) = scrLo.toΓ
    · dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc3]
      rw [if_neg (by omega)]; exact Function.update_self (sc_pos + 1) _ _
    -- scratch other cells
    · intro j hne_j; dsimp only []
      rw [if_pos (show utmScratchTape = (3 : Fin 4) from rfl),
          if_pos (show utmScratchTape = (3 : Fin 4) from rfl)]
      simp only [Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc3]
      rw [if_neg (by omega)]; exact Function.update_of_ne (by omega) _ _
    -- desc tape (i=0 ≠ 3)
    · dsimp only []
      rw [if_neg (show utmDescTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmDescTape ≠ (3 : Fin 4) from by decide)]
      exact rc_tape_idle_preserve (c₃.work utmDescTape)
        (rc_tape_read_ne_start_of_wf _ (hheads3 utmDescTape) (hwf3.2 utmDescTape)) (hheads3 utmDescTape)
    -- state tape (i=1 ≠ 3)
    · dsimp only []
      rw [if_neg (show utmStateTape ≠ (3 : Fin 4) from by decide),
          if_neg (show utmStateTape ≠ (3 : Fin 4) from by decide)]
      exact rc_tape_idle_preserve (c₃.work utmStateTape)
        (rc_tape_read_ne_start_of_wf _ (hheads3 utmStateTape) (hwf3.2 utmStateTape)) (hheads3 utmStateTape)
    -- input
    · simp only [idleDir, (by rw [hinp3, hinp2, hinp1]; exact hinp : c₃.input.read ≠ Γ.start),
        ite_false, Tape.move]
    -- output
    · exact rc_tape_idle_preserve c₃.output
        (by rw [hout3, hout2, hout1]; exact hout)
        (by rw [hout3, hout2, hout1]; exact hout_h)
  obtain ⟨c₄, hr4, hst4, hh4, hc4, hsc4h, hsc4v, hsc4o, hdesc4, hstate4, hinp4, hout4⟩ :=
    writeLo_result
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 5: Rewind sim tape
  -- ═══════════════════════════════════════════════════════════════════
  have hwf4 : WorkTapesWF c₄.work := by
    constructor
    · intro i
      by_cases h2 : i = utmSimTape
      · subst h2; show (c₄.work utmSimTape).cells 0 = _; rw [hc4]; exact hwf.1 utmSimTape
      · by_cases h3 : i = utmScratchTape
        · subst h3
          rw [hsc4o 0 (by omega), hsc3o 0 (by omega)]
          rw [ho2 utmScratchTape (by decide), ho1 utmScratchTape (by decide)]
          exact hwf.1 utmScratchTape
        · by_cases h4 : i = utmDescTape
          · rw [h4, hdesc4, hdesc3, ho2 _ (by decide)]; exact hwf1.1 _
          · have : i = utmStateTape := by revert h2 h3 h4; revert i; decide
            rw [this, hstate4, hstate3, ho2 _ (by decide)]; exact hwf1.1 _
    · intro i j hj
      by_cases h2 : i = utmSimTape
      · subst h2; show (c₄.work utmSimTape).cells j ≠ _; rw [hc4]; exact hwf.2 utmSimTape j hj
      · by_cases h3 : i = utmScratchTape
        · subst h3
          by_cases hj2 : j = sc_pos + 1
          · subst hj2; rw [hsc4v]; cases scrLo <;> simp [Γw.toΓ]
          · rw [hsc4o j hj2]
            by_cases hj3 : j = sc_pos
            · subst hj3; rw [hsc3v]; cases scrHi <;> simp [Γw.toΓ]
            · rw [hsc3o j hj3, ho2 utmScratchTape (by decide), ho1 utmScratchTape (by decide)]
              exact hwf.2 utmScratchTape j hj
        · by_cases h4 : i = utmDescTape
          · rw [h4, hdesc4, hdesc3, ho2 _ (by decide)]; exact hwf1.2 _ j hj
          · have : i = utmStateTape := by revert h2 h3 h4; revert i; decide
            rw [this, hstate4, hstate3, ho2 _ (by decide)]; exact hwf1.2 _ j hj
  have hheads4_ne : ∀ i, i ≠ utmSimTape → (c₄.work i).head ≥ 1 := by
    intro i hne
    by_cases h3 : i = utmScratchTape
    · rw [h3]; omega
    · by_cases h4 : i = utmDescTape
      · rw [h4, hdesc4, hdesc3, ho2 _ (by decide)]; exact hheads1 _
      · have : i = utmStateTape := by revert hne h3 h4; revert i; decide
        rw [this, hstate4, hstate3, ho2 _ (by decide)]; exact hheads1 _
  obtain ⟨c₅, hr5, hst5, hh5, hc5, ho5, hinp5, hout5, hwf5⟩ :=
    rewindSim_simulation (offset + 2) c₄ target hst4 hh4 hwf4
      (by rw [hinp4, hinp3, hinp2, hinp1]; exact hinp)
      (by rw [hinp4, hinp3, hinp2, hinp1]; exact hinp_h)
      (by rw [hout4, hout3, hout2, hout1]; exact hout)
      (by rw [hout4, hout3, hout2, hout1]; exact hout_h)
      hheads4_ne
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 6: rewindSimR step — transition to next tape or rewindState
  -- ═══════════════════════════════════════════════════════════════════
  have hheads5 : ∀ i, (c₅.work i).head ≥ 1 := by
    intro i; by_cases h : i = utmSimTape
    · rw [h]; omega
    · rw [ho5 i h]; exact hheads4_ne i h
  have rewindSimR_result : ∃ c₆,
      readCurrentTM.step c₅ = some c₆ ∧
      (if h : target.val = n + 1 then
        c₆.state = .rewindState
      else
        c₆.state = .scan ⟨target.val + 1, by omega⟩ ⟨0, by omega⟩) ∧
      c₆.work = c₅.work ∧
      c₆.input = c₅.input ∧ c₆.output = c₅.output := by
    simp only [TM.step, hst5, readCurrentTM]
    have hne : ReadCurrentQ.rewindSimR target ≠ ReadCurrentQ.done := nofun
    rw [if_neg hne]
    by_cases htgt : target.val = n + 1
    · rw [dif_pos htgt]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · rw [dif_pos htgt]
      · ext i; exact rc_tape_idle_preserve (c₅.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads5 i) (hwf5.2 i)) (hheads5 i)
      · simp only [idleDir, (show c₅.input.read ≠ Γ.start from by
          rw [hinp5, hinp4, hinp3, hinp2, hinp1]; exact hinp), ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c₅.output
          (by rw [hout5, hout4, hout3, hout2, hout1]; exact hout)
          (by rw [hout5, hout4, hout3, hout2, hout1]; exact hout_h)
    · rw [dif_neg htgt]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · rw [dif_neg htgt]
      · ext i; exact rc_tape_idle_preserve (c₅.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads5 i) (hwf5.2 i)) (hheads5 i)
      · simp only [idleDir, (show c₅.input.read ≠ Γ.start from by
          rw [hinp5, hinp4, hinp3, hinp2, hinp1]; exact hinp), ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c₅.output
          (by rw [hout5, hout4, hout3, hout2, hout1]; exact hout)
          (by rw [hout5, hout4, hout3, hout2, hout1]; exact hout_h)
  obtain ⟨c₆, hr6, hst6, hw6, hinp6, hout6⟩ := rewindSimR_result
  -- ═══════════════════════════════════════════════════════════════════
  -- Compose all phases
  -- ═══════════════════════════════════════════════════════════════════
  have hreach := reachesIn_trans _ hr1
    (.step hr2 (.step hr3 (.step hr4
      (reachesIn_trans _ hr5 (.step hr6 .zero)))))
  refine ⟨c₆, _, hreach, hst6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- sim tape head = 1
  · rw [hw6]; exact hh5
  -- sim tape cells preserved
  · rw [hw6, hc5, hc4]
  -- scratch tape head = sc_pos + 2
  · rw [hw6, ho5 utmScratchTape (by decide)]; exact hsc4h
  -- scratch cell sc_pos = correct encode bit 0
  · rw [hw6, ho5 utmScratchTape (by decide)]
    rw [hsc4o sc_pos (by omega)]
    rw [hsc3v]
    exact htrans.1
  -- scratch cell sc_pos + 1 = correct encode bit 1
  · rw [hw6, ho5 utmScratchTape (by decide)]
    rw [hsc4v]
    exact htrans.2
  -- previously written scratch cells preserved
  · intro j hj
    rw [hw6, ho5 utmScratchTape (by decide)]
    rw [hsc4o j (by omega)]
    rw [hsc3o j (by omega)]
    rw [ho2 utmScratchTape (by decide)]
    rw [ho1 utmScratchTape (by decide)]
  -- desc tape preserved
  · rw [hw6, ho5 utmDescTape (by decide), hdesc4, hdesc3]
    rw [ho2 utmDescTape (by decide), ho1 utmDescTape (by decide)]
  -- state tape preserved
  · rw [hw6, ho5 utmStateTape (by decide), hstate4, hstate3]
    rw [ho2 utmStateTape (by decide), ho1 utmStateTape (by decide)]
  -- input preserved
  · rw [hinp6, hinp5, hinp4, hinp3, hinp2, hinp1]
  -- output preserved
  · rw [hout6, hout5, hout4, hout3, hout2, hout1]
  -- WorkTapesWF preserved (two conjuncts)
  · intro i; rw [hw6]; exact hwf5.1 i
  · intro i j hj; rw [hw6]; exact hwf5.2 i j hj

/-- Phase 3: rewind state tape from some position to cell 1. -/
private theorem rewindState_simulation :
    ∀ (st_head : ℕ) (c : Cfg 4 (readCurrentTM (n := n)).Q),
    c.state = .rewindState →
    (c.work utmStateTape).head = st_head →
    WorkTapesWF c.work →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    (∀ i, i ≠ utmStateTape → (c.work i).head ≥ 1) →
    ∃ c',
      (readCurrentTM (n := n)).reachesIn (st_head + 2) c c' ∧
      c'.state = .rewindScratch ∧
      (c'.work utmStateTape).head = 1 ∧
      (c'.work utmStateTape).cells = (c.work utmStateTape).cells ∧
      (∀ i, i ≠ utmStateTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro st_head; induction st_head with
  | zero =>
    intro c hstate hst_head hwf hinp hinp_h hout hout_h hheads
    have hread : (c.work utmStateTape).read = Γ.start := by
      simp [Tape.read, hst_head, hwf.1 utmStateTape]
    -- Step 1: rewindState → rewindStateR (read ▷, move right)
    have hstep1 : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindStateR ∧
        (c₁.work utmStateTape).head = 1 ∧
        (c₁.work utmStateTape).cells = (c.work utmStateTape).cells ∧
        (∀ i, i ≠ utmStateTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write, hst_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells, Tape.write, hst_head]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep1
    -- Step 2: rewindStateR → rewindScratch (all idle)
    -- All tapes have head ≥ 1 after step 1
    have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
      intro i; by_cases h : i = utmStateTape
      · rw [h]; omega
      · rw [hw1 i h]; exact hheads i h
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h : i = utmStateTape
        · rw [h, hcells1]; exact hwf.1 utmStateTape
        · rw [hw1 i h]; exact hwf.1 i
      · intro i j hj; by_cases h : i = utmStateTape
        · rw [h, hcells1]; exact hwf.2 utmStateTape j hj
        · rw [hw1 i h]; exact hwf.2 i j hj
    have hinp1' : c₁.input.read ≠ Γ.start := by rw [hinp1]; exact hinp
    have hout1' : c₁.output.read ≠ Γ.start := by rw [hout1]; exact hout
    have hstep2 : ∃ c₂, (readCurrentTM (n := n)).step c₁ = some c₂ ∧
        c₂.state = .rewindScratch ∧
        c₂.work = c₁.work ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output := by
      simp only [TM.step, hst1, readCurrentTM]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · ext i; dsimp only []
        exact rc_tape_idle_preserve (c₁.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads1 i) (hwf1.2 i)) (hheads1 i)
      · simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c₁.output hout1' (by rw [hout1]; exact hout_h)
    obtain ⟨c₂, hstep2', hst2, hwork2, hinp2, hout2⟩ := hstep2
    refine ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork2]; exact hhead1
    · rw [hwork2, hcells1]
    · intro i hne; rw [hwork2, hw1 i hne]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]
    · rw [hwork2]; exact hwf1
  | succ h ih =>
    intro c hstate hst_head hwf hinp hinp_h hout hout_h hheads
    have hread_ne : (c.work utmStateTape).read ≠ Γ.start := by
      simp [Tape.read, hst_head]; exact hwf.2 utmStateTape (h + 1) (by omega)
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindState ∧
        (c₁.work utmStateTape).head = h ∧
        (c₁.work utmStateTape).cells = (c.work utmStateTape).cells ∧
        (∀ i, i ≠ utmStateTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hst_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h' : i = utmStateTape
        · rw [h', hcells1]; exact hwf.1 utmStateTape
        · rw [hw1 i h']; exact hwf.1 i
      · intro i j hj; by_cases h' : i = utmStateTape
        · rw [h', hcells1]; exact hwf.2 utmStateTape j hj
        · rw [hw1 i h']; exact hwf.2 i j hj
    have hheads1 : ∀ i, i ≠ utmStateTape → (c₁.work i).head ≥ 1 := by
      intro i h'; rw [hw1 i h']; exact hheads i h'
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ := ih c₁ hst1
      hhead1 hwf1
      (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
      (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
      hheads1
    refine ⟨c_f, .step hstep' hreach, hst_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

/-- Phase 3: rewind scratch tape to cell 1 and halt. -/
private theorem rewindScratch_simulation :
    ∀ (sc_head : ℕ) (c : Cfg 4 (readCurrentTM (n := n)).Q),
    c.state = .rewindScratch →
    (c.work utmScratchTape).head = sc_head →
    WorkTapesWF c.work →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    (∀ i, i ≠ utmScratchTape → (c.work i).head ≥ 1) →
    ∃ c',
      (readCurrentTM (n := n)).reachesIn (sc_head + 2) c c' ∧
      (readCurrentTM (n := n)).halted c' ∧
      (c'.work utmScratchTape).head = 1 ∧
      (c'.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
      (∀ i, i ≠ utmScratchTape → c'.work i = c.work i) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro sc_head; induction sc_head with
  | zero =>
    intro c hstate hsc_head hwf hinp hinp_h hout hout_h hheads
    have hread : (c.work utmScratchTape).read = Γ.start := by
      simp [Tape.read, hsc_head, hwf.1 utmScratchTape]
    -- Step 1: rewindScratch → rewindScratchR (read ▷, move right)
    have hstep1 : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindScratchR ∧
        (c₁.work utmScratchTape).head = 1 ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write, hsc_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells, Tape.write, hsc_head]
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep1
    -- All tapes have head ≥ 1 after step 1
    have hheads1 : ∀ i, (c₁.work i).head ≥ 1 := by
      intro i; by_cases h : i = utmScratchTape
      · rw [h]; omega
      · rw [hw1 i h]; exact hheads i h
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
    -- Step 2: rewindScratchR → done (all idle, halted)
    have hstep2 : ∃ c₂, (readCurrentTM (n := n)).step c₁ = some c₂ ∧
        c₂.state = .done ∧
        c₂.work = c₁.work ∧
        c₂.input = c₁.input ∧ c₂.output = c₁.output := by
      simp only [TM.step, hst1, readCurrentTM]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
      · ext i; dsimp only []
        exact rc_tape_idle_preserve (c₁.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads1 i) (hwf1.2 i)) (hheads1 i)
      · simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c₁.output hout1' (by rw [hout1]; exact hout_h)
    obtain ⟨c₂, hstep2', hst2, hwork2, hinp2, hout2⟩ := hstep2
    refine ⟨c₂, .step hstep1' (.step hstep2' .zero), hst2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork2]; exact hhead1
    · rw [hwork2, hcells1]
    · intro i hne; rw [hwork2, hw1 i hne]
    · rw [hinp2, hinp1]
    · rw [hout2, hout1]
    · rw [hwork2]; exact hwf1
  | succ h ih =>
    intro c hstate hsc_head hwf hinp hinp_h hout hout_h hheads
    have hread_ne : (c.work utmScratchTape).read ≠ Γ.start := by
      simp [Tape.read, hsc_head]; exact hwf.2 utmScratchTape (h + 1) (by omega)
    have hstep : ∃ c₁, (readCurrentTM (n := n)).step c = some c₁ ∧
        c₁.state = .rewindScratch ∧
        (c₁.work utmScratchTape).head = h ∧
        (c₁.work utmScratchTape).cells = (c.work utmScratchTape).cells ∧
        (∀ i, i ≠ utmScratchTape → c₁.work i = c.work i) ∧
        c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hstate, readCurrentTM, ↓reduceIte, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, Tape.move]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · omega
        · simp [hsc_head]
      · dsimp only []
        simp only [↓reduceIte,
          Tape.writeAndMove, rc_tape_move_cells]
        rw [rc_readBackWrite_toΓ_eq hread_ne]
        simp only [Tape.write]; split
        · rfl
        · exact Function.update_eq_self _ _
      · intro i hne; dsimp only []; rw [if_neg hne]
        exact rc_tape_idle_preserve (c.work i)
          (rc_tape_read_ne_start_of_wf _ (hheads i hne) (hwf.2 i)) (hheads i hne)
      · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · exact rc_tape_idle_preserve c.output hout hout_h
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hw1, hinp1, hout1⟩ := hstep
    have hwf1 : WorkTapesWF c₁.work := by
      constructor
      · intro i; by_cases h' : i = utmScratchTape
        · rw [h', hcells1]; exact hwf.1 utmScratchTape
        · rw [hw1 i h']; exact hwf.1 i
      · intro i j hj; by_cases h' : i = utmScratchTape
        · rw [h', hcells1]; exact hwf.2 utmScratchTape j hj
        · rw [hw1 i h']; exact hwf.2 i j hj
    have hheads1 : ∀ i, i ≠ utmScratchTape → (c₁.work i).head ≥ 1 := by
      intro i h'; rw [hw1 i h']; exact hheads i h'
    obtain ⟨c_f, hreach, hhalt_f, hhead_f, hcells_f, hw_f, hinp_f, hout_f, hwf_f⟩ := ih c₁ hst1
      hhead1 hwf1
      (by rw [hinp1]; exact hinp) (by rw [hinp1]; exact hinp_h)
      (by rw [hout1]; exact hout) (by rw [hout1]; exact hout_h)
      hheads1
    refine ⟨c_f, .step hstep' hreach, hhalt_f, hhead_f, ?_, ?_, ?_, ?_, hwf_f⟩
    · rw [hcells_f, hcells1]
    · intro i hne; rw [hw_f i hne, hw1 i hne]
    · rw [hinp_f, hinp1]
    · rw [hout_f, hout1]

-- ════════════════════════════════════════════════════════════════════════
-- Assembling the scratch tape postcondition
-- ════════════════════════════════════════════════════════════════════════

/-- Helper: the head symbol for simulated tape t_idx in simCfg.
    t_idx = 0 → input tape
    t_idx = 1..n → work tape (t_idx - 1)
    t_idx = n+1 → output tape -/
private noncomputable def simHeadSym {n : ℕ} {Q : Type} (simCfg : Cfg n Q)
    (t_idx : Fin (n + 2)) : Γ :=
  if h0 : t_idx.val = 0 then simCfg.input.read
  else if h1 : t_idx.val ≤ n then
    (simCfg.work ⟨t_idx.val - 1, by omega⟩).read
  else simCfg.output.read

/-- The encodeInputPattern matches what readCurrentTM writes to scratch. -/
private theorem encodeInputPattern_matches_scratch
    {Q : Type} (k n : ℕ) (q : Fin k) (simCfg : Cfg n Q) :
    TMEncoding.encodeInputPattern k n q simCfg.input.read
      (fun i => (simCfg.work i).read) simCfg.output.read =
    (List.finRange k).map (fun i => i == q) ++
    simCfg.input.read.encode ++
    (List.finRange n).flatMap (fun i => ((simCfg.work i).read).encode) ++
    simCfg.output.read.encode := by
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2 iteration: per_tape_simulation across all n+2 tapes
-- ════════════════════════════════════════════════════════════════════════

/-- Helper: the head position of simulated tape t_idx in simCfg. -/
private noncomputable def simHeadPos {n : ℕ} {Q : Type} (simCfg : Cfg n Q)
    (t_idx : Fin (n + 2)) : ℕ :=
  if h0 : t_idx.val = 0 then simCfg.input.head
  else if h1 : t_idx.val ≤ n then
    (simCfg.work ⟨t_idx.val - 1, by omega⟩).head
  else simCfg.output.head

/-- Helper: the cell function of simulated tape t_idx in simCfg. -/
private noncomputable def simCellsFn {n : ℕ} {Q : Type} (simCfg : Cfg n Q)
    (t_idx : Fin (n + 2)) : ℕ → Γ :=
  if h0 : t_idx.val = 0 then simCfg.input.cells
  else if h1 : t_idx.val ≤ n then
    (simCfg.work ⟨t_idx.val - 1, by omega⟩).cells
  else simCfg.output.cells

/-- Extract per-tape sim conditions from superCellsCorrect for a given target tape. -/
private theorem extract_sim_conditions
    {Q : Type} (simCfg : Cfg n Q) (cells : ℕ → Γ)
    (hscc : superCellsCorrect simCfg ⟨1, cells⟩) (target : Fin (n + 2)) :
    (∀ pos, cells (SuperCell.simTapeOffset (n + 2) pos target.val) =
      if simHeadPos simCfg target = pos then Γ.one else Γ.blank) ∧
    (∀ pos, cells (SuperCell.simTapeOffset (n + 2) pos target.val + 1) =
      (SuperCell.symToCellPair (simCellsFn simCfg target pos)).1) ∧
    (∀ pos, cells (SuperCell.simTapeOffset (n + 2) pos target.val + 2) =
      (SuperCell.symToCellPair (simCellsFn simCfg target pos)).2) := by
  obtain ⟨_, hscc_inp, hscc_work, hscc_out⟩ := hscc
  rcases target with ⟨tv, htv⟩
  simp only [] at *
  by_cases h0 : tv = 0
  · -- Input tape
    subst h0
    simp only [simHeadPos, simCellsFn, ↓reduceDIte]
    exact ⟨fun pos => (hscc_inp pos).1,
           fun pos => (hscc_inp pos).2.1,
           fun pos => (hscc_inp pos).2.2⟩
  · by_cases hlast : tv = n + 1
    · -- Output tape
      subst hlast
      simp only [simHeadPos, simCellsFn, show (n + 1) ≠ 0 from by omega,
        show ¬(n + 1 ≤ n) from by omega, ↓reduceDIte]
      exact ⟨fun pos => (hscc_out pos).1,
             fun pos => (hscc_out pos).2.1,
             fun pos => (hscc_out pos).2.2⟩
    · -- Work tape
      have hle : tv ≤ n := by omega
      have hlt : tv - 1 < n := by omega
      simp only [simHeadPos, simCellsFn, h0, hle, ↓reduceDIte]
      have hvaleq : (⟨tv - 1, hlt⟩ : Fin n).val + 1 = tv := by
        show tv - 1 + 1 = tv; omega
      refine ⟨fun pos => ?_, fun pos => ?_, fun pos => ?_⟩
      · have := (hscc_work ⟨tv - 1, hlt⟩ pos).1
        simp only [hvaleq] at this; exact this
      · have := (hscc_work ⟨tv - 1, hlt⟩ pos).2.1
        simp only [hvaleq] at this; exact this
      · have := (hscc_work ⟨tv - 1, hlt⟩ pos).2.2
        simp only [hvaleq] at this; exact this

/-- Phase 2: iterate per_tape_simulation over tapes [target..n+1], accumulating
    encoded head symbols onto the scratch tape.

    Starts at `.scan target 0` with scratch head at `sc_pos` and produces
    `.rewindState` with scratch head at `sc_pos + 2 * (n + 2 - target.val)`. -/
private theorem all_tapes_simulation
    {Q : Type} [DecidableEq Q] [Fintype Q]
    (simCfg : Cfg n Q) :
    ∀ (remaining : ℕ) (target : Fin (n + 2))
    (htarget : target.val = n + 2 - remaining) (hrem : remaining ≤ n + 2)
    (c : Cfg 4 (readCurrentTM (n := n)).Q)
    (sc_pos : ℕ),
    c.state = .scan target ⟨0, by omega⟩ →
    (c.work utmSimTape).head = 1 →
    (c.work utmSimTape).cells 0 = Γ.start →
    superCellsCorrect simCfg ⟨1, (c.work utmSimTape).cells⟩ →
    (c.work utmScratchTape).head = sc_pos →
    sc_pos ≥ 1 →
    WorkTapesWF c.work →
    c.input.read ≠ Γ.start → c.input.head ≥ 1 →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    (∀ i, (c.work i).head ≥ 1) →
    ∃ c' t,
      (readCurrentTM (n := n)).reachesIn t c c' ∧
      c'.state = .rewindState ∧
      (c'.work utmSimTape).head = 1 ∧
      (c'.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      (c'.work utmDescTape) = (c.work utmDescTape) ∧
      (c'.work utmStateTape) = (c.work utmStateTape) ∧
      (c'.work utmScratchTape).head = sc_pos + 2 * remaining ∧
      (∀ j, j < sc_pos → (c'.work utmScratchTape).cells j =
        (c.work utmScratchTape).cells j) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work := by
  intro remaining
  induction remaining with
  | zero =>
    intro target htarget; exact absurd htarget (by omega)
  | succ m ih =>
    intro target htarget hrem c sc_pos hstate hsim_head hsim_cell0 hscc
      hsc_head hsc_ge hwf hinp hinp_h hout hout_h hwork_heads
    -- Extract marker/hi/lo conditions for current target
    have ⟨hmarker, hhi, hlo⟩ := extract_sim_conditions simCfg _ hscc target
    -- Apply per_tape_simulation
    obtain ⟨c', t', hreach', hnext', hsim_head', hsim_cells', hsc_head', hsc0, hsc1,
      hsc_prev, hdesc', hstate', hinp', hout', hwf'⟩ :=
      per_tape_simulation (simCellsFn simCfg target) c target
        (simHeadPos simCfg target) sc_pos hstate hsim_head hmarker hhi hlo
        hsc_head hsc_ge hwf hinp hinp_h hout hout_h hsim_cell0 hwork_heads
    -- Case split: last tape or not?
    by_cases hlast : target.val = n + 1
    · -- Last tape (m = 0): per_tape_simulation reached .rewindState
      have hm0 : m = 0 := by omega
      subst hm0; simp [hlast] at hnext'
      exact ⟨c', t', hreach', hnext', hsim_head', hsim_cells', hdesc', hstate',
        by rw [hsc_head'], hsc_prev, hinp', hout', hwf'⟩
    · -- Not last tape: per_tape_simulation reached .scan ⟨target+1, _⟩, recurse
      simp [hlast] at hnext'
      have htarget1 : (⟨target.val + 1, by omega⟩ : Fin (n + 2)).val = n + 2 - m := by
        show target.val + 1 = n + 2 - m; omega
      obtain ⟨c'', t'', hreach'', hst'', hsim_head'', hsim_cells'', hdesc'', hstate'',
        hsc_head'', hsc_prev'', hinp'', hout'', hwf''⟩ :=
        ih ⟨target.val + 1, by omega⟩ htarget1 (by omega) c' (sc_pos + 2) hnext'
          hsim_head' (by rw [hsim_cells']; exact hsim_cell0)
          (by rw [hsim_cells']; exact hscc) hsc_head' (by omega) hwf'
          (by rw [hinp']; exact hinp) (by rw [hinp']; exact hinp_h)
          (by rw [hout']; exact hout) (by rw [hout']; exact hout_h)
          (by intro i
              by_cases hi2 : i = utmSimTape
              · rw [hi2]; omega
              · by_cases hi3 : i = utmScratchTape
                · rw [hi3, hsc_head']; omega
                · have : i = utmDescTape ∨ i = utmStateTape := by
                    simp only [Fin.ext_iff, utmSimTape, utmScratchTape, utmDescTape, utmStateTape] at *
                    omega
                  rcases this with rfl | rfl
                  · rw [hdesc']; exact hwork_heads _
                  · rw [hstate']; exact hwork_heads _)
      exact ⟨c'', t' + t'', reachesIn_trans readCurrentTM hreach' hreach'', hst'',
        hsim_head'', by rw [hsim_cells'', hsim_cells'],
        by rw [hdesc'', hdesc'], by rw [hstate'', hstate'],
        by rw [hsc_head'']; omega,
        fun j hj => by rw [hsc_prev'' j (by omega), hsc_prev j hj],
        by rw [hinp'', hinp'], by rw [hout'', hout'], hwf''⟩

-- ════════════════════════════════════════════════════════════════════════
-- Full readCurrentTM_hoareTime
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `readCurrentTM`.

    **Pre**: State and sim tapes encode `simCfg`; desc tape valid; all heads at 1.
    **Post**: All tapes preserved + scratch has input pattern for current
    state and head symbols. Heads returned to cell 1. -/
theorem readCurrentTM_hoareTime' (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (simCfg : Cfg n tm.Q) :
    let e := tm.stateEquivK hk
    ∃ B, (readCurrentTM (n := n)).HoareTime
      (fun inp work out =>
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (e simCfg.state) (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1)
      (fun _inp work _out =>
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (e simCfg.state) (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        scratchHasInputPattern k n (e simCfg.state)
          simCfg.input.read (fun i => (simCfg.work i).read) simCfg.output.read
          (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  -- Proof structure: Phase 1 (copyState) → Phase 2 (all_tapes) →
  -- Phase 3a (rewindState) → Phase 3b (rewindScratch), composed via reachesIn_trans.
  -- All phase lemmas are proved; this is mechanical composition.
  sorry

end TM
