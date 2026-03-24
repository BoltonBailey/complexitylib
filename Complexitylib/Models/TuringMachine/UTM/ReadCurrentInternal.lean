import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# ReadCurrent proof internals

Step-by-step simulation lemmas for `readCurrentTM`.
-/

namespace TM

variable {n : ℕ}

private theorem reachesIn_toReaches' {tm : TM n} {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') : tm.reaches c c' := by
  induction h with
  | zero => exact Relation.ReflTransGen.refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs ih

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
      (∀ j, j ≥ k + 1 → (c'.work utmScratchTape).cells j =
        (c.work utmScratchTape).cells j) ∧
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
      (∀ j, j ≥ k + 1 → (c'.work utmScratchTape).cells j =
        (c.work utmScratchTape).cells j) →
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
        (∀ j, j ≥ k + 1 → (c_f.work utmScratchTape).cells j =
          (c.work utmScratchTape).cells j) ∧
        (c_f.work utmSimTape).head = 1 ∧
        (c_f.work utmSimTape).cells = (c.work utmSimTape).cells ∧
        c_f.work utmDescTape = c.work utmDescTape ∧
        c_f.input = c.input ∧ c_f.output = c.output ∧
        WorkTapesWF c_f.work by
    exact loop k c le_rfl hstate (by omega) (by omega) hsim_head rfl rfl rfl rfl rfl
      (fun _ hj => absurd hj (by omega)) (fun _ _ => rfl) hwf
  intro rem; induction rem with
  | zero =>
    intro c' _ hstate' hst_h' hsc_h' hsim_h' hdesc' hst_c' hsim_c' hinp' hout' hsc_done hsc_high hwf'
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
    refine ⟨c₁, .step hstep' .zero, hst1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwork1]; omega
    · rw [hwork1, hst_c']
    · rw [hwork1]; omega
    · intro j hj; rw [hwork1]; exact hsc_done j (by omega)
    · intro j hj; rw [hwork1]; exact hsc_high j hj
    · rw [hwork1, hsim_h']
    · rw [hwork1, hsim_c']
    · rw [hwork1, hdesc']
    · rw [hinp1, hinp']
    · rw [hout1, hout']
    · rw [hwork1]; exact hwf'
  | succ m ih =>
    intro c' hle hstate' hst_h' hsc_h' hsim_h' hdesc' hst_c' hsim_c' hinp' hout' hsc_done hsc_high hwf'
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
    -- Scratch high cells preserved for IH
    have hsc_high₁ : ∀ j, j ≥ k + 1 →
        (c₁.work utmScratchTape).cells j = (c.work utmScratchTape).cells j := by
      intro j hj; rw [hc₁_sc_other j (by omega)]; exact hsc_high j hj
    -- Apply IH
    obtain ⟨c_f, hreach, hst_f, hhead_f, hcells_f, hsch_f, hsc_f, hsc_high_f, hsimh_f, hsimc_f,
            hdesc_f, hinp_f, hout_f, hwf_f⟩ :=
      ih c₁ (by omega) hc₁st (by omega) (by omega)
        (by rw [hc₁sim]; exact hsim_h')
        (by rw [hc₁desc]; exact hdesc')
        (by rw [hc₁stc]; exact hst_c')
        (by rw [hc₁sim]; exact hsim_c')
        (by rw [hc₁inp]; exact hinp')
        (by rw [hc₁out]; exact hout')
        hsc_done₁ hsc_high₁ hwf₁
    exact ⟨c_f, .step hstep' hreach, hst_f, hhead_f, hcells_f, hsch_f, hsc_f, hsc_high_f, hsimh_f, hsimc_f,
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
      -- Scratch cells above written range preserved
      (∀ j, j ≥ sc_pos + 2 → (c'.work utmScratchTape).cells j = (c.work utmScratchTape).cells j) ∧
      -- Other tapes preserved
      (c'.work utmDescTape) = (c.work utmDescTape) ∧
      (c'.work utmStateTape) = (c.work utmStateTape) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work ∧
      t ≤ 2 * SuperCell.simTapeOffset (n + 2) h_target target.val + 7 := by
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
  refine ⟨c₆, _, hreach, hst6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  -- scratch cells above written range preserved
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
  · exact ⟨fun i => by rw [hw6]; exact hwf5.1 i, fun i j hj => by rw [hw6]; exact hwf5.2 i j hj⟩
  -- Time bound: 2 * offset + 7
  · omega

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

/-- Time bound for all_tapes_simulation: sum of per-tape costs from `targetVal`
    for `remaining` tapes. Each tape costs `2 * simTapeOffset(n+2, head_pos, idx) + 7`. -/
private noncomputable def allTapesBound {n : ℕ} {Q : Type} (simCfg : Cfg n Q)
    (remaining : ℕ) (targetVal : ℕ) : ℕ :=
  match remaining with
  | 0 => 0
  | m + 1 =>
    (2 * SuperCell.simTapeOffset (n + 2)
      (if h : targetVal < n + 2 then simHeadPos simCfg ⟨targetVal, h⟩ else 0) targetVal + 7) +
    allTapesBound simCfg m (targetVal + 1)

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
      (∀ j, j ≥ sc_pos + 2 * remaining → (c'.work utmScratchTape).cells j =
        (c.work utmScratchTape).cells j) ∧
      (∀ (p : ℕ) (hp : p < remaining),
        (c'.work utmScratchTape).cells (sc_pos + 2 * p) =
          Γ.ofBool ((simCellsFn simCfg ⟨target.val + p, by omega⟩
            (simHeadPos simCfg ⟨target.val + p, by omega⟩)).encode[0]'(by rw [Γ.encode_length]; omega)) ∧
        (c'.work utmScratchTape).cells (sc_pos + 2 * p + 1) =
          Γ.ofBool ((simCellsFn simCfg ⟨target.val + p, by omega⟩
            (simHeadPos simCfg ⟨target.val + p, by omega⟩)).encode[1]'(by rw [Γ.encode_length]; omega))) ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      WorkTapesWF c'.work ∧
      t ≤ allTapesBound simCfg remaining target.val := by
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
      hsc_prev, hsc_above, hdesc', hstate', hinp', hout', hwf', ht'_bound⟩ :=
      per_tape_simulation (simCellsFn simCfg target) c target
        (simHeadPos simCfg target) sc_pos hstate hsim_head hmarker hhi hlo
        hsc_head hsc_ge hwf hinp hinp_h hout hout_h hsim_cell0 hwork_heads
    -- Case split: last tape or not?
    by_cases hlast : target.val = n + 1
    · -- Last tape (m = 0): per_tape_simulation reached .rewindState
      have hm0 : m = 0 := by omega
      subst hm0; simp [hlast] at hnext'
      refine ⟨c', t', hreach', hnext', hsim_head', hsim_cells', hdesc', hstate',
        by rw [hsc_head'], hsc_prev,
        fun j hj => hsc_above j (by omega),
        fun p hp => ?_, hinp', hout', hwf', ?_⟩
      · have hp0 : p = 0 := by omega
        subst hp0; simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
        exact ⟨hsc0, hsc1⟩
      · -- Time bound for last tape
        show t' ≤ allTapesBound simCfg (0 + 1) target.val
        simp only [allTapesBound]
        have : target.val < n + 2 := target.isLt
        rw [dif_pos this]
        omega
    · -- Not last tape: per_tape_simulation reached .scan ⟨target+1, _⟩, recurse
      simp [hlast] at hnext'
      have htarget1 : (⟨target.val + 1, by omega⟩ : Fin (n + 2)).val = n + 2 - m := by
        show target.val + 1 = n + 2 - m; omega
      obtain ⟨c'', t'', hreach'', hst'', hsim_head'', hsim_cells'', hdesc'', hstate'',
        hsc_head'', hsc_prev'', hsc_above'', hsc_vals'', hinp'', hout'', hwf'', ht''_bound⟩ :=
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
      refine ⟨c'', t' + t'', reachesIn_trans readCurrentTM hreach' hreach'', hst'',
        hsim_head'', by rw [hsim_cells'', hsim_cells'],
        by rw [hdesc'', hdesc'], by rw [hstate'', hstate'],
        by rw [hsc_head'']; omega,
        fun j hj => by rw [hsc_prev'' j (by omega), hsc_prev j hj],
        fun j hj => by rw [hsc_above'' j (by omega), hsc_above j (by omega)],
        fun p hp => ?_, by rw [hinp'', hinp'], by rw [hout'', hout'], hwf'', ?_⟩
      -- Prove the per-cell values for remaining = m + 1
      cases p with
      | zero =>
        simp only [Nat.mul_zero, Nat.add_zero]
        exact ⟨hsc_prev'' sc_pos (by omega) ▸ hsc0,
               hsc_prev'' (sc_pos + 1) (by omega) ▸ hsc1⟩
      | succ p' =>
        have hp' : p' < m := by omega
        have h := hsc_vals'' p' hp'
        have hfin : (⟨↑(⟨↑target + 1, by omega⟩ : Fin (n + 2)) + p',
            by show ↑target + 1 + p' < n + 2; omega⟩ : Fin (n + 2)) =
          ⟨↑target + (p' + 1), by omega⟩ :=
          Fin.ext (show ↑target + 1 + p' = ↑target + (p' + 1) by omega)
        simp only [hfin] at h
        constructor
        · rw [show sc_pos + 2 * (p' + 1) = sc_pos + 2 + 2 * p' from by omega]; exact h.1
        · rw [show sc_pos + 2 * (p' + 1) + 1 = sc_pos + 2 + 2 * p' + 1 from by omega]; exact h.2
      -- Time bound for recursive case
      · show t' + t'' ≤ allTapesBound simCfg (m + 1) target.val
        simp only [allTapesBound]
        have htlt : target.val < n + 2 := target.isLt
        rw [dif_pos htlt]
        have : (⟨target.val + 1, by omega⟩ : Fin (n + 2)).val = target.val + 1 := rfl
        have hfin_eq : (⟨target.val, htlt⟩ : Fin (n + 2)) = target := Fin.ext rfl
        calc t' + t''
            ≤ (2 * SuperCell.simTapeOffset (n + 2) (simHeadPos simCfg target) target.val + 7) +
              allTapesBound simCfg m (target.val + 1) :=
              Nat.add_le_add ht'_bound (by rw [show (⟨target.val + 1, by omega⟩ : Fin (n + 2)).val = target.val + 1 from rfl] at ht''_bound; exact ht''_bound)
          _ = _ := by rw [hfin_eq]


-- ════════════════════════════════════════════════════════════════════════
-- Helper lemmas for scratchHasInputPattern proof
-- ════════════════════════════════════════════════════════════════════════

/-- Length of flatMap of Γ.encode lists. -/
private lemma flatMap_encode_length {α : Type} (l : List α) (f : α → Γ) :
    (l.flatMap (fun x => (f x).encode)).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, Γ.encode_length, ih, List.length_cons]
    omega

/-- Length of encodeInputPattern equals k + 2*(n+2). -/
private lemma encodeInputPattern_length_eq (k n : ℕ) (q : Fin k) (iH : Γ)
    (wH : Fin n → Γ) (oH : Γ) :
    (TMEncoding.encodeInputPattern k n q iH wH oH).length = k + 2 * (n + 2) := by
  simp only [TMEncoding.encodeInputPattern, List.length_append, List.length_map,
             List.length_finRange, Γ.encode_length, flatMap_encode_length]
  omega

/-- Indexing into flatMap of Γ.encode lists: the (2m+b)-th element is
    the b-th encode bit of the m-th list element. -/
private lemma flatMap_encode_getElem {α : Type} (l : List α) (f : α → Γ)
    (m : ℕ) (hm : m < l.length) (b : ℕ) (hb : b < 2) :
    (l.flatMap (fun x => (f x).encode))[2 * m + b]'(by rw [flatMap_encode_length]; omega) =
    (f l[m]).encode[b]'(by rw [Γ.encode_length]; exact hb) := by
  induction l generalizing m with
  | nil => exact absurd hm (by simp)
  | cons a as ih =>
    simp only [List.flatMap_cons]
    match m with
    | 0 =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem_append_left (show b < (f a).encode.length by rw [Γ.encode_length]; exact hb)
    | m' + 1 =>
      rw [List.getElem_append_right
        (show (f a).encode.length ≤ 2 * (m' + 1) + b by rw [Γ.encode_length]; omega)]
      simp only [Γ.encode_length, show 2 * (m' + 1) + b - 2 = 2 * m' + b from by omega,
                  List.getElem_cons_succ]
      exact ih m' (by simp only [List.length_cons] at hm; omega)

/-- For tape-encoding indices i in [k, k + 2*(n+2)), the i-th bit of
    encodeInputPattern equals the b-th encode bit of the appropriate tape head,
    where p = (i-k)/2 selects the tape and b = (i-k)%2 selects the encode bit. -/
private lemma encodeInputPattern_tape_getElem (k n : ℕ) (q : Fin k) (iH : Γ)
    (wH : Fin n → Γ) (oH : Γ) (p b : ℕ) (hp : p < n + 2) (hb : b < 2) :
    let bits := TMEncoding.encodeInputPattern k n q iH wH oH
    (bits[k + (2 * p + b)]'(by rw [encodeInputPattern_length_eq]; omega)) =
    (if h₀ : p = 0 then iH
     else if h₁ : p ≤ n then wH ⟨p - 1, by omega⟩
     else oH).encode[b]'(by rw [Γ.encode_length]; omega) := by
  intro bits
  -- bits = stateMap ++ iH.encode ++ flatMap ++ oH.encode
  -- The stateMap has length k, so bits[k + (2*p+b)] = (iH.encode ++ flatMap ++ oH.encode)[2*p+b]
  show (TMEncoding.encodeInputPattern k n q iH wH oH)[k + (2 * p + b)]'(by
    rw [encodeInputPattern_length_eq]; omega) = _
  simp only [TMEncoding.encodeInputPattern, List.append_assoc]
  -- Now the LHS is ((map ++ (iH.encode ++ (flatMap ++ oH.encode))))[k + (2*p+b)]
  -- Skip past the map (length k)
  rw [List.getElem_append_right (show ((List.finRange k).map (· == q)).length ≤ k + (2 * p + b)
    from by simp [List.length_map, List.length_finRange])]
  simp only [List.length_map, List.length_finRange,
    show k + (2 * p + b) - k = 2 * p + b from by omega]
  -- Case split on p
  by_cases hp0 : p = 0
  · -- p = 0: indexing into iH.encode
    simp only [hp0, ↓reduceDIte, Nat.mul_zero, Nat.zero_add]
    exact List.getElem_append_left
      (show b < iH.encode.length by rw [Γ.encode_length]; exact hb)
  · by_cases hpn : p ≤ n
    · -- 1 ≤ p ≤ n: indexing into flatMap(wH)
      simp only [hp0, hpn, ↓reduceDIte]
      rw [List.getElem_append_right
        (show iH.encode.length ≤ 2 * p + b by rw [Γ.encode_length]; omega)]
      simp only [Γ.encode_length, show 2 * p + b - 2 = 2 * (p - 1) + b from by omega]
      -- Goal: (flatMap ++ oH.encode)[2*(p-1)+b] = (wH ⟨p-1,_⟩).encode[b]
      -- Since p ≤ n and p ≥ 1, 2*(p-1)+b < 2*n = flatMap.length
      rw [List.getElem_append_left
        (show 2 * (p - 1) + b <
            ((List.finRange n).flatMap (fun j => (wH j).encode)).length by
          rw [flatMap_encode_length, List.length_finRange]; omega)]
      have hpm : p - 1 < n := by omega
      rw [flatMap_encode_getElem _ _ (p - 1) (by simp [List.length_finRange]; exact hpm) b hb]
      simp only [List.getElem_finRange, Fin.cast_mk]
    · -- p = n + 1: indexing into oH.encode
      have hpeq : p = n + 1 := by omega
      simp only [hp0, show ¬(p ≤ n) from hpn, ↓reduceDIte]
      rw [List.getElem_append_right
        (show iH.encode.length ≤ 2 * p + b by rw [Γ.encode_length]; omega)]
      simp only [Γ.encode_length, show 2 * p + b - 2 = 2 * (p - 1) + b from by omega]
      -- Now we need (flatMap ++ oH.encode)[2*(p-1)+b], where p-1 = n, so index is 2*n + b
      -- flatMap has length 2*n, so we skip it to reach oH.encode[b]
      rw [List.getElem_append_right
        (show ((List.finRange n).flatMap (fun j => (wH j).encode)).length ≤
            2 * (p - 1) + b by
          rw [flatMap_encode_length, List.length_finRange, hpeq]; omega)]
      congr 1
      rw [flatMap_encode_length, List.length_finRange, hpeq]
      omega

-- ════════════════════════════════════════════════════════════════════════
-- Full readCurrentTM_hoareTime
-- ════════════════════════════════════════════════════════════════════════

/-- Total time bound for readCurrentTM:
    Phase 1 (copyState): k + 1 steps
    Phase 2 (all tapes): allTapesBound steps
    Phase 3a (rewindState): k + 3 steps
    Phase 3b (rewindScratch): k + 2*(n+2) + 3 steps -/
private noncomputable def readCurrentTimeBound {n : ℕ} {Q : Type} [DecidableEq Q] [Fintype Q]
    (k : ℕ) (simCfg : Cfg n Q) : ℕ :=
  (k + 1) + allTapesBound simCfg (n + 2) 0 + (k + 1 + 2) + (k + 1 + 2 * (n + 2) + 2)

/-- HoareTime specification for `readCurrentTM`.

    **Pre**: State and sim tapes encode `simCfg`; desc tape valid; all heads at 1;
    scratch tape cells ≥ 1 are blank (fresh scratch).
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
        (∀ j, j ≥ 1 → (work utmScratchTape).cells j = Γ.blank) ∧
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
  intro e
  -- Helper: tape index facts for `decide`
  have hne_desc_st : utmDescTape ≠ utmStateTape := by decide
  have hne_desc_sc : utmDescTape ≠ utmScratchTape := by decide
  have hne_st_sc : utmStateTape ≠ utmScratchTape := by decide
  have hne_sim_sc : utmSimTape ≠ utmScratchTape := by decide
  have hne_sim_st : utmSimTape ≠ utmStateTape := by decide
  have hne_desc_sim : utmDescTape ≠ utmSimTape := by decide
  -- Helper: classify Fin 4 into the 4 tape indices
  have fin4_cases : ∀ (i : Fin 4),
      i = utmDescTape ∨ i = utmStateTape ∨ i = utmSimTape ∨ i = utmScratchTape := by
    decide
  refine ⟨readCurrentTimeBound k simCfg, fun inp work out ⟨hdesc, hstate_tape, hscc, hdesc_h, hstate_h,
      hsim_h, hsc_h, hsc_blank, hwf, hinp_r, hinp_h, hout_r, hout_h⟩ => ?_⟩
  -- ── Phase 1: copyState ──────────────────────────────────────────────
  obtain ⟨c₁, hreach₁, hst₁, hst_head₁, hst_cells₁, hsc_head₁, hsc_cells₁, hsc_high₁,
      hsim_head₁, hsim_cells₁, hdesc₁, hinp₁, hout₁, hwf₁⟩ :=
    copyState_simulation
      ⟨(readCurrentTM (n := n)).qstart, inp, work, out⟩
      k (e simCfg.state) rfl hstate_h hsc_h hsim_h
      (show (work utmDescTape).head ≥ 1 by omega)
      hstate_tape hwf hinp_r hinp_h hout_r hout_h
  -- ── Phase 2: all_tapes ──────────────────────────────────────────────
  have hscc₁ : superCellsCorrect simCfg ⟨1, (c₁.work utmSimTape).cells⟩ := by
    rw [hsim_cells₁]; exact hscc
  have hwork_heads₁ : ∀ i, (c₁.work i).head ≥ 1 := by
    intro i; rcases fin4_cases i with rfl | rfl | rfl | rfl
    · have := congr_arg Tape.head hdesc₁; simp only [] at this; rw [this, hdesc_h]
    · omega
    · omega
    · omega
  obtain ⟨c₂, t₂, hreach₂, hst₂, hsim_head₂, hsim_cells₂, hdesc₂, hstate₂,
      hsc_head₂, hsc_prev₂, hsc_above₂, hsc_vals₂, hinp₂, hout₂, hwf₂, ht₂_bound⟩ :=
    all_tapes_simulation simCfg (n + 2) ⟨0, by omega⟩ (by simp) le_rfl c₁ (k + 1)
      hst₁ hsim_head₁ (by rw [hsim_cells₁]; exact hwf.1 utmSimTape) hscc₁
      hsc_head₁ (by omega) hwf₁
      (by rw [hinp₁]; exact hinp_r) (by rw [hinp₁]; exact hinp_h)
      (by rw [hout₁]; exact hout_r) (by rw [hout₁]; exact hout_h) hwork_heads₁
  -- ── Phase 3a: rewindState ───────────────────────────────────────────
  have hstate_head₂ : (c₂.work utmStateTape).head = k + 1 := by
    rw [hstate₂]; exact hst_head₁
  have hheads₂_ne : ∀ i, i ≠ utmStateTape → (c₂.work i).head ≥ 1 := by
    intro i hne; rcases fin4_cases i with rfl | rfl | rfl | rfl
    · have := congr_arg Tape.head hdesc₂; simp only [] at this; rw [this]
      exact hwork_heads₁ utmDescTape
    · exact absurd rfl hne
    · omega
    · rw [hsc_head₂]; omega
  obtain ⟨c₃, hreach₃, hst₃, hstate_head₃, hstate_cells₃, hother₃, hinp₃, hout₃, hwf₃⟩ :=
    rewindState_simulation (k + 1) c₂ hst₂ hstate_head₂ hwf₂
      (by rw [hinp₂, hinp₁]; exact hinp_r) (by rw [hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₂, hout₁]; exact hout_r) (by rw [hout₂, hout₁]; exact hout_h)
      hheads₂_ne
  -- ── Phase 3b: rewindScratch ─────────────────────────────────────────
  have hsc_head₃ : (c₃.work utmScratchTape).head = k + 1 + 2 * (n + 2) := by
    rw [hother₃ utmScratchTape hne_st_sc.symm]; exact hsc_head₂
  have hheads₃_ne : ∀ i, i ≠ utmScratchTape → (c₃.work i).head ≥ 1 := by
    intro i hne; rcases fin4_cases i with rfl | rfl | rfl | rfl
    · rw [hother₃ utmDescTape hne_desc_st]; exact hheads₂_ne utmDescTape hne_desc_st
    · omega
    · rw [hother₃ utmSimTape hne_sim_st]; omega
    · exact absurd rfl hne
  obtain ⟨c₄, hreach₄, hhalted₄, hsc_head₄, hsc_cells₄, hother₄, hinp₄, hout₄, hwf₄⟩ :=
    rewindScratch_simulation (k + 1 + 2 * (n + 2)) c₃ hst₃ hsc_head₃ hwf₃
      (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_r) (by rw [hinp₃, hinp₂, hinp₁]; exact hinp_h)
      (by rw [hout₃, hout₂, hout₁]; exact hout_r) (by rw [hout₃, hout₂, hout₁]; exact hout_h)
      hheads₃_ne
  -- ── Compose all phases ──────────────────────────────────────────────
  have hreaches := reachesIn_trans readCurrentTM hreach₁
    (reachesIn_trans readCurrentTM hreach₂
      (reachesIn_trans readCurrentTM hreach₃ hreach₄))
  refine ⟨c₄, _, ?_, hreaches, hhalted₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Time bound
  · show k + 1 + (t₂ + (k + 1 + 2 + (k + 1 + 2 * (n + 2) + 2))) ≤ readCurrentTimeBound k simCfg
    unfold readCurrentTimeBound
    have : (⟨0, by omega⟩ : Fin (n + 2)).val = 0 := rfl
    rw [this] at ht₂_bound
    omega
  -- Post 1: descOnTape
  · rw [hother₄ utmDescTape hne_desc_sc, hother₃ utmDescTape hne_desc_st,
        hdesc₂, hdesc₁]; exact hdesc
  -- Post 2: stateOnTapeAt
  · have hcells : (c₄.work utmStateTape).cells = (work utmStateTape).cells := by
      rw [hother₄ utmStateTape hne_st_sc]
      show (c₃.work utmStateTape).cells = _
      rw [hstate_cells₃, hstate₂, hst_cells₁]
    have hhead : (c₄.work utmStateTape).head = 1 := by
      rw [hother₄ utmStateTape hne_st_sc]; exact hstate_head₃
    show stateOnTapeAt k (e simCfg.state) (c₄.work utmStateTape)
    simp only [stateOnTapeAt, hcells, hhead]
    simp only [stateOnTapeAt, hstate_h] at hstate_tape
    exact hstate_tape
  -- Post 3: superCellsCorrect
  · have hcells : (c₄.work utmSimTape).cells = (work utmSimTape).cells := by
      rw [hother₄ utmSimTape hne_sim_sc, hother₃ utmSimTape hne_sim_st,
          hsim_cells₂, hsim_cells₁]
    show superCellsCorrect simCfg (c₄.work utmSimTape)
    unfold superCellsCorrect simTapeCellCorrect at hscc ⊢
    simp only [hcells]; exact hscc
  -- Post 4: scratchHasInputPattern
  · -- Establish cell chain: c₄ scratch cells = c₂ scratch cells
    have h_sc₃₂ : c₃.work utmScratchTape = c₂.work utmScratchTape :=
      hother₃ utmScratchTape (Ne.symm hne_st_sc)
    have hcc : ∀ j, (c₄.work utmScratchTape).cells j =
        (c₂.work utmScratchTape).cells j := by
      intro j; exact congr_fun hsc_cells₄ j ▸ congr_fun (congr_arg Tape.cells h_sc₃₂) j
    refine ⟨⟨hwf₄.1 utmScratchTape, ?_, ?_⟩, hsc_head₄⟩
    · -- Per-cell: ∀ i < bits.length, cells(i+1) = Γ.ofBool bits[i]
      intro i hi
      rw [encodeInputPattern_length_eq] at hi
      by_cases hik : i < k
      · -- State bits (i < k)
        rw [hcc, hsc_prev₂ (i + 1) (by omega), hsc_cells₁ i hik]; symm
        simp only [TMEncoding.encodeInputPattern, List.append_assoc]
        rw [List.getElem_append_left (show i < ((List.finRange k).map (· == e simCfg.state)).length
          from by simp [List.length_map, List.length_finRange]; omega)]
        rw [List.getElem_map, List.getElem_finRange]
        simp only [Fin.cast_mk, Γ.ofBool]
        by_cases h : i = (e simCfg.state).val
        · have : ((⟨i, hik⟩ : Fin k) == e simCfg.state) = true := by
            rw [beq_iff_eq, Fin.ext_iff]; exact h
          simp [h]
        · have : ((⟨i, hik⟩ : Fin k) == e simCfg.state) = false := by
            rw [beq_eq_false_iff_ne]; exact fun heq => h (Fin.ext_iff.mp heq)
          simp [this, h]

      · -- Tape encoding bits (i ≥ k)
        push_neg at hik
        have hp : (i - k) / 2 < n + 2 := by omega
        have hvals := hsc_vals₂ ((i - k) / 2) hp
        -- Normalize the ↑⟨0, ⋯⟩ + p to just p in hvals
        simp only [Nat.zero_add] at hvals
        -- Connect simCellsFn/simHeadPos to encodeInputPattern via tape_getElem
        have h_sim_eq : simCellsFn simCfg ⟨(i - k) / 2, by omega⟩
            (simHeadPos simCfg ⟨(i - k) / 2, by omega⟩) =
            (if h₀ : (i - k) / 2 = 0 then simCfg.input.read
             else if h₁ : (i - k) / 2 ≤ n then
               (simCfg.work ⟨(i - k) / 2 - 1, by omega⟩).read
             else simCfg.output.read) := by
          simp only [simCellsFn, simHeadPos, Tape.read]
          split <;> [rfl; split <;> rfl]
        -- Show cell(i+1) = cell in c₂ at the right position
        rw [hcc, show i + 1 = k + 1 + 2 * ((i - k) / 2) + (i - k) % 2 from by omega]
        rcases Nat.mod_two_eq_zero_or_one (i - k) with h0 | h1
        · -- b = 0
          rw [h0, Nat.add_zero]; rw [hvals.1]; congr 1
          have h_tape := encodeInputPattern_tape_getElem k n (e simCfg.state)
            simCfg.input.read (fun j => (simCfg.work j).read) simCfg.output.read
            ((i - k) / 2) 0 hp (by omega)
          simp only [h_sim_eq]; convert h_tape.symm using 2; omega
        · -- b = 1
          rw [h1]; rw [hvals.2]; congr 1
          have h_tape := encodeInputPattern_tape_getElem k n (e simCfg.state)
            simCfg.input.read (fun j => (simCfg.work j).read) simCfg.output.read
            ((i - k) / 2) 1 hp (by omega)
          simp only [h_sim_eq]; convert h_tape.symm using 2; omega
    · -- Sentinel blank: cells(bits.length + 1) = Γ.blank
      rw [encodeInputPattern_length_eq, hcc, hsc_above₂ _ (by omega),
          hsc_high₁ _ (by omega)]
      exact hsc_blank _ (by omega)
  -- Post 5: desc head = 1
  · rw [hother₄ utmDescTape hne_desc_sc, hother₃ utmDescTape hne_desc_st, hdesc₂, hdesc₁]
    exact hdesc_h
  -- Post 6: state head = 1
  · rw [hother₄ utmStateTape hne_st_sc]; exact hstate_head₃
  -- Post 7: sim head = 1
  · rw [hother₄ utmSimTape hne_sim_sc, hother₃ utmSimTape hne_sim_st]; exact hsim_head₂
  -- Post 8: WorkTapesWF
  · exact hwf₄

end TM
