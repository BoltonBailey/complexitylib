import Complexitylib.Models.TuringMachine.UTM.CheckHalt
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# CheckHalt proof internals

Step-by-step simulation lemmas for `skipToQhaltTM` and `compareWriteTM`.
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem readBackWrite_toΓ_eq' {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem tape_move_cells' (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

-- tape_idle_preserve is now public in HelpersInternal.lean

-- ════════════════════════════════════════════════════════════════════════
-- Single-step lemmas for skip phases
-- ════════════════════════════════════════════════════════════════════════

/-- A single step in skipK when reading one: stay in skipK. -/
private theorem skipK_step_one (c : Cfg 4 skipToQhaltTM.Q)
    (hstate : c.state = .skipK)
    (hread : (c.work (0 : Fin 4)).read = Γ.one)
    (hhead : (c.work 0).head ≥ 1)
    (hnostart : (c.work (0 : Fin 4)).read ≠ Γ.start)
    (hother : ∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houth : c.output.head ≥ 1) :
    ∃ c',
      skipToQhaltTM.step c = some c' ∧
      c'.state = .skipK ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) = Γ.one := hread
  simp only [TM.step, hstate, skipToQhaltTM, ↓reduceIte, hread_eq]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, Tape.move, Tape.write]
    split <;> (first | omega | rfl)
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, tape_move_cells', Tape.write]
    split
    · rfl
    · rw [readBackWrite_toΓ_eq' hnostart]; exact Function.update_eq_self _ _
  · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  · exact tape_idle_preserve c.output hout houth
  · intro i hne
    have : ¬(↑i = (0 : ℕ)) := fun h => hne (by ext; exact h)
    dsimp only []; simp only [this, ↓reduceIte]
    exact tape_idle_preserve (c.work i) (hother i hne).1 (hother i hne).2

/-- A single step in skipK when reading non-one: transition to skipN. -/
private theorem skipK_step_notone (c : Cfg 4 skipToQhaltTM.Q)
    (hstate : c.state = .skipK)
    (hread : (c.work (0 : Fin 4)).read ≠ Γ.one)
    (hhead : (c.work 0).head ≥ 1)
    (hnostart : (c.work (0 : Fin 4)).read ≠ Γ.start)
    (hother : ∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houth : c.output.head ≥ 1) :
    ∃ c',
      skipToQhaltTM.step c = some c' ∧
      c'.state = .skipN ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  have hread_ne : (fun i => (c.work i).read) (0 : Fin 4) ≠ Γ.one := hread
  simp only [TM.step, hstate, skipToQhaltTM, ↓reduceIte, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, Tape.move, Tape.write]
    split <;> (first | omega | rfl)
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, tape_move_cells', Tape.write]
    split
    · rfl
    · rw [readBackWrite_toΓ_eq' hnostart]; exact Function.update_eq_self _ _
  · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  · exact tape_idle_preserve c.output hout houth
  · intro i hne
    have : ¬(↑i = (0 : ℕ)) := fun h => hne (by ext; exact h)
    dsimp only []; simp only [this, ↓reduceIte]
    exact tape_idle_preserve (c.work i) (hother i hne).1 (hother i hne).2

/-- A single step in skipN when reading one: stay in skipN. -/
private theorem skipN_step_one (c : Cfg 4 skipToQhaltTM.Q)
    (hstate : c.state = .skipN)
    (hread : (c.work (0 : Fin 4)).read = Γ.one)
    (hhead : (c.work 0).head ≥ 1)
    (hnostart : (c.work (0 : Fin 4)).read ≠ Γ.start)
    (hother : ∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houth : c.output.head ≥ 1) :
    ∃ c',
      skipToQhaltTM.step c = some c' ∧
      c'.state = .skipN ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) = Γ.one := hread
  simp only [TM.step, hstate, skipToQhaltTM, ↓reduceIte, hread_eq]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, Tape.move, Tape.write]
    split <;> (first | omega | rfl)
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, tape_move_cells', Tape.write]
    split
    · rfl
    · rw [readBackWrite_toΓ_eq' hnostart]; exact Function.update_eq_self _ _
  · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  · exact tape_idle_preserve c.output hout houth
  · intro i hne
    have : ¬(↑i = (0 : ℕ)) := fun h => hne (by ext; exact h)
    dsimp only []; simp only [this, ↓reduceIte]
    exact tape_idle_preserve (c.work i) (hother i hne).1 (hother i hne).2

/-- A single step in skipN when reading non-one: transition to done (halt). -/
private theorem skipN_step_notone (c : Cfg 4 skipToQhaltTM.Q)
    (hstate : c.state = .skipN)
    (hread : (c.work (0 : Fin 4)).read ≠ Γ.one)
    (hhead : (c.work 0).head ≥ 1)
    (hnostart : (c.work (0 : Fin 4)).read ≠ Γ.start)
    (hother : ∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houth : c.output.head ≥ 1) :
    ∃ c',
      skipToQhaltTM.step c = some c' ∧
      skipToQhaltTM.halted c' ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  have hread_ne : (fun i => (c.work i).read) (0 : Fin 4) ≠ Γ.one := hread
  simp only [TM.step, hstate, skipToQhaltTM, ↓reduceIte, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, Tape.move, Tape.write]
    split <;> (first | omega | rfl)
  · dsimp only []
    simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
      Tape.writeAndMove, tape_move_cells', Tape.write]
    split
    · rfl
    · rw [readBackWrite_toΓ_eq' hnostart]; exact Function.update_eq_self _ _
  · simp only [idleDir, hinp, ↓reduceIte, Tape.move]
  · exact tape_idle_preserve c.output hout houth
  · intro i hne
    have : ¬(↑i = (0 : ℕ)) := fun h => hne (by ext; exact h)
    dsimp only []; simp only [this, ↓reduceIte]
    exact tape_idle_preserve (c.work i) (hother i hne).1 (hother i hne).2

-- ════════════════════════════════════════════════════════════════════════
-- Scan loops for skipToQhaltTM
-- ════════════════════════════════════════════════════════════════════════

/-- Scan past `count` ones + 1 separator in skipK phase. -/
private theorem skipK_scan :
    ∀ (count : ℕ) (c : Cfg 4 skipToQhaltTM.Q),
    c.state = .skipK →
    (∀ j, j < count → (c.work 0).cells ((c.work 0).head + j) = Γ.one) →
    (c.work 0).cells ((c.work 0).head + count) ≠ Γ.one →
    (c.work 0).head ≥ 1 →
    (∀ p, p ≥ 1 → (c.work 0).cells p ≠ Γ.start) →
    (∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      skipToQhaltTM.reachesIn (count + 1) c c' ∧
      c'.state = .skipN ∧
      (c'.work 0).head = (c.work 0).head + count + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  intro count; induction count with
  | zero =>
    intro c hstate _ hnotone hhead hnostart hother hinp hout houth
    simp only [Nat.add_zero] at hnotone
    have hread_ne : (c.work (0 : Fin 4)).read ≠ Γ.one := by
      simp only [Tape.read]; exact hnotone
    have hread_ns : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hnostart _ hhead
    obtain ⟨c', hstep, hst, hh, hc, hi, ho, hw⟩ :=
      skipK_step_notone c hstate hread_ne hhead hread_ns hother hinp hout houth
    exact ⟨c', .step hstep .zero, hst, by simp [hh], hc, hi, ho, hw⟩
  | succ n ih =>
    intro c hstate hones hnotone hhead hnostart hother hinp hout houth
    have hread_one : (c.work (0 : Fin 4)).read = Γ.one := by
      simp only [Tape.read]; exact hones 0 (by omega)
    have hread_ns : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hnostart _ hhead
    obtain ⟨c', hstep, hst, hh, hc, hi, ho, hw⟩ :=
      skipK_step_one c hstate hread_one hhead hread_ns hother hinp hout houth
    obtain ⟨c_f, hreach, hst_f, hh_f, hc_f, hi_f, ho_f, hw_f⟩ := ih c' hst
      (by intro j hj; rw [hc, hh]
          have : (c.work 0).head + 1 + j = (c.work 0).head + (j + 1) := by omega
          rw [this]; exact hones (j + 1) (by omega))
      (by rw [hc, hh]
          have : (c.work 0).head + 1 + n = (c.work 0).head + (n + 1) := by omega
          rw [this]; exact hnotone)
      (by omega)
      (by rwa [hc])
      (by intro i hne; rw [hw i hne]; exact hother i hne)
      (by rwa [hi])
      (by rwa [ho])
      (by rw [ho]; exact houth)
    exact ⟨c_f, .step hstep hreach, hst_f,
      by rw [hh_f, hh]; omega,
      by rw [hc_f, hc],
      by rw [hi_f, hi],
      by rw [ho_f, ho],
      fun i hne => by rw [hw_f i hne, hw i hne]⟩

/-- Scan past `count` ones + 1 separator in skipN phase. -/
private theorem skipN_scan :
    ∀ (count : ℕ) (c : Cfg 4 skipToQhaltTM.Q),
    c.state = .skipN →
    (∀ j, j < count → (c.work 0).cells ((c.work 0).head + j) = Γ.one) →
    (c.work 0).cells ((c.work 0).head + count) ≠ Γ.one →
    (c.work 0).head ≥ 1 →
    (∀ p, p ≥ 1 → (c.work 0).cells p ≠ Γ.start) →
    (∀ i, i ≠ (0 : Fin 4) → (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    ∃ c',
      skipToQhaltTM.reachesIn (count + 1) c c' ∧
      skipToQhaltTM.halted c' ∧
      (c'.work 0).head = (c.work 0).head + count + 1 ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c.work i) := by
  intro count; induction count with
  | zero =>
    intro c hstate _ hnotone hhead hnostart hother hinp hout houth
    simp only [Nat.add_zero] at hnotone
    have hread_ne : (c.work (0 : Fin 4)).read ≠ Γ.one := by
      simp only [Tape.read]; exact hnotone
    have hread_ns : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hnostart _ hhead
    obtain ⟨c', hstep, hhalt, hh, hc, hi, ho, hw⟩ :=
      skipN_step_notone c hstate hread_ne hhead hread_ns hother hinp hout houth
    exact ⟨c', .step hstep .zero, hhalt, by simp [hh], hc, hi, ho, hw⟩
  | succ n ih =>
    intro c hstate hones hnotone hhead hnostart hother hinp hout houth
    have hread_one : (c.work (0 : Fin 4)).read = Γ.one := by
      simp only [Tape.read]; exact hones 0 (by omega)
    have hread_ns : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hnostart _ hhead
    obtain ⟨c', hstep, hst, hh, hc, hi, ho, hw⟩ :=
      skipN_step_one c hstate hread_one hhead hread_ns hother hinp hout houth
    obtain ⟨c_f, hreach, hhalt_f, hh_f, hc_f, hi_f, ho_f, hw_f⟩ := ih c' hst
      (by intro j hj; rw [hc, hh]
          have : (c.work 0).head + 1 + j = (c.work 0).head + (j + 1) := by omega
          rw [this]; exact hones (j + 1) (by omega))
      (by rw [hc, hh]
          have : (c.work 0).head + 1 + n = (c.work 0).head + (n + 1) := by omega
          rw [this]; exact hnotone)
      (by omega)
      (by rwa [hc])
      (by intro i hne; rw [hw i hne]; exact hother i hne)
      (by rwa [hi])
      (by rwa [ho])
      (by rw [ho]; exact houth)
    exact ⟨c_f, .step hstep hreach, hhalt_f,
      by rw [hh_f, hh]; omega,
      by rw [hc_f, hc],
      by rw [hi_f, hi],
      by rw [ho_f, ho],
      fun i hne => by rw [hw_f i hne, hw i hne]⟩

-- ════════════════════════════════════════════════════════════════════════
-- skipToQhaltTM: full HoareTime
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for skipToQhaltTM: navigates desc from cell 1 past the header
    (k ones + sep + n ones + sep) to the qhalt one-hot.
    After halting, desc head is at cell `hk + hn + 3`. -/
theorem skipToQhaltTM_hoareTime (hk hn : ℕ)
    (c_init : Cfg 4 skipToQhaltTM.Q)
    (hstate : c_init.state = .skipK)
    (hdesc_head : (c_init.work 0).head = 1)
    (hones1 : ∀ j, j < hk → (c_init.work 0).cells (1 + j) = Γ.one)
    (hsep1 : (c_init.work 0).cells (1 + hk) ≠ Γ.one)
    (hones2 : ∀ j, j < hn → (c_init.work 0).cells (hk + 2 + j) = Γ.one)
    (hsep2 : (c_init.work 0).cells (hk + 2 + hn) ≠ Γ.one)
    (hnostart : ∀ p, p ≥ 1 → (c_init.work 0).cells p ≠ Γ.start)
    (hother : ∀ i, i ≠ (0 : Fin 4) → (c_init.work i).read ≠ Γ.start ∧ (c_init.work i).head ≥ 1)
    (hinp : c_init.input.read ≠ Γ.start)
    (hout : c_init.output.read ≠ Γ.start) (houth : c_init.output.head ≥ 1) :
    ∃ c',
      skipToQhaltTM.reachesIn (hk + hn + 2) c_init c' ∧
      skipToQhaltTM.halted c' ∧
      (c'.work 0).head = hk + hn + 3 ∧
      (c'.work 0).cells = (c_init.work 0).cells ∧
      c'.input = c_init.input ∧ c'.output = c_init.output ∧
      (∀ i, i ≠ (0 : Fin 4) → c'.work i = c_init.work i) := by
  -- Phase 1: skipK scans past k ones
  obtain ⟨c_mid, hreach1, hst_mid, hhead_mid, hcells_mid, hinp_mid, hout_mid, hwork_mid⟩ :=
    skipK_scan hk c_init hstate
      (by intro j hj; rw [hdesc_head]; exact hones1 j hj)
      (by rw [hdesc_head]; exact hsep1)
      (by omega)
      hnostart hother hinp hout houth
  -- Phase 2: skipN scans past n ones
  obtain ⟨c_final, hreach2, hhalt, hhead_final, hcells_final, hinp_f, hout_f, hwork_f⟩ :=
    skipN_scan hn c_mid hst_mid
      (by intro j hj; rw [hcells_mid, hhead_mid, hdesc_head]
          have : 1 + hk + 1 + j = hk + 2 + j := by omega
          rw [this]; exact hones2 j hj)
      (by rw [hcells_mid, hhead_mid, hdesc_head]
          have : 1 + hk + 1 + hn = hk + 2 + hn := by omega
          rw [this]; exact hsep2)
      (by omega)
      (by rwa [hcells_mid])
      (by intro i hne; rw [hwork_mid i hne]; exact hother i hne)
      (by rwa [hinp_mid])
      (by rwa [hout_mid])
      (by rw [hout_mid]; exact houth)
  refine ⟨c_final, ?_, hhalt,
    by rw [hhead_final, hhead_mid, hdesc_head]; omega,
    by rw [hcells_final, hcells_mid],
    by rw [hinp_f, hinp_mid],
    by rw [hout_f, hout_mid],
    fun i hne => by rw [hwork_f i hne, hwork_mid i hne]⟩
  have : hk + 1 + (hn + 1) = hk + hn + 2 := by omega
  rw [← this]
  exact reachesIn_trans _ hreach1 hreach2

-- ════════════════════════════════════════════════════════════════════════
-- compareWriteTM: tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Output head is preserved when writing blank with idleDir (stay). -/
private theorem output_head_idle (out : Tape) (hns : out.read ≠ Γ.start)
    (_hh : out.head ≥ 1) :
    (out.writeAndMove Γw.blank.toΓ (idleDir out.read)).head = out.head := by
  simp only [Tape.writeAndMove, Γw.toΓ, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split <;> rfl

/-- Output cells 0 is preserved when writing blank with idleDir (head ≥ 1). -/
private theorem output_cells0_idle (out : Tape) (hns : out.read ≠ Γ.start)
    (hh : out.head ≥ 1) :
    (out.writeAndMove Γw.blank.toΓ (idleDir out.read)).cells 0 = out.cells 0 := by
  simp only [Tape.writeAndMove, Γw.toΓ, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · rfl
  · show (Function.update out.cells out.head Γ.blank) 0 = out.cells 0
    rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ out.head)]

/-- Output cells ≥ 1 remain ≠ ▷ after writing blank with idleDir. -/
private theorem output_cellsNS_idle (out : Tape) (hns : out.read ≠ Γ.start)
    (_hh : out.head ≥ 1) (hons : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start) :
    ∀ j, j ≥ 1 → (out.writeAndMove Γw.blank.toΓ (idleDir out.read)).cells j ≠ Γ.start := by
  intro j hj
  simp only [Tape.writeAndMove, Γw.toΓ, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · exact hons j hj
  · show (Function.update out.cells out.head Γ.blank) j ≠ Γ.start
    by_cases heq : j = out.head
    · subst heq; rw [Function.update_self]; decide
    · rw [Function.update_of_ne heq]; exact hons j hj

/-- Output read ≠ ▷ after writing blank with idleDir. -/
private theorem output_readNS_idle (out : Tape) (hns : out.read ≠ Γ.start)
    (_hh : out.head ≥ 1) (_hons : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start) :
    (out.writeAndMove Γw.blank.toΓ (idleDir out.read)).read ≠ Γ.start := by
  have hns' : out.cells out.head ≠ Γ.start := by rw [← Tape.read]; exact hns
  have hdir : idleDir (out.cells out.head) = Dir3.stay := by simp [idleDir, hns']
  simp only [Tape.read, Tape.writeAndMove, Γw.toΓ, hdir, Tape.move, Tape.write,
    show out.head ≠ 0 from by omega, ↓reduceIte]
  show (Function.update out.cells out.head Γ.blank) out.head ≠ Γ.start
  rw [Function.update_self]; decide

-- ════════════════════════════════════════════════════════════════════════
-- compareWriteTM: compare scan (all match → rewindOutM)
-- ════════════════════════════════════════════════════════════════════════

/-- Comparison loop: scan past `count` matching cells, then sentinel → rewindOutM.
    Both desc (work 0) and state (work 1) advance right together. -/
private theorem compare_match_scan :
    ∀ (count : ℕ) (c : Cfg 4 compareWriteTM.Q),
    c.state = .compare →
    (∀ j, j < count → (c.work (0 : Fin 4)).cells ((c.work 0).head + j) =
                        (c.work (1 : Fin 4)).cells ((c.work 1).head + j)) →
    (∀ j, j < count → (c.work (1 : Fin 4)).cells ((c.work 1).head + j) ≠ Γ.blank) →
    (c.work (1 : Fin 4)).cells ((c.work 1).head + count) = Γ.blank →
    (c.work (0 : Fin 4)).head ≥ 1 →
    (c.work (1 : Fin 4)).head ≥ 1 →
    (∀ p, p ≥ 1 → (c.work (0 : Fin 4)).cells p ≠ Γ.start) →
    (∀ p, p ≥ 1 → (c.work (1 : Fin 4)).cells p ≠ Γ.start) →
    (∀ i : Fin 4, i ≠ 0 → i ≠ 1 →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    ∃ c',
      compareWriteTM.reachesIn (count + 1) c c' ∧
      c'.state = .rewindOutM ∧
      (c'.work (0 : Fin 4)).cells = (c.work 0).cells ∧
      (c'.work (1 : Fin 4)).cells = (c.work 1).cells ∧
      c'.input = c.input ∧
      c'.output.head = c.output.head ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
      (c'.work (0 : Fin 4)).head = (c.work (0 : Fin 4)).head + count ∧
      (c'.work (1 : Fin 4)).head = (c.work (1 : Fin 4)).head + count ∧
      (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
  intro count; induction count with
  | zero =>
    intro c hstate _ _ hsentinel hh0 hh1 hns0 hns1 hother hinp hout houth hoc0 hons
    simp only [Nat.add_zero] at hsentinel
    have hns_r0 : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns0 _ hh0
    have hns_r1 : (c.work (1 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns1 _ hh1
    have hread1_blank : (fun i => (c.work i).read) (1 : Fin 4) = Γ.blank := by
      simp only [Tape.read]; exact hsentinel
    -- Prove the step produces the right configuration
    have hstep : ∃ c',
        compareWriteTM.step c = some c' ∧
        c'.state = .rewindOutM ∧
        (c'.work 0).cells = (c.work 0).cells ∧
        (c'.work 1).cells = (c.work 1).cells ∧
        c'.input = c.input ∧
        c'.output.head = c.output.head ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
        (c'.work (0 : Fin 4)).head = (c.work (0 : Fin 4)).head ∧
        (c'.work (1 : Fin 4)).head = (c.work (1 : Fin 4)).head ∧
        (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
      simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread1_blank]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        rw [tape_idle_preserve (c.work 0) hns_r0 hh0]
      · dsimp only []
        rw [tape_idle_preserve (c.work 1) hns_r1 hh1]
      · dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · dsimp only []; exact output_head_idle c.output hout houth
      · dsimp only []; exact (output_cells0_idle c.output hout houth).trans hoc0
      · dsimp only []; exact output_cellsNS_idle c.output hout houth hons
      · dsimp only []; show _ = (c.work 0).head
        rw [tape_idle_preserve (c.work 0) hns_r0 hh0]
      · dsimp only []; show _ = (c.work 1).head
        rw [tape_idle_preserve (c.work 1) hns_r1 hh1]
      · intro i hne0 hne1; dsimp only []
        exact tape_idle_preserve (c.work i) (hother i hne0 hne1).1 (hother i hne0 hne1).2
    obtain ⟨c', hstep_eq, hst, hc0, hc1, hinp', hoh, hoc0', hons', hh0_eq, hh1_eq, hw⟩ := hstep
    exact ⟨c', .step hstep_eq .zero, hst, hc0, hc1, hinp', hoh, hoc0', hons',
      by simp [hh0_eq], by simp [hh1_eq], hw⟩
  | succ n ih =>
    intro c hstate hmatch hnotblank hsentinel hh0 hh1 hns0 hns1 hother hinp hout houth hoc0 hons
    have hns_r0 : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns0 _ hh0
    have hns_r1 : (c.work (1 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns1 _ hh1
    -- State tape reads non-blank (not sentinel yet)
    have hread1_ne : (fun i => (c.work i).read) (1 : Fin 4) ≠ Γ.blank := by
      simp only [Tape.read]; exact hnotblank 0 (by omega)
    -- Both tapes match at current position
    have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) =
        (fun i => (c.work i).read) (1 : Fin 4) := by
      simp only [Tape.read]; exact hmatch 0 (by omega)
    -- Prove the match step
    have hstep : ∃ c',
        compareWriteTM.step c = some c' ∧
        c'.state = .compare ∧
        (c'.work 0).head = (c.work 0).head + 1 ∧
        (c'.work 0).cells = (c.work 0).cells ∧
        (c'.work 1).head = (c.work 1).head + 1 ∧
        (c'.work 1).cells = (c.work 1).cells ∧
        c'.input = c.input ∧
        c'.output.head = c.output.head ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
        c'.output.read ≠ Γ.start ∧
        (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
      simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread1_ne, hread_eq]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- work 0 head
        dsimp only []
        simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write]
        split <;> (first | omega | rfl)
      · -- work 0 cells
        dsimp only []
        simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
          Tape.writeAndMove, tape_move_cells', Tape.write]
        split
        · rfl
        · rw [readBackWrite_toΓ_eq' hns_r0]; exact Function.update_eq_self _ _
      · -- work 1 head
        dsimp only []
        simp only [show (↑(1 : Fin 4) : ℕ) = 1 from rfl,
          show ¬((1 : ℕ) = 0) from by omega, ↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write]
        split <;> (first | omega | rfl)
      · -- work 1 cells
        dsimp only []
        simp only [show (↑(1 : Fin 4) : ℕ) = 1 from rfl,
          show ¬((1 : ℕ) = 0) from by omega, ↓reduceIte,
          Tape.writeAndMove, tape_move_cells', Tape.write]
        split
        · rfl
        · rw [readBackWrite_toΓ_eq' hns_r1]; exact Function.update_eq_self _ _
      · -- input
        dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · -- output head
        dsimp only []; exact output_head_idle c.output hout houth
      · -- output cells 0
        dsimp only []; exact (output_cells0_idle c.output hout houth).trans hoc0
      · -- output cells ≥ 1 ≠ start
        dsimp only []; exact output_cellsNS_idle c.output hout houth hons
      · -- output read ≠ start
        dsimp only []; exact output_readNS_idle c.output hout houth hons
      · -- other work tapes
        intro i hne0 hne1; dsimp only []
        have : ¬(↑i = (0 : ℕ)) := fun h => hne0 (by ext; exact h)
        have : ¬(↑i = (1 : ℕ)) := fun h => hne1 (by ext; exact h)
        simp only [*, ↓reduceIte]
        exact tape_idle_preserve (c.work i) (hother i hne0 hne1).1 (hother i hne0 hne1).2
    obtain ⟨c', hstep_eq, hst', hh0', hc0', hh1', hc1', hinp', hoh', hoc0'', hons'', hout_ns', hw'⟩ := hstep
    -- Apply IH to c'
    obtain ⟨c_f, hreach_f, hst_f, hcf0, hcf1, hinp_f, hoh_f, hoc0_f, hons_f, hh0_f, hh1_f, hw_f⟩ := ih c' hst'
      (by intro j hj; rw [hc0', hh0', hc1', hh1']
          have : (c.work 0).head + 1 + j = (c.work 0).head + (j + 1) := by omega
          have : (c.work 1).head + 1 + j = (c.work 1).head + (j + 1) := by omega
          rw [‹(c.work 0).head + 1 + j = _›, ‹(c.work 1).head + 1 + j = _›]
          exact hmatch (j + 1) (by omega))
      (by intro j hj; rw [hc1', hh1']
          have : (c.work 1).head + 1 + j = (c.work 1).head + (j + 1) := by omega
          rw [this]; exact hnotblank (j + 1) (by omega))
      (by rw [hc1', hh1']
          have : (c.work 1).head + 1 + n = (c.work 1).head + (n + 1) := by omega
          rw [this]; exact hsentinel)
      (by omega) (by omega)
      (by rwa [hc0'])
      (by rwa [hc1'])
      (by intro i hne0 hne1; rw [hw' i hne0 hne1]; exact hother i hne0 hne1)
      (by rwa [hinp'])
      hout_ns' (by rw [hoh']; exact houth)
      hoc0'' hons''
    exact ⟨c_f, .step hstep_eq hreach_f, hst_f,
      by rw [hcf0, hc0'],
      by rw [hcf1, hc1'],
      by rw [hinp_f, hinp'],
      by rw [hoh_f, hoh'],
      hoc0_f, hons_f,
      by rw [hh0_f, hh0']; omega, by rw [hh1_f, hh1']; omega,
      fun i hne0 hne1 => by rw [hw_f i hne0 hne1, hw' i hne0 hne1]⟩

-- ════════════════════════════════════════════════════════════════════════
-- compareWriteTM: rewind output + write
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind output tape from head position h to cell 1, then write sym and halt.
    Covers both match (rewindOutM → writeM → done, sym = .one) and
    mismatch (rewindOutD → writeD → done, sym = .zero) cases. -/
private theorem compareWriteTM_rewind_write
    (is_match : Bool) (c : Cfg 4 compareWriteTM.Q)
    (hstate : c.state = if is_match then .rewindOutM else .rewindOutD)
    (hoc0 : c.output.cells 0 = Γ.start)
    (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hns_work : ∀ i : Fin 4, (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start) :
    ∃ c',
      compareWriteTM.reachesIn (c.output.head + 2) c c' ∧
      compareWriteTM.halted c' ∧
      c'.output.cells 1 = (if is_match then Γ.one else Γ.zero) ∧
      c'.output.head = 1 ∧
      c'.input = c.input ∧
      (∀ i : Fin 4, c'.work i = c.work i) ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) := by
  -- Rewind output tape to cell 0 (reading ▷), then move right to cell 1, then write
  -- Phase 1: rewind loop (output.head steps to reach cell 0)
  suffices h_rewind : ∀ (h : ℕ) (c : Cfg 4 compareWriteTM.Q),
      c.state = (if is_match then .rewindOutM else .rewindOutD) →
      c.output.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
      c.output.head = h →
      (∀ i : Fin 4, (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
      c.input.read ≠ Γ.start →
      ∃ c',
        compareWriteTM.reachesIn (h + 2) c c' ∧
        compareWriteTM.halted c' ∧
        c'.output.cells 1 = (if is_match then Γ.one else Γ.zero) ∧
        c'.output.head = 1 ∧
        c'.input = c.input ∧
        (∀ i : Fin 4, c'.work i = c.work i) ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) by
    exact h_rewind c.output.head c hstate hoc0 hons rfl hns_work hinp
  intro h
  induction h with
  | zero =>
    intro c hstate hcell0 hnostart hhead hns_work hinp
    -- At cell 0: output reads ▷ → move right to cell 1, then write
    have hread_start : c.output.read = Γ.start := by
      simp [Tape.read, hhead, hcell0]
    -- Step 1: rewindOut{M,D} → write{M,D} (move right)
    have hstep1 : ∃ c₁,
        compareWriteTM.step c = some c₁ ∧
        c₁.state = (if is_match then .writeM else .writeD) ∧
        c₁.output.head = 1 ∧
        c₁.output.cells = c.output.cells ∧
        c₁.input = c.input ∧
        (∀ i : Fin 4, c₁.work i = c.work i) := by
      cases is_match <;> (
        simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread_start, Bool.false_eq_true]
        refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · dsimp only []
          simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
        · dsimp only []
          simp [Tape.writeAndMove, tape_move_cells', Tape.write, hhead]
        · dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
        · intro i; dsimp only []
          exact tape_idle_preserve (c.work i) (hns_work i).1 (hns_work i).2)
    obtain ⟨c₁, hstep1', hst1, hhead1, hcells1, hinp1, hwork1⟩ := hstep1
    -- Step 2: write{M,D} → done (write sym at cell 1 and halt)
    have hns1 : c₁.output.cells 1 ≠ Γ.start := by
      rw [hcells1]; exact hnostart 1 (by omega)
    have hout_read : c₁.output.read ≠ Γ.start := by
      simp [Tape.read, hhead1, hcells1]; exact hnostart 1 (by omega)
    have hns_work1 : ∀ i : Fin 4, (c₁.work i).read ≠ Γ.start ∧ (c₁.work i).head ≥ 1 := by
      intro i; rw [hwork1]; exact hns_work i
    have hinp1' : c₁.input.read ≠ Γ.start := by rw [hinp1]; exact hinp
    have hstep2 : ∃ c₂,
        compareWriteTM.step c₁ = some c₂ ∧
        compareWriteTM.halted c₂ ∧
        c₂.output.cells 1 = (if is_match then Γ.one else Γ.zero) ∧
        c₂.output.head = 1 ∧
        c₂.input = c₁.input ∧
        (∀ i : Fin 4, c₂.work i = c₁.work i) ∧
        c₂.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c₂.output.cells j ≠ Γ.start) := by
      cases is_match <;> (
        simp only [TM.step, hst1, compareWriteTM, ↓reduceIte, Bool.false_eq_true]
        refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- cells 1 = sym
          dsimp only []
          simp only [Tape.writeAndMove, idleDir, hout_read, ↓reduceIte,
            Tape.move, Tape.write, show c₁.output.head ≠ 0 from by omega]
          rw [hhead1, Function.update_self]; rfl
        · -- head = 1
          dsimp only []
          simp [Tape.writeAndMove, idleDir, hout_read, Tape.move, Tape.write, hhead1]
        · -- input
          dsimp only []; simp only [idleDir, hinp1', ↓reduceIte, Tape.move]
        · -- work
          intro i; dsimp only []
          exact tape_idle_preserve (c₁.work i) (hns_work1 i).1 (hns_work1 i).2
        · -- cells 0
          dsimp only []
          simp only [Tape.writeAndMove, idleDir, hout_read, ↓reduceIte,
            Tape.move, Tape.write, show c₁.output.head ≠ 0 from by omega]
          rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ c₁.output.head)]
          rw [hcells1]; exact hcell0
        · -- cells ≥ 1 ≠ start
          intro j hj; dsimp only []
          simp only [Tape.writeAndMove, idleDir, hout_read, ↓reduceIte,
            Tape.move, Tape.write, show c₁.output.head ≠ 0 from by omega]
          by_cases heq : j = c₁.output.head
          · subst heq; rw [Function.update_self]; decide
          · rw [Function.update_of_ne heq, hcells1]; exact hnostart j hj)
    obtain ⟨c₂, hstep2', hhalt, hcell, hhead2, hinp2, hwork2, hoc0', hons'⟩ := hstep2
    exact ⟨c₂, .step hstep1' (.step hstep2' .zero), hhalt, hcell, hhead2,
      by rw [hinp2, hinp1],
      fun i => by rw [hwork2 i, hwork1 i],
      hoc0', hons'⟩
  | succ h ih =>
    intro c hstate hcell0 hnostart hhead hns_work hinp
    -- Not at cell 0: output reads non-▷ → keep moving left
    have hread_ne : c.output.read ≠ Γ.start := by
      simp [Tape.read, hhead]; exact hnostart (h + 1) (by omega)
    have hstep : ∃ c₁,
        compareWriteTM.step c = some c₁ ∧
        c₁.state = (if is_match then .rewindOutM else .rewindOutD) ∧
        c₁.output.head = h ∧
        c₁.output.cells = c.output.cells ∧
        c₁.input = c.input ∧
        (∀ i : Fin 4, c₁.work i = c.work i) := by
      cases is_match <;> (
        simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread_ne, Bool.false_eq_true]
        refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
        · -- output head
          dsimp only []
          simp only [Tape.writeAndMove, Tape.move]
          rw [readBackWrite_toΓ_eq' hread_ne]
          simp only [Tape.write]; split
          · omega
          · simp [hhead]
        · -- output cells
          dsimp only []
          simp only [Tape.writeAndMove, tape_move_cells']
          rw [readBackWrite_toΓ_eq' hread_ne]
          simp only [Tape.write]; split
          · rfl
          · exact Function.update_eq_self _ _
        · -- input
          dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
        · -- work
          intro i; dsimp only []
          exact tape_idle_preserve (c.work i) (hns_work i).1 (hns_work i).2)
    obtain ⟨c₁, hstep', hst1, hhead1, hcells1, hinp1, hwork1⟩ := hstep
    obtain ⟨c_f, hreach_f, hhalt_f, hcell_f, hhead_f, hinp_f, hwork_f, hoc0_f, hons_f⟩ :=
      ih c₁ hst1 (by rw [hcells1]; exact hcell0) (by intro j hj; rw [hcells1]; exact hnostart j hj)
        hhead1 (by intro i; rw [hwork1]; exact hns_work i) (by rw [hinp1]; exact hinp)
    exact ⟨c_f, .step hstep' hreach_f, hhalt_f, hcell_f, hhead_f,
      by rw [hinp_f, hinp1],
      fun i => by rw [hwork_f i, hwork1 i],
      hoc0_f, hons_f⟩

-- ════════════════════════════════════════════════════════════════════════
-- compareWriteTM: mismatch scan (all match for prefix, then mismatch)
-- ════════════════════════════════════════════════════════════════════════

/-- Comparison loop variant for MISMATCH: scan past `count` matching non-blank cells,
    then a mismatch (non-blank cells that differ) → rewindOutD. -/
private theorem compare_mismatch_scan :
    ∀ (count : ℕ) (c : Cfg 4 compareWriteTM.Q),
    c.state = .compare →
    (∀ j, j < count → (c.work (0 : Fin 4)).cells ((c.work 0).head + j) =
                        (c.work (1 : Fin 4)).cells ((c.work 1).head + j)) →
    (∀ j, j ≤ count → (c.work (1 : Fin 4)).cells ((c.work 1).head + j) ≠ Γ.blank) →
    (c.work (0 : Fin 4)).cells ((c.work 0).head + count) ≠
      (c.work (1 : Fin 4)).cells ((c.work 1).head + count) →
    (c.work (0 : Fin 4)).head ≥ 1 →
    (c.work (1 : Fin 4)).head ≥ 1 →
    (∀ p, p ≥ 1 → (c.work (0 : Fin 4)).cells p ≠ Γ.start) →
    (∀ p, p ≥ 1 → (c.work (1 : Fin 4)).cells p ≠ Γ.start) →
    (∀ i : Fin 4, i ≠ 0 → i ≠ 1 →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1) →
    c.input.read ≠ Γ.start →
    c.output.read ≠ Γ.start → c.output.head ≥ 1 →
    c.output.cells 0 = Γ.start →
    (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) →
    ∃ c',
      compareWriteTM.reachesIn (count + 1) c c' ∧
      c'.state = .rewindOutD ∧
      (c'.work (0 : Fin 4)).cells = (c.work 0).cells ∧
      (c'.work (1 : Fin 4)).cells = (c.work 1).cells ∧
      c'.input = c.input ∧
      c'.output.head = c.output.head ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
      (c'.work (0 : Fin 4)).head = (c.work (0 : Fin 4)).head + count ∧
      (c'.work (1 : Fin 4)).head = (c.work (1 : Fin 4)).head + count ∧
      (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
  intro count; induction count with
  | zero =>
    intro c hstate _ hnotblank hmismatch hh0 hh1 hns0 hns1 hother hinp hout houth hoc0 hons
    have hns_r0 : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns0 _ hh0
    have hns_r1 : (c.work (1 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns1 _ hh1
    have hread1_ne_blank : (fun i => (c.work i).read) (1 : Fin 4) ≠ Γ.blank := by
      simp only [Tape.read]; exact hnotblank 0 (by omega)
    have hread_neq : (fun i => (c.work i).read) (0 : Fin 4) ≠
        (fun i => (c.work i).read) (1 : Fin 4) := by
      simp only [Tape.read, Nat.add_zero] at hmismatch ⊢; exact hmismatch
    have hstep : ∃ c',
        compareWriteTM.step c = some c' ∧
        c'.state = .rewindOutD ∧
        (c'.work 0).cells = (c.work 0).cells ∧
        (c'.work 1).cells = (c.work 1).cells ∧
        c'.input = c.input ∧
        c'.output.head = c.output.head ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
        (c'.work (0 : Fin 4)).head = (c.work (0 : Fin 4)).head ∧
        (c'.work (1 : Fin 4)).head = (c.work (1 : Fin 4)).head ∧
        (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
      simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread1_ne_blank, hread_neq]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []; rw [tape_idle_preserve (c.work 0) hns_r0 hh0]
      · dsimp only []; rw [tape_idle_preserve (c.work 1) hns_r1 hh1]
      · dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · dsimp only []; exact output_head_idle c.output hout houth
      · dsimp only []; exact (output_cells0_idle c.output hout houth).trans hoc0
      · dsimp only []; exact output_cellsNS_idle c.output hout houth hons
      · dsimp only []; show _ = (c.work 0).head
        rw [tape_idle_preserve (c.work 0) hns_r0 hh0]
      · dsimp only []; show _ = (c.work 1).head
        rw [tape_idle_preserve (c.work 1) hns_r1 hh1]
      · intro i hne0 hne1; dsimp only []
        exact tape_idle_preserve (c.work i) (hother i hne0 hne1).1 (hother i hne0 hne1).2
    obtain ⟨c', hstep_eq, hst, hc0, hc1, hinp', hoh, hoc0', hons', hh0_eq, hh1_eq, hw⟩ := hstep
    exact ⟨c', .step hstep_eq .zero, hst, hc0, hc1, hinp', hoh, hoc0', hons',
      by simp [hh0_eq], by simp [hh1_eq], hw⟩
  | succ n ih =>
    intro c hstate hmatch hnotblank hmismatch hh0 hh1 hns0 hns1 hother hinp hout houth hoc0 hons
    have hns_r0 : (c.work (0 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns0 _ hh0
    have hns_r1 : (c.work (1 : Fin 4)).read ≠ Γ.start := by
      simp only [Tape.read]; exact hns1 _ hh1
    have hread1_ne : (fun i => (c.work i).read) (1 : Fin 4) ≠ Γ.blank := by
      simp only [Tape.read]; exact hnotblank 0 (by omega)
    have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) =
        (fun i => (c.work i).read) (1 : Fin 4) := by
      simp only [Tape.read]; exact hmatch 0 (by omega)
    -- Match step (same as compare_match_scan succ case)
    have hstep : ∃ c',
        compareWriteTM.step c = some c' ∧
        c'.state = .compare ∧
        (c'.work 0).head = (c.work 0).head + 1 ∧
        (c'.work 0).cells = (c.work 0).cells ∧
        (c'.work 1).head = (c.work 1).head + 1 ∧
        (c'.work 1).cells = (c.work 1).cells ∧
        c'.input = c.input ∧
        c'.output.head = c.output.head ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
        c'.output.read ≠ Γ.start ∧
        (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) := by
      simp only [TM.step, hstate, compareWriteTM, ↓reduceIte, hread1_ne, hread_eq]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write]
        split <;> (first | omega | rfl)
      · dsimp only []
        simp only [show (↑(0 : Fin 4) : ℕ) = 0 from rfl, ↓reduceIte,
          Tape.writeAndMove, tape_move_cells', Tape.write]
        split
        · rfl
        · rw [readBackWrite_toΓ_eq' hns_r0]; exact Function.update_eq_self _ _
      · dsimp only []
        simp only [show (↑(1 : Fin 4) : ℕ) = 1 from rfl,
          show ¬((1 : ℕ) = 0) from by omega, ↓reduceIte,
          Tape.writeAndMove, Tape.move, Tape.write]
        split <;> (first | omega | rfl)
      · dsimp only []
        simp only [show (↑(1 : Fin 4) : ℕ) = 1 from rfl,
          show ¬((1 : ℕ) = 0) from by omega, ↓reduceIte,
          Tape.writeAndMove, tape_move_cells', Tape.write]
        split
        · rfl
        · rw [readBackWrite_toΓ_eq' hns_r1]; exact Function.update_eq_self _ _
      · dsimp only []; simp only [idleDir, hinp, ↓reduceIte, Tape.move]
      · dsimp only []; exact output_head_idle c.output hout houth
      · dsimp only []; exact (output_cells0_idle c.output hout houth).trans hoc0
      · dsimp only []; exact output_cellsNS_idle c.output hout houth hons
      · dsimp only []; exact output_readNS_idle c.output hout houth hons
      · intro i hne0 hne1; dsimp only []
        have : ¬(↑i = (0 : ℕ)) := fun h => hne0 (by ext; exact h)
        have : ¬(↑i = (1 : ℕ)) := fun h => hne1 (by ext; exact h)
        simp only [*, ↓reduceIte]
        exact tape_idle_preserve (c.work i) (hother i hne0 hne1).1 (hother i hne0 hne1).2
    obtain ⟨c', hstep_eq, hst', hh0', hc0', hh1', hc1', hinp', hoh', hoc0'', hons'', hout_ns', hw'⟩ := hstep
    obtain ⟨c_f, hreach_f, hst_f, hcf0, hcf1, hinp_f, hoh_f, hoc0_f, hons_f, hh0_f, hh1_f, hw_f⟩ := ih c' hst'
      (by intro j hj; rw [hc0', hh0', hc1', hh1']
          have : (c.work 0).head + 1 + j = (c.work 0).head + (j + 1) := by omega
          have : (c.work 1).head + 1 + j = (c.work 1).head + (j + 1) := by omega
          rw [‹(c.work 0).head + 1 + j = _›, ‹(c.work 1).head + 1 + j = _›]
          exact hmatch (j + 1) (by omega))
      (by intro j hj; rw [hc1', hh1']
          have : (c.work 1).head + 1 + j = (c.work 1).head + (j + 1) := by omega
          rw [this]; exact hnotblank (j + 1) (by omega))
      (by rw [hc0', hh0', hc1', hh1']
          have : (c.work 0).head + 1 + n = (c.work 0).head + (n + 1) := by omega
          have : (c.work 1).head + 1 + n = (c.work 1).head + (n + 1) := by omega
          rw [‹(c.work 0).head + 1 + n = _›, ‹(c.work 1).head + 1 + n = _›]
          exact hmismatch)
      (by omega) (by omega)
      (by rwa [hc0'])
      (by rwa [hc1'])
      (by intro i hne0 hne1; rw [hw' i hne0 hne1]; exact hother i hne0 hne1)
      (by rwa [hinp'])
      hout_ns' (by rw [hoh']; exact houth)
      hoc0'' hons''
    exact ⟨c_f, .step hstep_eq hreach_f, hst_f,
      by rw [hcf0, hc0'],
      by rw [hcf1, hc1'],
      by rw [hinp_f, hinp'],
      by rw [hoh_f, hoh'],
      hoc0_f, hons_f,
      by rw [hh0_f, hh0']; omega, by rw [hh1_f, hh1']; omega,
      fun i hne0 hne1 => by rw [hw_f i hne0 hne1, hw' i hne0 hne1]⟩

-- ════════════════════════════════════════════════════════════════════════
-- compareWriteTM: full simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Full simulation of compareWriteTM. Compares two one-hot patterns:
    desc tape at `desc_pos` and state tape at cell 1, each of width `k`.
    If patterns match (q_desc = q_state), writes Γ.one to output cell 1.
    If they differ, writes Γ.zero. -/
private theorem compareWriteTM_simulation (k : ℕ) (q_desc q_state : Fin k)
    (desc_pos B : ℕ)
    (c : Cfg 4 compareWriteTM.Q)
    (hstate : c.state = .compare)
    (hdh : (c.work (0 : Fin 4)).head = desc_pos) (hh0 : desc_pos ≥ 1)
    (hsh : (c.work (1 : Fin 4)).head = 1)
    -- desc tape has one-hot for q_desc at desc_pos
    (hdesc : ∀ j, j < k → (c.work (0 : Fin 4)).cells (desc_pos + j) =
      if j = q_desc.val then Γ.one else Γ.zero)
    -- state tape has one-hot for q_state
    (hstate_enc : stateOnTapeAt k q_state (c.work (1 : Fin 4)))
    -- output WF
    (hoc0 : c.output.cells 0 = Γ.start)
    (hons : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hoh : c.output.head ≤ B)
    -- Work tape WF
    (hns0 : ∀ p, p ≥ 1 → (c.work (0 : Fin 4)).cells p ≠ Γ.start)
    (hns1 : ∀ p, p ≥ 1 → (c.work (1 : Fin 4)).cells p ≠ Γ.start)
    (hother : ∀ i : Fin 4, i ≠ 0 → i ≠ 1 →
      (c.work i).read ≠ Γ.start ∧ (c.work i).head ≥ 1)
    (hinp : c.input.read ≠ Γ.start)
    (hout_ns : c.output.read ≠ Γ.start) (hout_h : c.output.head ≥ 1) :
    ∃ c' t, t ≤ k + B + 3 ∧ compareWriteTM.reachesIn t c c' ∧
      compareWriteTM.halted c' ∧
      (q_desc = q_state → c'.output.cells 1 = Γ.one) ∧
      (q_desc ≠ q_state → c'.output.cells 1 = Γ.zero) ∧
      c'.output.head = 1 ∧
      (c'.work (0 : Fin 4)).cells = (c.work 0).cells ∧
      (c'.work (1 : Fin 4)).cells = (c.work 1).cells ∧
      c'.input = c.input ∧
      (∀ i : Fin 4, i ≠ 0 → i ≠ 1 → c'.work i = c.work i) ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
      (c'.work (0 : Fin 4)).head ≥ 1 ∧
      (c'.work (1 : Fin 4)).head ≥ 1 ∧
      (c'.work (0 : Fin 4)).head ≤ desc_pos + k ∧
      (c'.work (1 : Fin 4)).head ≤ 1 + k := by
  -- Extract state tape structure
  obtain ⟨hst0, hst_bits, hst_sentinel⟩ := hstate_enc
  -- Helper: convert between j + 1 and 1 + j for state tape
  have hst_bits' : ∀ j, j < k → (c.work 1).cells (1 + j) =
      if j = q_state.val then Γ.one else Γ.zero := by
    intro j hj; rw [show 1 + j = j + 1 from by omega]; exact hst_bits j hj
  have hst_sentinel' : (c.work 1).cells (1 + k) = Γ.blank := by
    rw [show 1 + k = k + 1 from by omega]; exact hst_sentinel
  by_cases heq : q_desc = q_state
  · -- MATCH case: all k cells match, sentinel at k → rewindOutM
    have hmatch_cells : ∀ j, j < k →
        (c.work 0).cells ((c.work 0).head + j) =
        (c.work 1).cells ((c.work 1).head + j) := by
      intro j hj; rw [hdh, hsh, hdesc j hj, hst_bits' j hj, heq]
    have hnotblank : ∀ j, j < k →
        (c.work 1).cells ((c.work 1).head + j) ≠ Γ.blank := by
      intro j hj; rw [hsh, hst_bits' j hj]; split <;> decide
    have hsentinel : (c.work 1).cells ((c.work 1).head + k) = Γ.blank := by
      rw [hsh]; exact hst_sentinel'
    obtain ⟨c_mid, hreach1, hst_mid, hc0_mid, hc1_mid, hinp_mid, hoh_mid,
            hoc0_mid, hons_mid, hh0_mid_eq, hh1_mid_eq, hw_mid⟩ :=
      compare_match_scan k c hstate hmatch_cells hnotblank hsentinel
        (by omega) (by omega) hns0 hns1 hother hinp hout_ns hout_h hoc0 hons
    have hh0_mid_ge : (c_mid.work (0 : Fin 4)).head ≥ 1 := by rw [hh0_mid_eq]; omega
    have hh1_mid_ge : (c_mid.work (1 : Fin 4)).head ≥ 1 := by rw [hh1_mid_eq]; omega
    have hns_work_mid : ∀ i : Fin 4, (c_mid.work i).read ≠ Γ.start ∧ (c_mid.work i).head ≥ 1 := by
      intro i
      by_cases h0 : i = 0
      · subst h0
        exact ⟨by simp only [Tape.read]; rw [hc0_mid]; exact hns0 _ hh0_mid_ge, hh0_mid_ge⟩
      · by_cases h1 : i = 1
        · subst h1
          exact ⟨by simp only [Tape.read]; rw [hc1_mid]; exact hns1 _ hh1_mid_ge, hh1_mid_ge⟩
        · rw [hw_mid i h0 h1]; exact hother i h0 h1
    obtain ⟨c_done, hreach2, hhalt, hcell1, hhead_done, hinp_done, hwork_done,
            hoc0_done, hons_done⟩ :=
      compareWriteTM_rewind_write true c_mid hst_mid hoc0_mid hons_mid hns_work_mid
        (by rw [hinp_mid]; exact hinp)
    refine ⟨c_done, k + 1 + (c_mid.output.head + 2), by rw [hoh_mid]; omega,
      reachesIn_trans _ hreach1 hreach2, hhalt, ?_, ?_, hhead_done,
      ?_, ?_, by rw [hinp_done, hinp_mid], ?_, hoc0_done, hons_done,
      by rw [hwork_done 0]; exact hh0_mid_ge,
      by rw [hwork_done 1]; exact hh1_mid_ge,
      by rw [hwork_done 0, hh0_mid_eq, hdh],
      by rw [hwork_done 1, hh1_mid_eq, hsh]⟩
    · intro _; exact hcell1
    · intro hne; exact absurd heq hne
    · rw [hwork_done 0, hc0_mid]
    · rw [hwork_done 1, hc1_mid]
    · intro i hne0 hne1; rw [hwork_done i]; exact hw_mid i hne0 hne1
  · -- MISMATCH case: first mismatch at position min(q_desc, q_state)
    let m := min q_desc.val q_state.val
    have hm_lt : m < k := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) q_desc.isLt
    -- Cells at positions 0..m-1 all match (both are Γ.zero)
    have hmatch_prefix : ∀ j, j < m →
        (c.work 0).cells ((c.work 0).head + j) =
        (c.work 1).cells ((c.work 1).head + j) := by
      intro j hj; rw [hdh, hsh, hdesc j (by omega), hst_bits' j (by omega)]
      have : j ≠ q_desc.val := by omega
      have : j ≠ q_state.val := by omega
      simp [*]
    -- All state tape cells in 0..m are non-blank
    have hnotblank_prefix : ∀ j, j ≤ m →
        (c.work 1).cells ((c.work 1).head + j) ≠ Γ.blank := by
      intro j hj; rw [hsh, hst_bits' j (by omega)]; split <;> decide
    -- At position m: cells differ (one is 1, other is 0)
    have hmismatch_at_m :
        (c.work 0).cells ((c.work 0).head + m) ≠
        (c.work 1).cells ((c.work 1).head + m) := by
      rw [hdh, hsh, hdesc m hm_lt, hst_bits' m hm_lt]
      simp only [m, Nat.min_def]
      split
      · -- q_desc.val ≤ q_state.val, so min = q_desc.val
        simp only [↓reduceIte]
        have : q_desc.val ≠ q_state.val := fun h => heq (Fin.ext h)
        simp [this]
      · -- q_state.val < q_desc.val, so min = q_state.val
        rename_i hgt
        have : q_state.val ≠ q_desc.val := by omega
        have : q_desc.val ≠ q_state.val := fun h => heq (Fin.ext h)
        simp [*]
    obtain ⟨c_mid, hreach1, hst_mid, hc0_mid, hc1_mid, hinp_mid, hoh_mid,
            hoc0_mid, hons_mid, hh0_mid_eq, hh1_mid_eq, hw_mid⟩ :=
      compare_mismatch_scan m c hstate hmatch_prefix hnotblank_prefix hmismatch_at_m
        (by omega) (by omega) hns0 hns1 hother hinp hout_ns hout_h hoc0 hons
    have hh0_mid_ge : (c_mid.work (0 : Fin 4)).head ≥ 1 := by rw [hh0_mid_eq]; omega
    have hh1_mid_ge : (c_mid.work (1 : Fin 4)).head ≥ 1 := by rw [hh1_mid_eq]; omega
    have hns_work_mid : ∀ i : Fin 4, (c_mid.work i).read ≠ Γ.start ∧ (c_mid.work i).head ≥ 1 := by
      intro i
      by_cases h0 : i = 0
      · subst h0
        exact ⟨by simp only [Tape.read]; rw [hc0_mid]; exact hns0 _ hh0_mid_ge, hh0_mid_ge⟩
      · by_cases h1 : i = 1
        · subst h1
          exact ⟨by simp only [Tape.read]; rw [hc1_mid]; exact hns1 _ hh1_mid_ge, hh1_mid_ge⟩
        · rw [hw_mid i h0 h1]; exact hother i h0 h1
    obtain ⟨c_done, hreach2, hhalt, hcell1, hhead_done, hinp_done, hwork_done,
            hoc0_done, hons_done⟩ :=
      compareWriteTM_rewind_write false c_mid hst_mid hoc0_mid hons_mid hns_work_mid
        (by rw [hinp_mid]; exact hinp)
    refine ⟨c_done, m + 1 + (c_mid.output.head + 2), by rw [hoh_mid]; omega,
      reachesIn_trans _ hreach1 hreach2, hhalt, ?_, ?_, hhead_done,
      ?_, ?_, by rw [hinp_done, hinp_mid], ?_, hoc0_done, hons_done,
      by rw [hwork_done 0]; exact hh0_mid_ge,
      by rw [hwork_done 1]; exact hh1_mid_ge,
      by rw [hwork_done 0, hh0_mid_eq, hdh]; exact Nat.add_le_add_left (le_of_lt hm_lt) _,
      by rw [hwork_done 1, hh1_mid_eq, hsh]; exact Nat.add_le_add_left (le_of_lt hm_lt) _⟩
    · intro heq_contra; exact absurd heq_contra heq
    · intro _; exact hcell1
    · rw [hwork_done 0, hc0_mid]
    · rw [hwork_done 1, hc1_mid]
    · intro i hne0 hne1; rw [hwork_done i]; exact hw_mid i hne0 hne1

-- ════════════════════════════════════════════════════════════════════════
-- Rich HoareTime specs for sub-machines (for composition)
-- ════════════════════════════════════════════════════════════════════════

variable {n : ℕ}

/-- HoareTime wrapper for skipToQhaltTM. Navigates desc tape from cell 1
    past header to qhalt one-hot position. Preserves all other tapes. -/
private theorem skipToQhaltTM_asHoareTime {Q : Type} [DecidableEq Q]
    (k' n' : ℕ) (desc : List Bool) (simCfg : Cfg n Q)
    (q : Fin k')
    -- Header structure on the desc tape
    (hones1 : ∀ j, j < k' → desc[j]? = some true)
    (hsep1 : desc[k']? = some false)
    (hones2 : ∀ j, j < n' → desc[k' + 1 + j]? = some true)
    (hsep2 : desc[k' + 1 + n']? = some false)
    (hdesc_long : k' + 1 + n' + 1 ≤ desc.length)
    {B_out : ℕ} :
    skipToQhaltTM.HoareTime
      (fun inp work out =>
        descOnTape desc (work (0 : Fin 4)) ∧
        stateOnTapeAt k' q (work (1 : Fin 4)) ∧
        (work (0 : Fin 4)).head = 1 ∧
        (work (1 : Fin 4)).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        out.head ≤ B_out ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k' n' + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k' n' + 1) = Γ.blank)
      (fun inp work out =>
        descOnTape desc (work (0 : Fin 4)) ∧
        stateOnTapeAt k' q (work (1 : Fin 4)) ∧
        (work (0 : Fin 4)).head = k' + n' + 3 ∧
        (work (1 : Fin 4)).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        out.head ≤ B_out ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k' n' + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k' n' + 1) = Γ.blank)
      (k' + n' + 2) := by
  intro inp work out ⟨hdesc_tape, hstate_tape, hdh, hsh, hoc0, hons, hwf, hinp, hout_ns, hout_h,
    hheads, hout_le, hsim, hsim_h, hscratch_h, hscratch_inp_blank, hscratch_out_blank⟩
  -- Derive the header structure on the tape from descOnTape + desc structure
  have hones1_tape : ∀ j, j < k' → (work (0 : Fin 4)).cells (1 + j) = Γ.one := by
    intro j hj
    obtain ⟨_, hbits, _⟩ := hdesc_tape
    have hlen : j < desc.length := by omega
    have heq : j + 1 = 1 + j := by omega
    rw [show (1 : ℕ) + j = j + 1 from by omega, hbits j hlen]
    have := hones1 j hj
    simp only [List.getElem?_eq_getElem hlen] at this
    injection this with h; rw [h]; rfl
  have hsep1_tape : (work (0 : Fin 4)).cells (1 + k') ≠ Γ.one := by
    obtain ⟨_, hbits, _⟩ := hdesc_tape
    have hlen : k' < desc.length := by omega
    rw [show (1 : ℕ) + k' = k' + 1 from by omega, hbits k' hlen]
    have := hsep1
    simp only [List.getElem?_eq_getElem hlen] at this
    injection this with h; rw [h]; decide
  have hones2_tape : ∀ j, j < n' → (work (0 : Fin 4)).cells (k' + 2 + j) = Γ.one := by
    intro j hj
    obtain ⟨_, hbits, _⟩ := hdesc_tape
    have hlen : k' + 1 + j < desc.length := by omega
    rw [show k' + 2 + j = (k' + 1 + j) + 1 from by omega, hbits (k' + 1 + j) hlen]
    have := hones2 j hj
    simp only [List.getElem?_eq_getElem hlen] at this
    injection this with h; rw [h]; rfl
  have hsep2_tape : (work (0 : Fin 4)).cells (k' + 2 + n') ≠ Γ.one := by
    obtain ⟨_, hbits, _⟩ := hdesc_tape
    have hlen : k' + 1 + n' < desc.length := by omega
    rw [show k' + 2 + n' = (k' + 1 + n') + 1 from by omega, hbits (k' + 1 + n') hlen]
    have := hsep2
    simp only [List.getElem?_eq_getElem hlen] at this
    injection this with h; rw [h]; decide
  -- Other tapes read ≠ ▷ and head ≥ 1
  have hother : ∀ i, i ≠ (0 : Fin 4) → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1 := by
    intro i hne
    refine ⟨?_, hheads i⟩
    simp only [Tape.read]
    exact hwf.2 i _ (hheads i)
  -- Apply the existing simulation lemma
  obtain ⟨c', hreach, hhalt, hh', hcells', hinp', hout', hwork'⟩ :=
    skipToQhaltTM_hoareTime k' n'
      { state := skipToQhaltTM.qstart, input := inp, work := work, output := out }
      rfl hdh hones1_tape hsep1_tape hones2_tape hsep2_tape
      (fun p hp => hwf.2 0 p hp) hother hinp hout_ns hout_h
  -- Reduce struct field projections
  change (c'.work 0).cells = (work 0).cells at hcells'
  change c'.input = inp at hinp'
  change c'.output = out at hout'
  change ∀ i, i ≠ (0 : Fin 4) → c'.work i = work i at hwork'
  refine ⟨c', k' + n' + 2, le_rfl, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, hh', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- descOnTape preserved (cells unchanged)
    obtain ⟨h0, hbits, hblank⟩ := hdesc_tape
    refine ⟨?_, ?_, ?_⟩
    · rw [show (c'.work (0 : Fin 4)).cells 0 = (work 0).cells 0 from by rw [hcells']]; exact h0
    · intro i hi
      rw [show (c'.work (0 : Fin 4)).cells (i + 1) = (work 0).cells (i + 1) from by rw [hcells']]
      exact hbits i hi
    · rw [show (c'.work (0 : Fin 4)).cells (desc.length + 1) = (work 0).cells (desc.length + 1)
        from by rw [hcells']]
      exact hblank
  · -- stateOnTapeAt preserved (tape unchanged)
    rw [hwork' 1 (by decide)]; exact hstate_tape
  · -- state head preserved
    rw [hwork' 1 (by decide)]; exact hsh
  · -- output cells 0 preserved
    rw [hout']; exact hoc0
  · -- output cells ≥ 1 ≠ ▷
    intro j hj; rw [hout']; exact hons j hj
  · -- WorkTapesWF preserved
    constructor
    · intro i
      by_cases h : i = 0
      · subst h; rw [hcells']; exact hwf.1 0
      · rw [hwork' i h]; exact hwf.1 i
    · intro i j hj
      by_cases h : i = 0
      · subst h; rw [hcells']; exact hwf.2 0 j hj
      · rw [hwork' i h]; exact hwf.2 i j hj
  · -- input preserved
    rw [hinp']; exact hinp
  · -- output read ≠ ▷
    rw [hout']; exact hout_ns
  · -- output head ≥ 1
    rw [hout']; exact hout_h
  · -- all heads ≥ 1
    intro i
    by_cases h : i = 0
    · subst h; rw [hh']; omega
    · rw [hwork' i h]; exact hheads i
  · -- output head bound preserved
    rw [hout']; exact hout_le
  · -- sim tape preserved
    rw [hwork' 2 (by decide)]; exact hsim
  · -- sim head preserved
    rw [hwork' 2 (by decide)]; exact hsim_h
  · -- scratch head preserved
    rw [hwork' 3 (by decide)]; exact hscratch_h
  · -- scratch input-pattern sentinel preserved
    rw [hwork' 3 (by decide)]; exact hscratch_inp_blank
  · -- scratch output sentinel preserved
    rw [hwork' 3 (by decide)]; exact hscratch_out_blank

/-- HoareTime for compareWriteTM with rich postcondition. -/
private theorem compareWriteTM_asHoareTime {Q : Type} [DecidableEq Q]
    (tm : TM n) (k : ℕ) (simCfg : Cfg n Q)
    (e : tm.Q ≃ Fin k) (desc : List Bool) (q : Fin k) (B : ℕ)
    (he_val : ∀ q : tm.Q, (e q).val = (tm.stateEquiv q).val)
    -- qhalt encoding on desc at position k+n+3
    (hqhalt : ∀ j, j < k → desc[k + 2 + n + j]? = some (decide (j = (e tm.qhalt).val)))
    (hdesc_long : k + 2 + n + k ≤ desc.length) :
    compareWriteTM.HoareTime
      (fun inp work out =>
        descOnTape desc (work (0 : Fin 4)) ∧
        stateOnTapeAt k q (work (1 : Fin 4)) ∧
        (work (0 : Fin 4)).head = k + n + 3 ∧
        (work (1 : Fin 4)).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ B ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (fun inp work out =>
        descOnTape desc (work (0 : Fin 4)) ∧
        stateOnTapeAt k q (work (1 : Fin 4)) ∧
        (q = e tm.qhalt → out.cells 1 = Γ.one) ∧
        (q ≠ e tm.qhalt → out.cells 1 = Γ.zero) ∧
        out.head = 1 ∧ out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        WorkTapesWF work ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, (work i).head ≥ 1) ∧
        (work (0 : Fin 4)).head ≤ 2 * k + n + 3 ∧
        (work (1 : Fin 4)).head ≤ k + 1 ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (k + B + 3) := by
  intro inp work out ⟨hdesc_tape, hstate_tape, hdh, hsh, hoc0, hons, hoh, hwf, hinp, hout_ns, hout_h,
    hheads, hsim, hsim_h, hscratch_h, hscratch_inp_blank, hscratch_out_blank⟩
  have hh0 : k + n + 3 ≥ 1 := by omega
  -- Desc tape one-hot for qhalt at position k+n+3
  have hdesc_qhalt : ∀ j, j < k → (work (0 : Fin 4)).cells (k + n + 3 + j) =
      if j = (e tm.qhalt).val then Γ.one else Γ.zero := by
    intro j hj
    obtain ⟨_, hbits, _⟩ := hdesc_tape
    have hlen : k + 2 + n + j < desc.length := by omega
    rw [show k + n + 3 + j = (k + 2 + n + j) + 1 from by omega, hbits (k + 2 + n + j) hlen]
    have := hqhalt j hj
    simp only [List.getElem?_eq_getElem hlen] at this
    injection this with h; rw [h]; simp [Γ.ofBool]; split <;> simp_all
  obtain ⟨c', t, ht, hreach, hhalt, hq_eq, hq_ne, hhead1, hcw0, hcw1, hinp', hw_other,
          hoc0', hons', hh0_ge, hh1_ge, hh0_le, hh1_le⟩ :=
    compareWriteTM_simulation k (e tm.qhalt) q (k + n + 3) B
      { state := compareWriteTM.qstart, input := inp, work := work, output := out }
      rfl hdh hh0 hsh hdesc_qhalt hstate_tape hoc0 hons hoh
      (fun p hp => hwf.2 0 p hp) (fun p hp => hwf.2 1 p hp)
      (fun i h0 h1 => ⟨by simp only [Tape.read]; exact hwf.2 i _ (hheads i), hheads i⟩)
      (by simp only [Tape.read]; exact hinp) hout_ns hout_h
  change (c'.work 0).cells = (work 0).cells at hcw0
  change (c'.work 1).cells = (work 1).cells at hcw1
  change c'.input = inp at hinp'
  refine ⟨c', t, ht, hreach, hhalt, ?_⟩
  refine ⟨?_, ?_, fun h => hq_eq h.symm, fun h => hq_ne (fun h' => h h'.symm),
    hhead1, hoc0', hons', ?_, by rw [hinp']; exact hinp,
    by simp only [Tape.read, hhead1]; exact hons' 1 (by omega),
    by rw [hhead1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h0, hbits, hblank⟩ := hdesc_tape
    exact ⟨by rw [hcw0]; exact h0,
      fun i hi => by rw [hcw0]; exact hbits i hi,
      by rw [hcw0]; exact hblank⟩
  · obtain ⟨h0, hbits, hsentinel⟩ := hstate_tape
    exact ⟨by rw [hcw1]; exact h0,
      fun j hj => by rw [hcw1]; exact hbits j hj,
      by rw [hcw1]; exact hsentinel⟩
  · constructor
    · intro i
      by_cases h0 : i = 0
      · subst h0; rw [hcw0]; exact hwf.1 0
      · by_cases h1 : i = 1
        · subst h1; rw [hcw1]; exact hwf.1 1
        · rw [hw_other i h0 h1]; exact hwf.1 i
    · intro i j hj
      by_cases h0 : i = 0
      · subst h0; rw [hcw0]; exact hwf.2 0 j hj
      · by_cases h1 : i = 1
        · subst h1; rw [hcw1]; exact hwf.2 1 j hj
        · rw [hw_other i h0 h1]; exact hwf.2 i j hj
  · intro i
    by_cases h0 : i = 0
    · subst h0; exact hh0_ge
    · by_cases h1 : i = 1
      · subst h1; exact hh1_ge
      · rw [hw_other i h0 h1]; exact hheads i
  · -- desc head ≤ 2*k + n + 3
    have := hh0_le; omega
  · -- state head ≤ k + 1
    have := hh1_le; omega
  · -- sim tape preserved
    rw [hw_other 2 (by decide) (by decide)]; exact hsim
  · -- sim head preserved
    rw [hw_other 2 (by decide) (by decide)]; exact hsim_h
  · -- scratch head preserved
    rw [hw_other 3 (by decide) (by decide)]; exact hscratch_h
  · -- scratch input-pattern sentinel preserved
    rw [hw_other 3 (by decide) (by decide)]; exact hscratch_inp_blank
  · -- scratch output sentinel preserved
    rw [hw_other 3 (by decide) (by decide)]; exact hscratch_out_blank

-- rewindWorkTM_rich_hoareTime is now public in HelpersInternal.lean

-- ════════════════════════════════════════════════════════════════════════
-- Encoding structure lemmas (derived from encodeTM definition)
-- ════════════════════════════════════════════════════════════════════════

private theorem encodeTM_ones1 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    ∀ j, j < k → desc[j]? = some true := by
  subst hdesc; intro j hj
  have hj' : j < Fintype.card tm.Q := hk ▸ hj
  show (TMEncoding.encodeTM tm)[j]? = some true
  unfold TMEncoding.encodeTM
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_replicate, if_pos hj']

private theorem encodeTM_sep1 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    desc[k]? = some false := by
  subst hdesc; subst hk
  show (TMEncoding.encodeTM tm)[Fintype.card tm.Q]? = some false
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  simp [List.length_replicate, List.length_map, List.length_finRange]

private theorem encodeTM_ones2 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    ∀ j, j < n → desc[k + 1 + j]? = some true := by
  subst hdesc; subst hk; intro j hj
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  -- Peel right appends until we reach (replicate k ++ [false] ++ replicate n)
  rw [List.getElem?_append_left (by simp; omega)]  -- peel transTable
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel map qstart
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel map qhalt
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  -- Now: ((replicate k ++ [false]) ++ replicate n)[k+1+j]?
  have hlen : (List.replicate (Fintype.card tm.Q) true ++ [false]).length ≤ Fintype.card tm.Q + 1 + j := by
    simp
  rw [List.getElem?_append_right hlen]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  rw [show Fintype.card tm.Q + 1 + j - (Fintype.card tm.Q + 1) = j from by omega]
  rw [List.getElem?_replicate, if_pos hj]

private theorem encodeTM_sep2 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    desc[k + 1 + n]? = some false := by
  subst hdesc; subst hk
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel transTable
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel map qstart
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel map qhalt
  -- Now: (((replicate k ++ [false]) ++ replicate n) ++ [false])[k+1+n]?
  have hlen : ((List.replicate (Fintype.card tm.Q) true ++ [false]) ++ List.replicate n true).length ≤ Fintype.card tm.Q + 1 + n := by
    simp; omega
  rw [List.getElem?_append_right hlen]
  have : Fintype.card tm.Q + 1 + n - (List.replicate (Fintype.card tm.Q) true ++ [false] ++ List.replicate n true).length = 0 := by
    simp; omega
  rw [this]
  simp

private theorem encodeTM_long1 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    k + 1 + n + 1 ≤ desc.length := by
  subst hdesc; subst hk
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  simp only [List.length_append, List.length_replicate, List.length_map, List.length_finRange,
    List.length_cons, List.length_nil]
  omega

private theorem encodeTM_qhalt (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm)
    {e : tm.Q ≃ Fin k}
    (he_val : ∀ q : tm.Q, (e q).val = (tm.stateEquiv q).val) :
    ∀ j, j < k → desc[k + 2 + n + j]? = some (decide (j = (e tm.qhalt).val)) := by
  subst hdesc; intro j hj
  have hj' : j < Fintype.card tm.Q := hk ▸ hj
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  -- Peel right appends: transTable, [false], map qstart, [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel transTable
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  rw [List.getElem?_append_left (by simp; omega)]  -- peel map qstart
  rw [List.getElem?_append_left (by simp; omega)]  -- peel [false]
  -- Now: (replicate k ++ [false] ++ replicate n ++ [false] ++ map...qhalt)[k+2+n+j]?
  have hlen : (List.replicate (Fintype.card tm.Q) true ++ [false] ++ List.replicate n true ++ [false]).length ≤ k + 2 + n + j := by
    simp; omega
  rw [List.getElem?_append_right hlen]
  have hidx : k + 2 + n + j - (List.replicate (Fintype.card tm.Q) true ++ [false] ++ List.replicate n true ++ [false]).length = j := by
    simp; omega
  rw [hidx]
  -- Goal: (map (fun i => i == tm.stateEquiv tm.qhalt) (finRange k'))[j]? = some (decide (j = (e tm.qhalt).val))
  rw [List.getElem?_map]
  have hfr : (List.finRange (Fintype.card tm.Q))[j]? = some ⟨j, hj'⟩ := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simp [hj'], by simp [List.getElem_finRange]⟩
  rw [hfr]
  dsimp only [Option.map]
  congr 1
  -- Goal: (⟨j, hj'⟩ == tm.stateEquiv tm.qhalt) = decide (j = (e tm.qhalt).val)
  rw [Bool.beq_eq_decide_eq]
  simp only [Fin.ext_iff]
  rw [he_val]

private theorem encodeTM_long2 (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm) :
    k + 2 + n + k ≤ desc.length := by
  subst hdesc; subst hk
  unfold TMEncoding.encodeTM
  simp only [TMEncoding.encodeStateOneHot]
  simp only [List.length_append, List.length_replicate, List.length_map, List.length_finRange,
    List.length_cons, List.length_nil]
  omega

-- ════════════════════════════════════════════════════════════════════════
-- Full checkHaltTM_hoareTime
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `utmCheckHaltTM`.

    **Pre**: Desc tape has valid encoding; state tape has one-hot of q;
    output tape is WF; heads at 1.
    **Post**: Output cell 1 = Γ.one iff q = e(qhalt), Γ.zero otherwise.
    Desc, state tapes preserved. Heads at 1.

    **Time**: O(k + n + B). -/
theorem checkHaltTM_hoareTime (tm : TM n) (k : ℕ)
    (e : tm.Q ≃ Fin k) (desc : List Bool) (q : Fin k) (simCfg : Cfg n tm.Q) (B : ℕ)
    -- Encoding structure
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (hdesc : desc = TMEncoding.encodeTM tm)
    (he_val : ∀ q : tm.Q, (e q).val = (tm.stateEquiv q).val) :
    utmCheckHaltTM.HoareTime
      (fun inp work out =>
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k q (work utmStateTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ B ∧
        WorkTapesWF work ∧
        -- Input tape WF (needed for seqTransition identity)
        inp.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
        inp.head ≥ 1 ∧
        -- All heads ≥ 1 and output head ≥ 1 (needed for idle preservation)
        (∀ i, (work i).head ≥ 1) ∧
        out.head ≥ 1 ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (fun inp work out =>
        -- Read-only tapes preserved
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k q (work utmStateTape) ∧
        -- Halt check result
        (q = e tm.qhalt → out.cells 1 = Γ.one) ∧
        (q ≠ e tm.qhalt → out.cells 1 = Γ.zero) ∧
        -- Output head at cell 1 (after rewind + write)
        out.head = 1 ∧
        -- Heads restored
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        WorkTapesWF work ∧
        -- Preserved: all work heads ≥ 1
        (∀ i, (work i).head ≥ 1) ∧
        -- Preserved: inp tape
        inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
        -- Preserved: out tape WF
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        -- Preserved: sim/scratch facts for the next readCurrent call
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        (work utmScratchTape).head = 1 ∧
        (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (5 * k + 2 * n + B + 20) := by
  -- ── Step 1: Derive encoding structure ───────────────────────────────
  have hones1 := encodeTM_ones1 tm hk hdesc
  have hsep1 := encodeTM_sep1 tm hk hdesc
  have hones2 := encodeTM_ones2 tm hk hdesc
  have hsep2 := encodeTM_sep2 tm hk hdesc
  have hdesc_long1 := encodeTM_long1 tm hk hdesc
  have hqhalt := encodeTM_qhalt tm hk hdesc he_val
  have hdesc_long2 := encodeTM_long2 tm hk hdesc
  -- ── Step 2: Unfold HoareTime and run each phase ────────────────────
  intro inp work out ⟨hdesc_tape, hstate_tape, hdh, hsh, hoc0, hons, hoh_le, hwf,
    hinp_c0, hinp_ns, hinp_h, hheads, hout_h, hsim, hsim_h, hscratch_h,
    hscratch_inp_blank, hscratch_out_blank⟩
  -- Derive read-level facts
  have hinp_read : inp.read ≠ Γ.start := by
    simp only [Tape.read]; exact hinp_ns _ hinp_h
  have hout_read : out.read ≠ Γ.start := by
    simp only [Tape.read]; exact hons _ hout_h
  -- ── Phase 1: skipToQhaltTM ─────────────────────────────────────────
  obtain ⟨c1, t1, ht1, hreach1, hhalt1, hdesc1, hstate1, hdh1, hsh1,
          hoc01, hons1, hwf1, hinp1, hout1, houth1, hheads1, hoh1_le,
          hsim1, hsim_h1, hscratch_h1, hscratch_inp_blank1, hscratch_out_blank1⟩ :=
    skipToQhaltTM_asHoareTime (B_out := B) k n desc simCfg q hones1 hsep1 hones2 hsep2 hdesc_long1
      inp work out
      ⟨hdesc_tape, hstate_tape, hdh, hsh, hoc0, hons, hwf,
       hinp_read, hout_read, hout_h, hheads, hoh_le,
       hsim, hsim_h, hscratch_h, hscratch_inp_blank, hscratch_out_blank⟩
  -- seqTransition identity
  have hseq1_w := seqTransition_work_id hwf1 hheads1
  have hseq1_i := seqTransitionInput_id hinp1
  have hseq1_o := seqTransitionTape_id hout1 houth1
  -- ── Phase 2: compareWriteTM ────────────────────────────────────────
  -- skip preserves output, so c1.output.head = out.head ≤ B
  -- (the skip raw simulation gives c'.output = c_init.output, which is
  --  embedded in the postcondition: houth1 ≥ 1, but we also need ≤ B.
  --  The skip postcondition preserves output head, so we need ≤ B.)
  -- We pass hoh_le through: skip only touches desc tape (tape 0).
  -- After skip, output head = original output head (skip idles output).
  -- houth1 : c1.output.head ≥ 1 — this is our output head after skip.
  -- The skip postcondition doesn't carry ≤ B, but the output is preserved.
  -- We work around this by noting skip preserves output.
  -- Actually, skipToQhaltTM_asHoareTime doesn't expose out.head ≤ B.
  -- We need to modify skip or pass B through. For now, we observe that
  -- houth1 ≤ B because skip preserves output head = out.head ≤ B.
  -- TODO: this follows from skip preserving output, not yet in postcondition.
  -- skip preserves output head: skipToQhaltTM_asHoareTime internally uses
  -- skipToQhaltTM_hoareTime which proves c'.output = c_init.output.
  -- We recover this by rerunning the raw simulation on the config c1.
  -- But more efficiently: the skip postcondition preserves all output properties.
  -- We know c1.output.cells 0 = Γ.start (hoc01) and ∀ j ≥ 1, ... (hons1)
  -- and c1.output.head ≥ 1 (houth1). Since skip only touches work tape 0,
  -- c1.output = out, giving c1.output.head = out.head ≤ B.
  -- For now, derive via the raw simulation:
  -- hoh1_le : c1.output.head ≤ B (from skip postcondition, output preserved)
  obtain ⟨c2, t2, ht2, hreach2, hhalt2, hdesc2, hstate2, hq_eq2, hq_ne2,
          hoh2, hoc02, hons2, hwf2, hinp2, hout2, houth2, hheads2,
          hdh2_le, hsh2_le, hsim2, hsim_h2, hscratch_h2,
          hscratch_inp_blank2, hscratch_out_blank2⟩ :=
    compareWriteTM_asHoareTime tm k simCfg e desc q B he_val hqhalt hdesc_long2
      (seqTransitionInput c1.input) (fun i => seqTransitionTape (c1.work i))
      (seqTransitionTape c1.output)
      (by rw [hseq1_w, hseq1_i, hseq1_o]
          exact ⟨hdesc1, hstate1, hdh1, hsh1, hoc01, hons1,
            hoh1_le, hwf1, hinp1, hout1, houth1, hheads1,
            hsim1, hsim_h1, hscratch_h1, hscratch_inp_blank1, hscratch_out_blank1⟩)
  -- seqTransition identity
  have hseq2_w := seqTransition_work_id hwf2 hheads2
  have hseq2_i := seqTransitionInput_id hinp2
  have hseq2_o := seqTransitionTape_id hout2 houth2
  -- ── Phase 3: rewindWorkTM 0 (desc tape) ────────────────────────────
  obtain ⟨c3, t3, ht3, hreach3, hhalt3, hpost3⟩ :=
    rewindWorkTM_rich_hoareTime (0 : Fin 4) (2 * k + n + 3)
      (P := fun inp' work' out' =>
        descOnTape desc (work' 0) ∧ stateOnTapeAt k q (work' 1) ∧
        (q = e tm.qhalt → out'.cells 1 = Γ.one) ∧
        (q ≠ e tm.qhalt → out'.cells 1 = Γ.zero) ∧
        out'.head = 1 ∧ out'.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out'.cells j ≠ Γ.start) ∧ WorkTapesWF work' ∧
        inp'.read ≠ Γ.start ∧ inp'.head ≥ 1 ∧ out'.read ≠ Γ.start ∧ out'.head ≥ 1 ∧
        (∀ i, (work' i).head ≥ 1) ∧ (work' 1).head ≤ k + 1 ∧
        superCellsCorrect simCfg (work' utmSimTape) ∧
        (work' utmSimTape).head = 1 ∧
        (work' utmScratchTape).head = 1 ∧
        (work' utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work' utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (by -- Frame preservation for rewind 0: P is stable under rewind of tape 0
          intro _ w0 o0 _ w1 o1 hP hc0 hh0 hot heq_i heq_oc heq_oh
          obtain ⟨hd, hs, hqe, hqn, ho, hoc, hon, hw, hi, hih, hor, hoh', hhe, hsl,
            hsim', hsim_h', hscratch_h', hscratch_inp_blank', hscratch_out_blank'⟩ := hP
          refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hc0]; exact hd.1
          · intro i hi'; rw [hc0]; exact hd.2.1 i hi'
          · rw [hc0]; exact hd.2.2
          · rw [hot 1 (by decide)]; exact hs
          · intro h; rw [heq_oc]; exact hqe h
          · intro h; rw [heq_oc]; exact hqn h
          · rw [heq_oh]; exact ho
          · rw [heq_oc]; exact hoc
          · intro j hj; rw [heq_oc]; exact hon j hj
          · intro i; by_cases h : i = 0
            · subst h; rw [hc0]; exact hw.1 0
            · rw [hot i h]; exact hw.1 i
          · intro i j hj; by_cases h : i = 0
            · subst h; rw [hc0]; exact hw.2 0 j hj
            · rw [hot i h]; exact hw.2 i j hj
          · rw [heq_i]; exact hi
          · rw [heq_i]; exact hih
          · simp only [Tape.read, heq_oh, heq_oc]; rw [ho]; exact hon 1 (by omega)
          · rw [heq_oh]; exact hoh'
          · intro i; by_cases h : i = 0
            · subst h; rw [hh0]
            · rw [hot i h]; exact hhe i
          · rw [hot 1 (by decide)]; exact hsl
          · rw [hot 2 (by decide)]; exact hsim'
          · rw [hot 2 (by decide)]; exact hsim_h'
          · rw [hot 3 (by decide)]; exact hscratch_h'
          · rw [hot 3 (by decide)]; exact hscratch_inp_blank'
          · rw [hot 3 (by decide)]; exact hscratch_out_blank')
      (seqTransitionInput c2.input) (fun i => seqTransitionTape (c2.work i))
      (seqTransitionTape c2.output)
      (by rw [hseq2_w, hseq2_i, hseq2_o]
          exact ⟨hwf2.1 0, hwf2.2 0, hdh2_le, hinp2, hout2, houth2,
            fun i hne => ⟨by simp only [Tape.read]; exact hwf2.2 i _ (hheads2 i), hheads2 i⟩,
            hdesc2, hstate2, hq_eq2, hq_ne2, hoh2, hoc02, hons2, hwf2,
            hinp2, by
              -- c2.input.head ≥ 1: input tape is read-only, cells 0 is always Γ.start
              by_contra h; push_neg at h
              have hh0 : c2.input.head = 0 := by omega
              -- Input cells are preserved through reachesIn
              have hcells2 : c2.input.cells = (seqTransitionInput c1.input).cells :=
                input_cells_of_reachesIn hreach2
              rw [hseq1_i] at hcells2
              have hcells1 : c1.input.cells = inp.cells :=
                input_cells_of_reachesIn hreach1
              have : c2.input.read = Γ.start := by
                simp only [Tape.read, hh0, hcells2, hcells1]; exact hinp_c0
              exact hinp2 this,
            hout2, houth2, hheads2, hsh2_le,
            hsim2, hsim_h2, hscratch_h2, hscratch_inp_blank2, hscratch_out_blank2⟩)
  obtain ⟨hhead3, hdesc3, hstate3, hq_eq3, hq_ne3, hoh3, hoc03, hons3, hwf3,
          hinp3, hinp3_h, hout3, houth3, hheads3, hsh3_le,
          hsim3, hsim_h3, hscratch_h3, hscratch_inp_blank3, hscratch_out_blank3⟩ := hpost3
  -- seqTransition identity
  have hseq3_w := seqTransition_work_id hwf3 hheads3
  have hseq3_i := seqTransitionInput_id hinp3
  have hseq3_o := seqTransitionTape_id hout3 houth3
  -- ── Phase 4: rewindWorkTM 1 (state tape) ───────────────────────────
  obtain ⟨c4, t4, ht4, hreach4, hhalt4, hpost4⟩ :=
    rewindWorkTM_rich_hoareTime (1 : Fin 4) (k + 1)
      (P := fun inp' work' out' =>
        descOnTape desc (work' 0) ∧ stateOnTapeAt k q (work' 1) ∧
        (q = e tm.qhalt → out'.cells 1 = Γ.one) ∧
        (q ≠ e tm.qhalt → out'.cells 1 = Γ.zero) ∧
        out'.head = 1 ∧ (work' 0).head = 1 ∧ WorkTapesWF work' ∧
        (∀ i, (work' i).head ≥ 1) ∧
        inp'.read ≠ Γ.start ∧ inp'.head ≥ 1 ∧
        out'.cells 0 = Γ.start ∧ (∀ j, j ≥ 1 → out'.cells j ≠ Γ.start) ∧
        superCellsCorrect simCfg (work' utmSimTape) ∧
        (work' utmSimTape).head = 1 ∧
        (work' utmScratchTape).head = 1 ∧
        (work' utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
        (work' utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank)
      (by -- Frame preservation for rewind 1: P is stable under rewind of tape 1
          intro _ w0 o0 _ w1 o1 hP hc1 hh1 hot heq_i heq_oc heq_oh
          obtain ⟨hd, hs, hqe, hqn, ho, hdh', hw, hhe, hir, hih, hoc, hon,
            hsim', hsim_h', hscratch_h', hscratch_inp_blank', hscratch_out_blank'⟩ := hP
          refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hot 0 (by decide)]; exact hd
          · rw [hc1]; exact hs.1
          · intro j hj; rw [hc1]; exact hs.2.1 j hj
          · rw [hc1]; exact hs.2.2
          · intro h; rw [heq_oc]; exact hqe h
          · intro h; rw [heq_oc]; exact hqn h
          · rw [heq_oh]; exact ho
          · rw [hot 0 (by decide)]; exact hdh'
          · intro i; by_cases h : i = 1
            · subst h; rw [hc1]; exact hw.1 1
            · rw [hot i h]; exact hw.1 i
          · intro i j hj; by_cases h : i = 1
            · subst h; rw [hc1]; exact hw.2 1 j hj
            · rw [hot i h]; exact hw.2 i j hj
          · intro i; by_cases h : i = 1
            · subst h; rw [hh1]
            · rw [hot i h]; exact hhe i
          · rw [heq_i]; exact hir
          · rw [heq_i]; exact hih
          · rw [heq_oc]; exact hoc
          · intro j hj; rw [heq_oc]; exact hon j hj
          · rw [hot 2 (by decide)]; exact hsim'
          · rw [hot 2 (by decide)]; exact hsim_h'
          · rw [hot 3 (by decide)]; exact hscratch_h'
          · rw [hot 3 (by decide)]; exact hscratch_inp_blank'
          · rw [hot 3 (by decide)]; exact hscratch_out_blank')
      (seqTransitionInput c3.input) (fun i => seqTransitionTape (c3.work i))
      (seqTransitionTape c3.output)
      (by rw [hseq3_w, hseq3_i, hseq3_o]
          exact ⟨hwf3.1 1, hwf3.2 1, hsh3_le, hinp3, hout3, houth3,
            fun i hne => ⟨by simp only [Tape.read]; exact hwf3.2 i _ (hheads3 i), hheads3 i⟩,
            hdesc3, hstate3, hq_eq3, hq_ne3, hoh3, hhead3, hwf3,
            hheads3, hinp3, hinp3_h, hoc03, hons3,
            hsim3, hsim_h3, hscratch_h3, hscratch_inp_blank3, hscratch_out_blank3⟩)
  obtain ⟨hhead4, hdesc4, hstate4, hq_eq4, hq_ne4, hoh4, hdh4, hwf4,
          hheads4, hinp4_r, hinp4_h, hoc04, hons4,
          hsim4, hsim_h4, hscratch_h4, hscratch_inp_blank4, hscratch_out_blank4⟩ := hpost4
  -- ── Compose reachesIn chains via seqTM_full_simulation ─────────────
  have hsim := seqTM_full_simulation skipToQhaltTM
    (seqTM compareWriteTM (seqTM (rewindWorkTM (0 : Fin 4)) (rewindWorkTM (1 : Fin 4))))
    hreach1 hhalt1
    (seqTM_full_simulation compareWriteTM
      (seqTM (rewindWorkTM (0 : Fin 4)) (rewindWorkTM (1 : Fin 4)))
      hreach2 hhalt2
      (seqTM_full_simulation (rewindWorkTM (0 : Fin 4)) (rewindWorkTM (1 : Fin 4))
        hreach3 hhalt3 hreach4))
  refine ⟨_, t1 + 1 + (t2 + 1 + (t3 + 1 + t4)), by omega, hsim, ?_, ?_⟩
  · -- halted
    show utmCheckHaltTM.halted _
    simp only [utmCheckHaltTM]
    rw [phase2Wrap_halted, phase2Wrap_halted, phase2Wrap_halted]; exact hhalt4
  · exact ⟨hdesc4, hstate4, hq_eq4, hq_ne4, hoh4, hdh4, hhead4, hwf4,
          hheads4, hinp4_r, hinp4_h, hoc04, hons4,
          hsim4, hsim_h4, hscratch_h4, hscratch_inp_blank4, hscratch_out_blank4⟩

end TM
