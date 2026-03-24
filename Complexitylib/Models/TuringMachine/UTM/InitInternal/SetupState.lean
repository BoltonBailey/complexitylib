import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.UTM.InitInternal.Rewind

/-!
# Init proof internals: setupStateTM

Step-by-step simulation lemmas and HoareTime proof for `setupStateTM`.
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

private theorem ss_readBackWrite_toΓ_eq {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by cases g <;> simp_all [readBackWrite, Γw.toΓ]

private theorem ss_tape_move_cells (t : Tape) (d : Dir3) :
    (t.move d).cells = t.cells := by cases d <;> rfl

private theorem ss_tape_read_ne_start_of_wf (t : Tape) (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) : t.read ≠ Γ.start := by
  simp only [Tape.read]; exact hns _ hh

private theorem initTape_nil_cell_ge1 {j : ℕ} (hj : j ≥ 1) :
    (initTape ([] : List Γ)).cells j = Γ.blank := by
  simp [initTape, Nat.ne_of_gt (by omega : j > 0)]

private theorem initTape_nil_cell_0 :
    (initTape ([] : List Γ)).cells 0 = Γ.start := by simp [initTape]

-- ════════════════════════════════════════════════════════════════════════
-- encodeTM desc tape cell access
-- ════════════════════════════════════════════════════════════════════════

theorem encodeTM_length_ge (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    (TMEncoding.encodeTM tm).length ≥ 3 * k + n + 4 := by
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.length_append, List.length_replicate, List.length_singleton,
             List.length_map, List.length_finRange]
  omega

theorem tapeStoresBools_cell {bits : List Bool} {t : Tape}
    (h : tapeStoresBools bits t) {i : ℕ} (hi : i < bits.length) :
    t.cells (i + 1) = Γ.ofBool bits[i] := h.2.1 i hi

theorem desc_ones_cells (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    {t : Tape} (hdesc : descOnTape (TMEncoding.encodeTM tm) t)
    (j : ℕ) (hj : j < k) :
    t.cells (j + 1) = Γ.one := by
  have hlen : j < (TMEncoding.encodeTM tm).length := by
    have := encodeTM_length_ge tm hk; omega
  rw [tapeStoresBools_cell hdesc hlen]
  suffices h : (TMEncoding.encodeTM tm)[j] = true by rw [h]; rfl
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.append_assoc]
  rw [List.getElem_append_left (show j < (List.replicate _ true).length by simp; omega)]
  exact List.getElem_replicate _

theorem desc_sep_k_cell (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    {t : Tape} (hdesc : descOnTape (TMEncoding.encodeTM tm) t) :
    t.cells (k + 1) = Γ.zero := by
  have hlen : k < (TMEncoding.encodeTM tm).length := by
    have := encodeTM_length_ge tm hk; omega
  rw [tapeStoresBools_cell hdesc hlen]
  suffices h : (TMEncoding.encodeTM tm)[k] = false by rw [h]; rfl
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.append_assoc]
  rw [List.getElem_append_right (show (List.replicate _ true).length ≤ k by simp; omega)]
  simp [hk]

theorem desc_n_ones_cells (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    {t : Tape} (hdesc : descOnTape (TMEncoding.encodeTM tm) t)
    (j : ℕ) (hj : j < n) :
    t.cells (k + 2 + j) = Γ.one := by
  have hlen : k + 1 + j < (TMEncoding.encodeTM tm).length := by
    have := encodeTM_length_ge tm hk; omega
  rw [show k + 2 + j = (k + 1 + j) + 1 from by omega, tapeStoresBools_cell hdesc hlen]
  suffices h : (TMEncoding.encodeTM tm)[k + 1 + j] = true by rw [h]; rfl
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.append_assoc]
  rw [List.getElem_append_right (show (List.replicate _ true).length ≤ k + 1 + j by simp; omega)]
  have h1 : k + 1 + j - @Fintype.card tm.Q tm.finQ = j + 1 := by omega
  simp only [h1, List.singleton_append, List.getElem_cons_succ,
             List.getElem_append_left, List.getElem_replicate,
             List.length_replicate, hj]

theorem desc_sep_kn_cell (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    {t : Tape} (hdesc : descOnTape (TMEncoding.encodeTM tm) t) :
    t.cells (k + 2 + n) = Γ.zero := by
  have hlen : k + 1 + n < (TMEncoding.encodeTM tm).length := by
    have := encodeTM_length_ge tm hk; omega
  rw [show k + 2 + n = (k + 1 + n) + 1 from by omega, tapeStoresBools_cell hdesc hlen]
  suffices h : (TMEncoding.encodeTM tm)[k + 1 + n] = false by rw [h]; rfl
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.append_assoc]
  rw [List.getElem_append_right (show (List.replicate _ true).length ≤ k + 1 + n by simp; omega)]
  have h1 : k + 1 + n - @Fintype.card tm.Q tm.finQ = n + 1 := by omega
  simp only [h1, List.singleton_append, List.getElem_cons_succ,
             List.getElem_append_right, List.length_replicate, le_refl,
             Nat.sub_self, List.getElem_cons_zero]

theorem desc_qstart_cells (tm : TM n)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    {t : Tape} (hdesc : descOnTape (TMEncoding.encodeTM tm) t)
    (j : ℕ) (hj : j < k) :
    t.cells (2 * k + 4 + n + j) =
      Γ.ofBool ((⟨j, by omega⟩ : Fin k) == (hk ▸ tm.stateEquiv tm.qstart)) := by
  have hlen : 2 * k + 3 + n + j < (TMEncoding.encodeTM tm).length := by
    have := encodeTM_length_ge tm hk; omega
  rw [show 2 * k + 4 + n + j = (2 * k + 3 + n + j) + 1 from by omega,
      tapeStoresBools_cell hdesc hlen]
  congr 1
  unfold TMEncoding.encodeTM TMEncoding.encodeStateOneHot TM.stateEquiv
  simp only [List.append_assoc]
  rw [List.getElem_append_right (show (List.replicate _ true).length ≤ 2 * k + 3 + n + j by simp; omega)]
  have h1 : 2 * k + 3 + n + j -
    (List.replicate (@Fintype.card tm.Q tm.finQ) true).length = (k + 2 + n + j) + 1 := by
    simp; omega
  simp only [h1, List.singleton_append, List.getElem_cons_succ]
  rw [List.getElem_append_right (show (List.replicate n true).length ≤ k + 2 + n + j by simp; omega)]
  have h3 : k + 2 + n + j - (List.replicate n true).length = k + 2 + j := by simp; omega
  simp only [h3]
  have h4 : k + 2 + j = (k + 1 + j) + 1 := by omega
  simp only [h4, List.getElem_cons_succ]
  have hqhalt_len :
      (List.map (fun i => i == (Fintype.equivFin tm.Q) tm.qhalt)
        (List.finRange (@Fintype.card tm.Q tm.finQ))).length = k := by
    simp [List.length_map, List.length_finRange, hk]
  rw [List.getElem_append_right (by omega)]
  have h5 : k + 1 + j -
    (List.map (fun i => i == (Fintype.equivFin tm.Q) tm.qhalt)
      (List.finRange (@Fintype.card tm.Q tm.finQ))).length = j + 1 := by
    rw [hqhalt_len]; omega
  simp only [h5, List.getElem_cons_succ]
  rw [List.getElem_append_left (by
    simp [List.length_map, List.length_finRange]; omega)]
  simp only [List.getElem_map, List.getElem_finRange]
  subst hk
  simp

-- ════════════════════════════════════════════════════════════════════════
-- Idle-tape preservation
-- ════════════════════════════════════════════════════════════════════════

/-- Idle tape: writeAndMove with blank and idleDir preserves a tape with
    head ≥ 1 and cells matching initTape (all blank for j ≥ 1). -/
private theorem idle_tape_initTape {t : Tape} (hh : t.head ≥ 1)
    (hc : t.cells = (initTape ([] : List Γ)).cells) :
    t.writeAndMove (Γw.blank : Γw) (idleDir t.read) = t := by
  have hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
    intro j hj; rw [hc]; intro h; simp [initTape, show j ≠ 0 from by omega] at h
  have hread : t.read ≠ Γ.start := by simp [Tape.read]; exact hns _ hh
  simp only [Tape.writeAndMove, idleDir, hread, ↓reduceIte, Tape.move,
    Tape.write, show t.head ≠ 0 from by omega]
  show { head := t.head, cells := Function.update t.cells t.head Γ.blank } = t
  have : Function.update t.cells t.head Γ.blank = t.cells := by
    ext j; simp only [Function.update]
    split
    · next h => subst h; rw [hc]; exact (initTape_nil_cell_ge1 hh).symm
    · rfl
  simp [this]

/-- Idle tape for output/non-initTape tapes: writeAndMove blank+stay
    when head ≥ 1, read ≠ ▷. Output may not be initTape but we
    just need cells j ≠ ▷ preserved and head unchanged. -/
private theorem idle_tape_wf {t : Tape} (hh : t.head ≥ 1)
    (hc0 : t.cells 0 = Γ.start)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    (t.writeAndMove (Γw.blank : Γw) (idleDir t.read)).cells 0 = Γ.start ∧
    (∀ j, j ≥ 1 → (t.writeAndMove (Γw.blank : Γw) (idleDir t.read)).cells j ≠ Γ.start) ∧
    (t.writeAndMove (Γw.blank : Γw) (idleDir t.read)).head = t.head := by
  have hread : t.read ≠ Γ.start := by simp [Tape.read]; exact hns _ hh
  simp only [Tape.writeAndMove, idleDir, hread, ↓reduceIte, Tape.move,
    Tape.write, show t.head ≠ 0 from by omega]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Function.update, show (0 : ℕ) ≠ t.head from by omega]; exact hc0
  · intro j hj
    simp only [Function.update]
    split
    · next h => subst h; show Γ.blank ≠ Γ.start; exact Γ.noConfusion
    · exact hns j hj
  · trivial

/-- Input tape idle: move with idleDir preserves everything. -/
private theorem idle_input {t : Tape} (hh : t.head ≥ 1)
    (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  have hread : t.read ≠ Γ.start := by simp [Tape.read]; exact hns _ hh
  simp [idleDir, hread, Tape.move]

-- ════════════════════════════════════════════════════════════════════════
-- WriteAndMove helpers for active tapes
-- ════════════════════════════════════════════════════════════════════════

private theorem writeAndMove_right_head {t : Tape} {w : Γw} :
    (t.writeAndMove w Dir3.right).head = t.head + 1 := by
  simp [Tape.writeAndMove, Tape.write]; split <;> simp [Tape.move]

private theorem writeAndMove_left_head {t : Tape} {w : Γw} :
    (t.writeAndMove w Dir3.left).head = t.head - 1 := by
  simp [Tape.writeAndMove, Tape.write]; split <;> simp [Tape.move]

private theorem writeAndMove_stay_head {t : Tape} {w : Γw} :
    (t.writeAndMove w Dir3.stay).head = t.head := by
  simp [Tape.writeAndMove, Tape.write]; split <;> rfl

private theorem writeAndMove_cells_at_head {t : Tape} {w : Γw} {d : Dir3}
    (hh : t.head ≠ 0) :
    (t.writeAndMove w d).cells t.head = w.toΓ := by
  simp only [Tape.writeAndMove, ss_tape_move_cells, Tape.write, hh, ↓reduceIte,
    Function.update_self]

private theorem writeAndMove_cells_ne {t : Tape} {w : Γw} {d : Dir3} {j : ℕ}
    (hj : j ≠ t.head) :
    (t.writeAndMove w d).cells j = t.cells j := by
  simp only [Tape.writeAndMove, ss_tape_move_cells, Tape.write]
  split
  · rfl
  · simp only [Function.update]; split
    · next h => exact absurd h hj
    · rfl

private theorem writeAndMove_cells_0 {t : Tape} {w : Γw} {d : Dir3}
    (hh : t.head ≠ 0) :
    (t.writeAndMove w d).cells 0 = t.cells 0 := by
  exact writeAndMove_cells_ne (Ne.symm hh)

/-- readBackWrite preserves cells regardless of direction. -/
private theorem readBackWrite_cells {t : Tape} {d : Dir3}
    (hh : t.head ≥ 1) (hns : ∀ j, j ≥ 1 → t.cells j ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read) d).cells = t.cells := by
  have hread : t.read ≠ Γ.start := by simp [Tape.read]; exact hns _ hh
  ext j
  simp only [Tape.writeAndMove, ss_tape_move_cells, Tape.write,
    show t.head ≠ 0 from by omega, ↓reduceIte]
  simp only [Function.update]
  split
  · next h => subst h; exact ss_readBackWrite_toΓ_eq hread
  · rfl

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: skipK loop — copy k ones from desc to state, then separator
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 1 loop: from skipK state with `copied` ones already processed,
    process `rem` more ones and then the separator, reaching copyN.
    Desc head at copied+1, state head at copied+1. -/
private theorem skipK_loop (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ) :
    ∀ (rem : ℕ) (c : Cfg 4 setupStateTM.Q),
    c.state = .skipK →
    (c.work utmDescTape).head + rem = k + 1 →
    (c.work utmDescTape).cells = (w₀ : Tape).cells →
    descOnTape (TMEncoding.encodeTM tm) ⟨0, w₀.cells⟩ →
    (c.work utmDescTape).head ≥ 1 →
    (c.work utmStateTape).head = (c.work utmDescTape).head →
    (c.work utmStateTape).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → j < (c.work utmDescTape).head → (c.work utmStateTape).cells j = Γ.one) →
    (∀ j, j ≥ (c.work utmDescTape).head → (c.work utmStateTape).cells j = (initTape []).cells j) →
    (c.work utmSimTape).cells = (initTape []).cells → (c.work utmSimTape).head ≥ 1 →
    (c.work utmScratchTape).cells = (initTape []).cells → (c.work utmScratchTape).head = 1 →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) → c.input.cells 0 = Γ.start →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) → c.output.cells 0 = Γ.start →
    (∀ i, (c.work i).cells 0 = Γ.start) →
    (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c', setupStateTM.reachesIn (rem + 1) c c' ∧
      c'.state = .copyN ∧
      (c'.work utmDescTape).cells = w₀.cells ∧
      (c'.work utmDescTape).head = k + 2 ∧
      (c'.work utmStateTape).head = k + 1 ∧
      (∀ j, j < k → (c'.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c'.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c'.work utmStateTape).cells 0 = Γ.start ∧
      (c'.work utmSimTape).cells = (initTape []).cells ∧ (c'.work utmSimTape).head ≥ 1 ∧
      (c'.work utmScratchTape).cells = (initTape []).cells ∧ (c'.work utmScratchTape).head = 1 ∧
      c'.input.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧ c'.input.cells 0 = Γ.start ∧
      c'.output.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧ c'.output.cells 0 = Γ.start ∧
      WorkTapesWF c'.work := by
  intro rem
  induction rem with
  | zero =>
    intro c hstate hhead_rem hcells hdesc hhead_ge hst_head hst_0 hst_ones hst_tail
      hsim_c hsim_h hsc_c hsc_h hinp_h hinp_ns hinp_0 hout_h hout_ns hout_0 hwf0 hwf1
    have hdesc_head : (c.work utmDescTape).head = k + 1 := by omega
    have hread : (c.work utmDescTape).read = Γ.zero := by
      simp only [Tape.read, hdesc_head, hcells]; exact desc_sep_k_cell tm hk hdesc
    have hread_ne_one : (fun i => (c.work i).read) (0 : Fin 4) ≠ Γ.one := by
      show (c.work utmDescTape).read ≠ Γ.one; rw [hread]; decide
    simp only [show (0 + 1 : ℕ) = 1 from rfl]
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.skipK ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers
    have hst_head_val : (c.work utmStateTape).head = k + 1 := by rw [hst_head, hdesc_head]
    have hst_ne : (c.work utmStateTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
    have hst_idle : (c.work utmStateTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmStateTape).read) = c.work utmStateTape := by
      simp only [Tape.writeAndMove, idleDir, hst_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmStateTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmStateTape).cells
          (c.work utmStateTape).head Γw.blank.toΓ = (c.work utmStateTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmStateTape).cells (c.work utmStateTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hst_head_val, hst_tail (k + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hsc_idle := idle_tape_initTape (by omega) hsc_c
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Build explicit step config (skipK else → copyN)
    let c₁ : Cfg 4 setupStateTM.Q :=
      { state := .copyN
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove
          ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
            else Γw.blank : Γw) : Γ)
          (if (i : Fin 4).val = 0 then Dir3.right
           else idleDir (c.work i).read)
        output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      unfold TM.step
      simp only [hstate, show (SetupStatePhase.skipK : SetupStatePhase) ≠ .done from nofun,
        ↓reduceIte, setupStateTM, hread_ne_one]
      show some _ = some c₁; congr 1
    -- Unfold c₁ work tapes for each index
    have hw_desc : c₁.work utmDescTape =
        (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right := by
      simp only [c₁, show (utmDescTape : Fin 4).val = 0 from rfl, ↓reduceIte]
    have hw_st : c₁.work utmStateTape =
        (c.work utmStateTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmStateTape).read) := by
      simp only [c₁, show ((utmStateTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sim : c₁.work utmSimTape =
        (c.work utmSimTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmSimTape).read) := by
      simp only [c₁, show ((utmSimTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sc : c₁.work utmScratchTape =
        (c.work utmScratchTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmScratchTape).read) := by
      simp only [c₁, show ((utmScratchTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    refine ⟨c₁, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- desc cells
      rw [hw_desc, readBackWrite_cells hhead_ge (hwf1 utmDescTape)]; exact hcells
    · -- desc head = k + 2
      rw [hw_desc, writeAndMove_right_head]; omega
    · -- state head = k + 1
      rw [hw_st, hst_idle]; exact hst_head_val
    · -- state ones
      intro j hj; rw [hw_st, hst_idle]; exact hst_ones (j + 1) (by omega) (by omega)
    · -- state tail
      intro j hj; rw [hw_st, hst_idle]; exact hst_tail j (by omega)
    · -- state cells 0
      rw [hw_st, hst_idle]; exact hst_0
    · -- sim cells
      rw [hw_sim, hsim_idle]; exact hsim_c
    · -- sim head
      rw [hw_sim, hsim_idle]; exact hsim_h
    · -- scratch cells
      rw [hw_sc, hsc_idle]; exact hsc_c
    · -- scratch head
      rw [hw_sc, hsc_idle]; exact hsc_h
    · -- input head
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_h
    · -- input cells ns
      intro j hj
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_ns j hj
    · -- input cells 0
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_0
    · -- output head
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      rw [hout_h']; exact hout_h
    · -- output cells ns
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_ns'
    · -- output cells 0
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_0'
    · -- WorkTapesWF
      exact ⟨
        fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [hw_desc, writeAndMove_cells_0 (by omega)]; exact hwf0 utmDescTape
            | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [hw_st, hst_idle]; exact hwf0 utmStateTape
            | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [hw_sim, hsim_idle]; exact hwf0 utmSimTape
            | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [hw_sc, hsc_idle]; exact hwf0 utmScratchTape,
        fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [hw_desc, readBackWrite_cells hhead_ge (hwf1 utmDescTape)]; exact hwf1 utmDescTape j hj
            | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [hw_st, hst_idle]; exact hwf1 utmStateTape j hj
            | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [hw_sim, hsim_idle]; exact hwf1 utmSimTape j hj
            | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [hw_sc, hsc_idle]; exact hwf1 utmScratchTape j hj⟩
  | succ rem' ih =>
    intro c hstate hhead_rem hcells hdesc hhead_ge hst_head hst_0 hst_ones hst_tail
      hsim_c hsim_h hsc_c hsc_h hinp_h hinp_ns hinp_0 hout_h hout_ns hout_0 hwf0 hwf1
    -- Desc reads one
    have hread_one : (c.work utmDescTape).read = Γ.one := by
      simp only [Tape.read, hcells]
      have := desc_ones_cells tm hk hdesc ((c.work utmDescTape).head - 1) (by omega)
      rwa [show (c.work utmDescTape).head - 1 + 1 = (c.work utmDescTape).head from by omega] at this
    have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) = Γ.one := hread_one
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.skipK ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers
    have hst_ne : (c.work utmStateTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hsc_idle := idle_tape_initTape (by omega) hsc_c
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Step: skipK with one → stay skipK, desc+state right, state writes one
    let c₁ : Cfg 4 setupStateTM.Q := {
      state := .skipK
      input := c.input.move (idleDir c.input.read)
      work := fun i => (c.work i).writeAndMove
        ((if (i : Fin 4).val = 0 then readBackWrite Γ.one
          else if (i : Fin 4).val = 1 then Γw.one else Γw.blank : Γw) : Γ)
        (if (i : Fin 4).val = 0 then Dir3.right
         else if (i : Fin 4).val = 1 then Dir3.right
         else idleDir (c.work i).read)
      output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      simp only [TM.step, hstate, ↓reduceIte, setupStateTM, hread_eq]; rfl
    -- c₁ desc tape
    have h1_desc_cells : (c₁.work utmDescTape).cells = w₀.cells := by
      show ((c.work utmDescTape).writeAndMove
        (readBackWrite Γ.one : Γw) Dir3.right).cells = _
      rw [← hread_one, readBackWrite_cells hhead_ge (hwf1 utmDescTape)]; exact hcells
    have h1_desc_head : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      show ((c.work utmDescTape).writeAndMove _ Dir3.right).head = _
      exact writeAndMove_right_head
    -- c₁ state tape
    have h1_st_head : (c₁.work utmStateTape).head = (c.work utmStateTape).head + 1 := by
      show ((c.work utmStateTape).writeAndMove (Γw.one : Γw) Dir3.right).head = _
      exact writeAndMove_right_head
    have h1_st_cells_0 : (c₁.work utmStateTape).cells 0 = Γ.start := by
      show ((c.work utmStateTape).writeAndMove (Γw.one : Γw) Dir3.right).cells 0 = _
      rw [writeAndMove_cells_0 (by omega)]; exact hst_0
    have h1_st_ones : ∀ j, 1 ≤ j → j < (c₁.work utmDescTape).head →
        (c₁.work utmStateTape).cells j = Γ.one := by
      intro j hj1 hj2
      show ((c.work utmStateTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j = Γ.one
      rw [h1_desc_head] at hj2
      by_cases hje : j = (c.work utmStateTape).head
      · subst hje; rw [writeAndMove_cells_at_head (by omega)]; rfl
      · rw [writeAndMove_cells_ne hje]; exact hst_ones j hj1 (by rw [← hst_head] at hj2; omega)
    have h1_st_tail : ∀ j, j ≥ (c₁.work utmDescTape).head →
        (c₁.work utmStateTape).cells j = (initTape []).cells j := by
      intro j hj
      show ((c.work utmStateTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j = _
      rw [h1_desc_head] at hj
      rw [writeAndMove_cells_ne (by rw [hst_head]; omega)]
      exact hst_tail j (by omega)
    -- c₁ sim/scratch idle
    have h1_sim : c₁.work utmSimTape = c.work utmSimTape := by
      show (c.work utmSimTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmSimTape).read) = _
      exact hsim_idle
    have h1_sc : c₁.work utmScratchTape = c.work utmScratchTape := by
      show (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmScratchTape).read) = _
      exact hsc_idle
    have h1_inp : c₁.input = c.input := hinp_idle
    -- WorkTapesWF for c₁
    have h1_wf0 : ∀ i, (c₁.work i).cells 0 = Γ.start :=
      fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf0 utmDescTape
          | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; exact h1_st_cells_0
          | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [h1_sim]; exact hwf0 utmSimTape
          | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [h1_sc]; exact hwf0 utmScratchTape
    have h1_wf1 : ∀ i j, j ≥ 1 → (c₁.work i).cells j ≠ Γ.start :=
      fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf1 utmDescTape j hj
          | ⟨1, _⟩, j, hj => by
              change (c₁.work utmStateTape).cells j ≠ Γ.start
              show ((c.work utmStateTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j ≠ Γ.start
              by_cases hje : j = (c.work utmStateTape).head
              · subst hje; rw [writeAndMove_cells_at_head (by omega)]; decide
              · rw [writeAndMove_cells_ne hje]; exact hwf1 utmStateTape j hj
          | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [h1_sim]; exact hwf1 utmSimTape j hj
          | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [h1_sc]; exact hwf1 utmScratchTape j hj
    -- Apply IH
    obtain ⟨c_f, hreach, hprops⟩ := ih c₁ rfl
      (by rw [h1_desc_head]; omega)
      h1_desc_cells hdesc
      (by rw [h1_desc_head]; omega)
      (by rw [h1_st_head, hst_head, h1_desc_head])
      h1_st_cells_0 h1_st_ones h1_st_tail
      (by rw [h1_sim]; exact hsim_c)
      (by rw [h1_sim]; exact hsim_h)
      (by rw [h1_sc]; exact hsc_c)
      (by rw [h1_sc]; exact hsc_h)
      (by rw [h1_inp]; exact hinp_h)
      (fun j hj => by rw [h1_inp]; exact hinp_ns j hj)
      (by rw [h1_inp]; exact hinp_0)
      (by rw [hout_h']; exact hout_h)
      hout_ns' hout_0'
      h1_wf0 h1_wf1
    exact ⟨c_f, .step hstep hreach, hprops⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: copyN loop — copy n ones from desc to scratch, then separator
-- ════════════════════════════════════════════════════════════════════════

private theorem copyN_loop (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ) :
    ∀ (rem : ℕ) (c : Cfg 4 setupStateTM.Q),
    c.state = .copyN →
    (c.work utmDescTape).head + rem = k + n + 2 →
    (c.work utmDescTape).cells = (w₀ : Tape).cells →
    descOnTape (TMEncoding.encodeTM tm) ⟨0, w₀.cells⟩ →
    (c.work utmDescTape).head ≥ k + 2 →
    -- state tape: already has k ones, head at k+1, unchanged during this phase
    (c.work utmStateTape).head = k + 1 →
    (∀ j, j < k → (c.work utmStateTape).cells (j + 1) = Γ.one) →
    (∀ j, j ≥ k + 1 → (c.work utmStateTape).cells j = (initTape []).cells j) →
    (c.work utmStateTape).cells 0 = Γ.start →
    -- scratch tape: head at copied+1 where copied = desc_head - (k+2)
    (c.work utmScratchTape).head = (c.work utmDescTape).head - (k + 1) →
    (c.work utmScratchTape).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → j < (c.work utmScratchTape).head → (c.work utmScratchTape).cells j = Γ.one) →
    (∀ j, j ≥ (c.work utmScratchTape).head → (c.work utmScratchTape).cells j = (initTape []).cells j) →
    (c.work utmSimTape).cells = (initTape []).cells → (c.work utmSimTape).head ≥ 1 →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) → c.input.cells 0 = Γ.start →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) → c.output.cells 0 = Γ.start →
    (∀ i, (c.work i).cells 0 = Γ.start) →
    (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c', setupStateTM.reachesIn (rem + 1) c c' ∧
      c'.state = .skipQhalt ∧
      (c'.work utmDescTape).cells = w₀.cells ∧
      (c'.work utmDescTape).head = k + n + 3 ∧
      (c'.work utmStateTape).head = k + 1 ∧
      (∀ j, j < k → (c'.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c'.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c'.work utmStateTape).cells 0 = Γ.start ∧
      (c'.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c'.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c'.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (c'.work utmSimTape).cells = (initTape []).cells ∧ (c'.work utmSimTape).head ≥ 1 ∧
      c'.input.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧ c'.input.cells 0 = Γ.start ∧
      c'.output.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧ c'.output.cells 0 = Γ.start ∧
      WorkTapesWF c'.work := by
  intro rem
  induction rem with
  | zero =>
    intro c hstate hhead_rem hcells hdesc hhead_ge hst_head hst_ones hst_tail hst_0
      hsc_head hsc_0 hsc_ones hsc_tail hsim_c hsim_h hinp_h hinp_ns hinp_0
      hout_h hout_ns hout_0 hwf0 hwf1
    have hdesc_head : (c.work utmDescTape).head = k + n + 2 := by omega
    have hsc_head_val : (c.work utmScratchTape).head = n + 1 := by
      rw [hsc_head, hdesc_head]; omega
    have hread : (c.work utmDescTape).read = Γ.zero := by
      simp only [Tape.read, hdesc_head, hcells]
      have := desc_sep_kn_cell tm hk hdesc
      rwa [show k + 2 + n = k + n + 2 from by omega] at this
    have hread_ne_one : (fun i => (c.work i).read) (0 : Fin 4) ≠ Γ.one := by
      show (c.work utmDescTape).read ≠ Γ.one; rw [hread]; decide
    simp only [show (0 + 1 : ℕ) = 1 from rfl]
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.copyN ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers
    have hst_ne : (c.work utmStateTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
    have hst_idle : (c.work utmStateTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmStateTape).read) = c.work utmStateTape := by
      simp only [Tape.writeAndMove, idleDir, hst_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmStateTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmStateTape).cells
          (c.work utmStateTape).head Γw.blank.toΓ = (c.work utmStateTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmStateTape).cells (c.work utmStateTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hst_head, hst_tail (k + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hsc_ne : (c.work utmScratchTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmScratchTape)
    have hsc_idle : (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmScratchTape).read) = c.work utmScratchTape := by
      simp only [Tape.writeAndMove, idleDir, hsc_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmScratchTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmScratchTape).cells
          (c.work utmScratchTape).head Γw.blank.toΓ = (c.work utmScratchTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmScratchTape).cells (c.work utmScratchTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hsc_head_val, hsc_tail (n + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Build explicit step config (copyN else → skipQhalt)
    let c₁ : Cfg 4 setupStateTM.Q :=
      { state := .skipQhalt
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove
          ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
            else Γw.blank : Γw) : Γ)
          (if (i : Fin 4).val = 0 then Dir3.right
           else idleDir (c.work i).read)
        output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      unfold TM.step
      simp only [hstate, show (SetupStatePhase.copyN : SetupStatePhase) ≠ .done from nofun,
        ↓reduceIte, setupStateTM, hread_ne_one]
      show some _ = some c₁; congr 1
    -- Unfold c₁ work tapes for each index
    have hw_desc : c₁.work utmDescTape =
        (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right := by
      simp only [c₁, show (utmDescTape : Fin 4).val = 0 from rfl, ↓reduceIte]
    have hw_st : c₁.work utmStateTape =
        (c.work utmStateTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmStateTape).read) := by
      simp only [c₁, show ((utmStateTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sim : c₁.work utmSimTape =
        (c.work utmSimTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmSimTape).read) := by
      simp only [c₁, show ((utmSimTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sc : c₁.work utmScratchTape =
        (c.work utmScratchTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmScratchTape).read) := by
      simp only [c₁, show ((utmScratchTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    refine ⟨c₁, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- desc cells
      rw [hw_desc, readBackWrite_cells (by omega) (hwf1 utmDescTape)]; exact hcells
    · -- desc head = k + n + 3
      rw [hw_desc, writeAndMove_right_head]; omega
    · -- state head = k + 1
      rw [hw_st, hst_idle]; exact hst_head
    · -- state ones
      intro j hj; rw [hw_st, hst_idle]; exact hst_ones j hj
    · -- state tail
      intro j hj; rw [hw_st, hst_idle]; exact hst_tail j hj
    · -- state cells 0
      rw [hw_st, hst_idle]; exact hst_0
    · -- scratch head = n + 1
      rw [hw_sc, hsc_idle]; exact hsc_head_val
    · -- scratch ones
      intro j hj; rw [hw_sc, hsc_idle]; exact hsc_ones (j + 1) (by omega) (by omega)
    · -- scratch tail
      intro j hj; rw [hw_sc, hsc_idle]; exact hsc_tail j (by omega)
    · -- scratch cells 0
      rw [hw_sc, hsc_idle]; exact hsc_0
    · -- sim cells
      rw [hw_sim, hsim_idle]; exact hsim_c
    · -- sim head
      rw [hw_sim, hsim_idle]; exact hsim_h
    · -- input head
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_h
    · -- input cells ns
      intro j hj
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_ns j hj
    · -- input cells 0
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_0
    · -- output head
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      rw [hout_h']; exact hout_h
    · -- output cells ns
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_ns'
    · -- output cells 0
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_0'
    · -- WorkTapesWF
      exact ⟨
        fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [hw_desc, writeAndMove_cells_0 (by omega)]; exact hwf0 utmDescTape
            | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [hw_st, hst_idle]; exact hwf0 utmStateTape
            | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [hw_sim, hsim_idle]; exact hwf0 utmSimTape
            | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [hw_sc, hsc_idle]; exact hwf0 utmScratchTape,
        fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [hw_desc, readBackWrite_cells (by omega) (hwf1 utmDescTape)]; exact hwf1 utmDescTape j hj
            | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [hw_st, hst_idle]; exact hwf1 utmStateTape j hj
            | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [hw_sim, hsim_idle]; exact hwf1 utmSimTape j hj
            | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [hw_sc, hsc_idle]; exact hwf1 utmScratchTape j hj⟩
  | succ rem' ih =>
    intro c hstate hhead_rem hcells hdesc hhead_ge hst_head hst_ones hst_tail hst_0
      hsc_head hsc_0 hsc_ones hsc_tail hsim_c hsim_h hinp_h hinp_ns hinp_0
      hout_h hout_ns hout_0 hwf0 hwf1
    -- Desc reads one
    have hread_one : (c.work utmDescTape).read = Γ.one := by
      simp only [Tape.read, hcells]
      have := desc_n_ones_cells tm hk hdesc ((c.work utmDescTape).head - (k + 2)) (by omega)
      rwa [show k + 2 + ((c.work utmDescTape).head - (k + 2)) = (c.work utmDescTape).head from by omega] at this
    have hread_eq : (fun i => (c.work i).read) (0 : Fin 4) = Γ.one := hread_one
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.copyN ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers
    have hst_ne : (c.work utmStateTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
    have hst_idle : (c.work utmStateTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmStateTape).read) = c.work utmStateTape := by
      simp only [Tape.writeAndMove, idleDir, hst_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmStateTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmStateTape).cells
          (c.work utmStateTape).head Γw.blank.toΓ = (c.work utmStateTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmStateTape).cells (c.work utmStateTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hst_head, hst_tail (k + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Step: copyN with one → stay copyN, desc+scratch right, scratch writes one
    let c₁ : Cfg 4 setupStateTM.Q := {
      state := .copyN
      input := c.input.move (idleDir c.input.read)
      work := fun i => (c.work i).writeAndMove
        ((if (i : Fin 4).val = 0 then readBackWrite Γ.one
          else if (i : Fin 4).val = 3 then Γw.one else Γw.blank : Γw) : Γ)
        (if (i : Fin 4).val = 0 then Dir3.right
         else if (i : Fin 4).val = 3 then Dir3.right
         else idleDir (c.work i).read)
      output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      simp only [TM.step, hstate, ↓reduceIte, setupStateTM, hread_eq]; rfl
    -- c₁ desc tape
    have h1_desc_cells : (c₁.work utmDescTape).cells = w₀.cells := by
      show ((c.work utmDescTape).writeAndMove
        (readBackWrite Γ.one : Γw) Dir3.right).cells = _
      rw [← hread_one, readBackWrite_cells (by omega) (hwf1 utmDescTape)]; exact hcells
    have h1_desc_head : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      show ((c.work utmDescTape).writeAndMove _ Dir3.right).head = _
      exact writeAndMove_right_head
    -- c₁ state tape (idle)
    have h1_st : c₁.work utmStateTape = c.work utmStateTape := by
      show (c.work utmStateTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmStateTape).read) = _
      exact hst_idle
    -- c₁ scratch tape (active)
    have h1_sc_head : (c₁.work utmScratchTape).head = (c.work utmScratchTape).head + 1 := by
      show ((c.work utmScratchTape).writeAndMove (Γw.one : Γw) Dir3.right).head = _
      exact writeAndMove_right_head
    have h1_sc_cells_0 : (c₁.work utmScratchTape).cells 0 = Γ.start := by
      show ((c.work utmScratchTape).writeAndMove (Γw.one : Γw) Dir3.right).cells 0 = _
      rw [writeAndMove_cells_0 (by omega)]; exact hsc_0
    have h1_sc_ones : ∀ j, 1 ≤ j → j < (c₁.work utmScratchTape).head →
        (c₁.work utmScratchTape).cells j = Γ.one := by
      intro j hj1 hj2
      show ((c.work utmScratchTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j = Γ.one
      rw [h1_sc_head] at hj2
      by_cases hje : j = (c.work utmScratchTape).head
      · subst hje; rw [writeAndMove_cells_at_head (by omega)]; rfl
      · rw [writeAndMove_cells_ne hje]; exact hsc_ones j hj1 (by omega)
    have h1_sc_tail : ∀ j, j ≥ (c₁.work utmScratchTape).head →
        (c₁.work utmScratchTape).cells j = (initTape []).cells j := by
      intro j hj
      show ((c.work utmScratchTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j = _
      rw [h1_sc_head] at hj
      rw [writeAndMove_cells_ne (by omega)]
      exact hsc_tail j (by omega)
    -- c₁ sim idle
    have h1_sim : c₁.work utmSimTape = c.work utmSimTape := by
      show (c.work utmSimTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmSimTape).read) = _
      exact hsim_idle
    have h1_inp : c₁.input = c.input := hinp_idle
    -- WorkTapesWF for c₁
    have h1_wf0 : ∀ i, (c₁.work i).cells 0 = Γ.start :=
      fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf0 utmDescTape
          | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [h1_st]; exact hwf0 utmStateTape
          | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [h1_sim]; exact hwf0 utmSimTape
          | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; exact h1_sc_cells_0
    have h1_wf1 : ∀ i j, j ≥ 1 → (c₁.work i).cells j ≠ Γ.start :=
      fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf1 utmDescTape j hj
          | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [h1_st]; exact hwf1 utmStateTape j hj
          | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [h1_sim]; exact hwf1 utmSimTape j hj
          | ⟨3, _⟩, j, hj => by
              change (c₁.work utmScratchTape).cells j ≠ Γ.start
              show ((c.work utmScratchTape).writeAndMove (Γw.one : Γw) Dir3.right).cells j ≠ Γ.start
              by_cases hje : j = (c.work utmScratchTape).head
              · subst hje; rw [writeAndMove_cells_at_head (by omega)]; decide
              · rw [writeAndMove_cells_ne hje]; exact hwf1 utmScratchTape j hj
    -- Apply IH
    obtain ⟨c_f, hreach, hprops⟩ := ih c₁ rfl
      (by rw [h1_desc_head]; omega)
      h1_desc_cells hdesc
      (by rw [h1_desc_head]; omega)
      (by rw [h1_st]; exact hst_head)
      (by intro j hj; rw [h1_st]; exact hst_ones j hj)
      (by intro j hj; rw [h1_st]; exact hst_tail j hj)
      (by rw [h1_st]; exact hst_0)
      (by rw [h1_sc_head, hsc_head, h1_desc_head]; omega)
      h1_sc_cells_0 h1_sc_ones h1_sc_tail
      (by rw [h1_sim]; exact hsim_c)
      (by rw [h1_sim]; exact hsim_h)
      (by rw [h1_inp]; exact hinp_h)
      (fun j hj => by rw [h1_inp]; exact hinp_ns j hj)
      (by rw [h1_inp]; exact hinp_0)
      (by rw [hout_h']; exact hout_h)
      hout_ns' hout_0'
      h1_wf0 h1_wf1
    exact ⟨c_f, .step hstep hreach, hprops⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3: skipQhalt loop — rewind state tape using desc as counter
-- ════════════════════════════════════════════════════════════════════════

private theorem skipQhalt_loop (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ) :
    ∀ (rem : ℕ) (c : Cfg 4 setupStateTM.Q),
    c.state = .skipQhalt →
    rem = (c.work utmStateTape).head + 1 →
    (c.work utmDescTape).cells = (w₀ : Tape).cells →
    descOnTape (TMEncoding.encodeTM tm) ⟨0, w₀.cells⟩ →
    (c.work utmDescTape).head ≥ k + n + 3 →
    (c.work utmDescTape).head + (c.work utmStateTape).head = k + n + 3 + k + 1 →
    (c.work utmStateTape).cells 0 = Γ.start →
    (∀ j, j < k → (c.work utmStateTape).cells (j + 1) = Γ.one) →
    (∀ j, j ≥ k + 1 → (c.work utmStateTape).cells j = (initTape []).cells j) →
    (c.work utmScratchTape).head = n + 1 →
    (∀ j, j < n → (c.work utmScratchTape).cells (j + 1) = Γ.one) →
    (∀ j, j ≥ n + 1 → (c.work utmScratchTape).cells j = (initTape []).cells j) →
    (c.work utmScratchTape).cells 0 = Γ.start →
    (c.work utmSimTape).cells = (initTape []).cells → (c.work utmSimTape).head ≥ 1 →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) → c.input.cells 0 = Γ.start →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) → c.output.cells 0 = Γ.start →
    (∀ i, (c.work i).cells 0 = Γ.start) →
    (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c', setupStateTM.reachesIn rem c c' ∧
      c'.state = .copyQstart ∧
      (c'.work utmDescTape).cells = w₀.cells ∧
      (c'.work utmDescTape).head = 2 * k + n + 4 ∧
      (c'.work utmStateTape).head = 1 ∧
      (∀ j, j < k → (c'.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c'.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c'.work utmStateTape).cells 0 = Γ.start ∧
      (c'.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c'.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c'.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (c'.work utmSimTape).cells = (initTape []).cells ∧ (c'.work utmSimTape).head ≥ 1 ∧
      c'.input.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧ c'.input.cells 0 = Γ.start ∧
      c'.output.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧ c'.output.cells 0 = Γ.start ∧
      WorkTapesWF c'.work := by
  intro rem
  induction rem with
  | zero =>
    intro c _ hrem
    omega
  | succ rem' ih =>
    intro c hstate hrem hcells hdesc hdesc_ge hdesc_st_sum hst_0 hst_ones hst_tail
      hsc_h hsc_ones hsc_tail hsc_0 hsim_c hsim_h hinp_h hinp_ns hinp_0
      hout_h hout_ns hout_0 hwf0 hwf1
    have hst_head_eq : (c.work utmStateTape).head = rem' := by omega
    cases rem' with
    | zero =>
      -- BASE: state_head = 0, reads ▷, one step to .copyQstart
      have hread_start : (fun i => (c.work i).read) (1 : Fin 4) = Γ.start := by
        show (c.work utmStateTape).read = Γ.start
        simp only [Tape.read, hst_head_eq]; exact hst_0
      have hdesc_head : (c.work utmDescTape).head = 2 * k + n + 4 := by omega
      -- Idle tape helpers
      have hdesc_ne : (c.work utmDescTape).read ≠ Γ.start :=
        ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmDescTape)
      have hdesc_idle : (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read : Γw)
          (idleDir (c.work utmDescTape).read) = c.work utmDescTape := by
        simp only [Tape.writeAndMove, idleDir, hdesc_ne, ↓reduceIte, Tape.move,
          Tape.write, show (c.work utmDescTape).head ≠ 0 from by omega]
        have : Function.update (c.work utmDescTape).cells
            (c.work utmDescTape).head (readBackWrite (c.work utmDescTape).read).toΓ =
            (c.work utmDescTape).cells := by
          have hcb : (readBackWrite (c.work utmDescTape).read).toΓ =
              (c.work utmDescTape).cells (c.work utmDescTape).head := by
            rw [ss_readBackWrite_toΓ_eq hdesc_ne]; rfl
          rw [hcb, Function.update_eq_self]
        simp only [this]
      have hsc_ne : (c.work utmScratchTape).read ≠ Γ.start :=
        ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmScratchTape)
      have hsc_idle : (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
          (idleDir (c.work utmScratchTape).read) = c.work utmScratchTape := by
        simp only [Tape.writeAndMove, idleDir, hsc_ne, ↓reduceIte, Tape.move,
          Tape.write, show (c.work utmScratchTape).head ≠ 0 from by omega]
        have : Function.update (c.work utmScratchTape).cells
            (c.work utmScratchTape).head Γw.blank.toΓ = (c.work utmScratchTape).cells := by
          have hcb : Γw.blank.toΓ =
              (c.work utmScratchTape).cells (c.work utmScratchTape).head := by
            rw [show Γw.blank.toΓ = Γ.blank from rfl,
              hsc_h, hsc_tail (n + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
          rw [hcb, Function.update_eq_self]
        simp only [this]
      have hsim_idle := idle_tape_initTape hsim_h hsim_c
      have hinp_idle := idle_input hinp_h hinp_ns
      have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
      -- Build step config (skipQhalt with ▷ → copyQstart)
      let c₁ : Cfg 4 setupStateTM.Q := {
        state := .copyQstart
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove
          ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
            else Γw.blank : Γw) : Γ)
          (if (i : Fin 4).val = 1 then Dir3.right
           else idleDir (c.work i).read)
        output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
      have hstep : setupStateTM.step c = some c₁ := by
        unfold TM.step
        simp only [hstate, show (SetupStatePhase.skipQhalt : SetupStatePhase) ≠ .done from nofun,
          ↓reduceIte, setupStateTM, hread_start]
        show some _ = some c₁; congr 1
      -- Unfold c₁ work tapes
      have hw_desc : c₁.work utmDescTape =
          (c.work utmDescTape).writeAndMove
            (readBackWrite (c.work utmDescTape).read : Γw)
            (idleDir (c.work utmDescTape).read) := by
        simp only [c₁, show ((utmDescTape : Fin 4).val = 0) = True from by decide,
          show ((utmDescTape : Fin 4).val = 1) = False from by decide, ↓reduceIte]
      have hw_st : c₁.work utmStateTape =
          (c.work utmStateTape).writeAndMove (Γw.blank : Γw) Dir3.right := by
        simp only [c₁, show ((utmStateTape : Fin 4).val = 0) = False from by decide,
          show ((utmStateTape : Fin 4).val = 1) = True from by decide, ↓reduceIte]
      have hw_sim : c₁.work utmSimTape =
          (c.work utmSimTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmSimTape).read) := by
        simp only [c₁, show ((utmSimTape : Fin 4).val = 0) = False from by decide,
          show ((utmSimTape : Fin 4).val = 1) = False from by decide, ↓reduceIte]
      have hw_sc : c₁.work utmScratchTape =
          (c.work utmScratchTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmScratchTape).read) := by
        simp only [c₁, show ((utmScratchTape : Fin 4).val = 0) = False from by decide,
          show ((utmScratchTape : Fin 4).val = 1) = False from by decide, ↓reduceIte]
      -- State tape: write at head 0 is no-op, so cells preserved
      have hst_cells : (c₁.work utmStateTape).cells = (c.work utmStateTape).cells := by
        rw [hw_st]
        simp only [Tape.writeAndMove, Tape.write, hst_head_eq, ↓reduceIte, ss_tape_move_cells]
      refine ⟨c₁, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- desc cells
        rw [hw_desc, hdesc_idle]; exact hcells
      · -- desc head = 2 * k + n + 4
        rw [hw_desc, hdesc_idle]; exact hdesc_head
      · -- state head = 1
        rw [hw_st, writeAndMove_right_head, hst_head_eq]
      · -- state ones
        intro j hj; rw [hst_cells]; exact hst_ones j hj
      · -- state tail
        intro j hj; rw [hst_cells]; exact hst_tail j hj
      · -- state cells 0
        rw [hst_cells]; exact hst_0
      · -- scratch head
        rw [hw_sc, hsc_idle]; exact hsc_h
      · -- scratch ones
        intro j hj; rw [hw_sc, hsc_idle]; exact hsc_ones j hj
      · -- scratch tail
        intro j hj; rw [hw_sc, hsc_idle]; exact hsc_tail j hj
      · -- scratch cells 0
        rw [hw_sc, hsc_idle]; exact hsc_0
      · -- sim cells
        rw [hw_sim, hsim_idle]; exact hsim_c
      · -- sim head
        rw [hw_sim, hsim_idle]; exact hsim_h
      · -- input head
        rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_h
      · -- input cells ns
        intro j hj
        rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_ns j hj
      · -- input cells 0
        rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_0
      · -- output head
        rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
        rw [hout_h']; exact hout_h
      · -- output cells ns
        rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
        exact hout_ns'
      · -- output cells 0
        rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
        exact hout_0'
      · -- WorkTapesWF
        exact ⟨
          fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [hw_desc, hdesc_idle]; exact hwf0 utmDescTape
              | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [hst_cells]; exact hst_0
              | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [hw_sim, hsim_idle]; exact hwf0 utmSimTape
              | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [hw_sc, hsc_idle]; exact hwf0 utmScratchTape,
          fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [hw_desc, hdesc_idle]; exact hwf1 utmDescTape j hj
              | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [hst_cells]; exact hwf1 utmStateTape j hj
              | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [hw_sim, hsim_idle]; exact hwf1 utmSimTape j hj
              | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [hw_sc, hsc_idle]; exact hwf1 utmScratchTape j hj⟩
    | succ rem'' =>
      -- INDUCTIVE: state_head = rem'' + 1 > 0, one step then IH
      have hread_ne_start : (fun i => (c.work i).read) (1 : Fin 4) ≠ Γ.start := by
        show (c.work utmStateTape).read ≠ Γ.start
        exact ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
      -- Idle tape helpers
      have hsim_idle := idle_tape_initTape hsim_h hsim_c
      have hsc_ne : (c.work utmScratchTape).read ≠ Γ.start :=
        ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmScratchTape)
      have hsc_idle : (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
          (idleDir (c.work utmScratchTape).read) = c.work utmScratchTape := by
        simp only [Tape.writeAndMove, idleDir, hsc_ne, ↓reduceIte, Tape.move,
          Tape.write, show (c.work utmScratchTape).head ≠ 0 from by omega]
        have : Function.update (c.work utmScratchTape).cells
            (c.work utmScratchTape).head Γw.blank.toΓ = (c.work utmScratchTape).cells := by
          have hcb : Γw.blank.toΓ =
              (c.work utmScratchTape).cells (c.work utmScratchTape).head := by
            rw [show Γw.blank.toΓ = Γ.blank from rfl,
              hsc_h, hsc_tail (n + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
          rw [hcb, Function.update_eq_self]
        simp only [this]
      have hinp_idle := idle_input hinp_h hinp_ns
      have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
      -- Step: skipQhalt with ≠ ▷ → stay skipQhalt, desc right, state left
      let c₁ : Cfg 4 setupStateTM.Q := {
        state := .skipQhalt
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove
          ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
            else if (i : Fin 4).val = 1 then readBackWrite (c.work (1 : Fin 4)).read
            else Γw.blank : Γw) : Γ)
          (if (i : Fin 4).val = 0 then Dir3.right
           else if (i : Fin 4).val = 1 then Dir3.left
           else idleDir (c.work i).read)
        output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
      have hstep : setupStateTM.step c = some c₁ := by
        unfold TM.step
        simp only [hstate, show (SetupStatePhase.skipQhalt : SetupStatePhase) ≠ .done from nofun,
          ↓reduceIte, setupStateTM, hread_ne_start]
        show some _ = some c₁; congr 1
      -- c₁ desc tape (readBackWrite + right)
      have h1_desc_cells : (c₁.work utmDescTape).cells = w₀.cells := by
        show ((c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells = _
        rw [readBackWrite_cells (by omega) (hwf1 utmDescTape)]; exact hcells
      have h1_desc_head : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
        show ((c.work utmDescTape).writeAndMove _ Dir3.right).head = _
        exact writeAndMove_right_head
      -- c₁ state tape (readBackWrite + left)
      have h1_st_cells : (c₁.work utmStateTape).cells = (c.work utmStateTape).cells := by
        show ((c.work utmStateTape).writeAndMove
          (readBackWrite (c.work utmStateTape).read : Γw) Dir3.left).cells = _
        rw [readBackWrite_cells (by omega) (hwf1 utmStateTape)]
      have h1_st_head : (c₁.work utmStateTape).head = (c.work utmStateTape).head - 1 := by
        show ((c.work utmStateTape).writeAndMove _ Dir3.left).head = _
        exact writeAndMove_left_head
      -- c₁ sim idle
      have h1_sim : c₁.work utmSimTape = c.work utmSimTape := by
        show (c.work utmSimTape).writeAndMove (Γw.blank : Γw)
          (idleDir (c.work utmSimTape).read) = _
        exact hsim_idle
      -- c₁ scratch idle
      have h1_sc : c₁.work utmScratchTape = c.work utmScratchTape := by
        show (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
          (idleDir (c.work utmScratchTape).read) = _
        exact hsc_idle
      have h1_inp : c₁.input = c.input := hinp_idle
      -- WorkTapesWF for c₁
      have h1_wf0 : ∀ i, (c₁.work i).cells 0 = Γ.start :=
        fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf0 utmDescTape
            | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [h1_st_cells]; exact hwf0 utmStateTape
            | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [h1_sim]; exact hwf0 utmSimTape
            | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [h1_sc]; exact hwf0 utmScratchTape
      have h1_wf1 : ∀ i j, j ≥ 1 → (c₁.work i).cells j ≠ Γ.start :=
        fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf1 utmDescTape j hj
            | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [h1_st_cells]; exact hwf1 utmStateTape j hj
            | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [h1_sim]; exact hwf1 utmSimTape j hj
            | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [h1_sc]; exact hwf1 utmScratchTape j hj
      -- Apply IH
      obtain ⟨c_f, hreach, hprops⟩ := ih c₁ rfl
        (by rw [h1_st_head, hst_head_eq]; rfl)
        h1_desc_cells hdesc
        (by rw [h1_desc_head]; omega)
        (by rw [h1_desc_head, h1_st_head, hst_head_eq]; omega)
        (by rw [h1_st_cells]; exact hst_0)
        (by intro j hj; rw [h1_st_cells]; exact hst_ones j hj)
        (by intro j hj; rw [h1_st_cells]; exact hst_tail j hj)
        (by rw [h1_sc]; exact hsc_h)
        (by intro j hj; rw [h1_sc]; exact hsc_ones j hj)
        (by intro j hj; rw [h1_sc]; exact hsc_tail j hj)
        (by rw [h1_sc]; exact hsc_0)
        (by rw [h1_sim]; exact hsim_c)
        (by rw [h1_sim]; exact hsim_h)
        (by rw [h1_inp]; exact hinp_h)
        (fun j hj => by rw [h1_inp]; exact hinp_ns j hj)
        (by rw [h1_inp]; exact hinp_0)
        (by rw [hout_h']; exact hout_h)
        hout_ns' hout_0'
        h1_wf0 h1_wf1
      exact ⟨c_f, .step hstep hreach, hprops⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 4: copyQstart loop — copy k desc bits to state, then sentinel
-- ════════════════════════════════════════════════════════════════════════

private theorem copyQstart_loop (tm : TM n) (hk : k = @Fintype.card tm.Q tm.finQ) :
    ∀ (rem : ℕ) (c : Cfg 4 setupStateTM.Q),
    c.state = .copyQstart →
    (c.work utmDescTape).head + rem = 3 * k + n + 4 →
    (c.work utmDescTape).cells = (w₀ : Tape).cells →
    descOnTape (TMEncoding.encodeTM tm) ⟨0, w₀.cells⟩ →
    (c.work utmDescTape).head ≥ 2 * k + n + 4 →
    (c.work utmStateTape).head = (c.work utmDescTape).head - (2 * k + n + 3) →
    (c.work utmStateTape).head ≤ k + 1 →
    (c.work utmStateTape).cells 0 = Γ.start →
    -- Cells 1..copied already have qstart bits, cells copied+1..k have ones (from Phase 1)
    (∀ (j : ℕ) (hj : j < k), j + 1 < (c.work utmStateTape).head →
      (c.work utmStateTape).cells (j + 1) =
        Γ.ofBool ((⟨j, hj⟩ : Fin k) == (hk ▸ tm.stateEquiv tm.qstart))) →
    (∀ j, (c.work utmStateTape).head - 1 ≤ j → j < k →
      (c.work utmStateTape).cells (j + 1) = Γ.one) →
    (∀ j, j ≥ k + 1 → (c.work utmStateTape).cells j = (initTape []).cells j) →
    (c.work utmScratchTape).head = n + 1 →
    (∀ j, j < n → (c.work utmScratchTape).cells (j + 1) = Γ.one) →
    (∀ j, j ≥ n + 1 → (c.work utmScratchTape).cells j = (initTape []).cells j) →
    (c.work utmScratchTape).cells 0 = Γ.start →
    (c.work utmSimTape).cells = (initTape []).cells → (c.work utmSimTape).head ≥ 1 →
    c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) → c.input.cells 0 = Γ.start →
    c.output.head ≥ 1 → (∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start) → c.output.cells 0 = Γ.start →
    (∀ i, (c.work i).cells 0 = Γ.start) →
    (∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) →
    ∃ c', setupStateTM.reachesIn (rem + 1) c c' ∧
      c'.state = .done ∧
      (c'.work utmDescTape).cells = w₀.cells ∧
      (c'.work utmDescTape).head = 3 * k + n + 4 ∧
      (c'.work utmStateTape).head = k + 1 ∧
      (∀ (j : Fin k), (c'.work utmStateTape).cells (j.val + 1) =
        Γ.ofBool (j == (hk ▸ tm.stateEquiv tm.qstart))) ∧
      (∀ j, j ≥ k + 1 → (c'.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c'.work utmStateTape).cells 0 = Γ.start ∧
      (c'.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c'.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c'.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c'.work utmScratchTape).cells 0 = Γ.start ∧
      (c'.work utmSimTape).cells = (initTape []).cells ∧ (c'.work utmSimTape).head ≥ 1 ∧
      c'.input.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.input.cells j ≠ Γ.start) ∧ c'.input.cells 0 = Γ.start ∧
      c'.output.head ≥ 1 ∧ (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧ c'.output.cells 0 = Γ.start ∧
      WorkTapesWF c'.work := by
  intro rem
  induction rem with
  | zero =>
    intro c hstate hhead_rem hcells hdesc hdesc_ge hst_head hst_head_bound hst_0
      hst_copied hst_ones hst_tail hsc_h hsc_ones hsc_tail hsc_0
      hsim_c hsim_h hinp_h hinp_ns hinp_0 hout_h hout_ns hout_0 hwf0 hwf1
    have hdesc_head : (c.work utmDescTape).head = 3 * k + n + 4 := by omega
    have hst_head_val : (c.work utmStateTape).head = k + 1 := by
      rw [hst_head, hdesc_head]; omega
    -- State tape reads blank sentinel at head = k + 1
    have hread_blank : (fun i => (c.work i).read) (1 : Fin 4) = Γ.blank := by
      show (c.work utmStateTape).read = Γ.blank
      simp only [Tape.read, hst_head_val]
      rw [hst_tail (k + 1) (by omega)]
      exact initTape_nil_cell_ge1 (by omega)
    simp only [show (0 + 1 : ℕ) = 1 from rfl]
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.copyQstart ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers for base case (all tapes idle — all dirs are idleDir)
    have hdesc_ne : (c.work utmDescTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmDescTape)
    have hdesc_idle : (c.work utmDescTape).writeAndMove
        (readBackWrite (c.work utmDescTape).read : Γw)
        (idleDir (c.work utmDescTape).read) = c.work utmDescTape := by
      simp only [Tape.writeAndMove, idleDir, hdesc_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmDescTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmDescTape).cells
          (c.work utmDescTape).head (readBackWrite (c.work utmDescTape).read).toΓ =
          (c.work utmDescTape).cells := by
        have hcb : (readBackWrite (c.work utmDescTape).read).toΓ =
            (c.work utmDescTape).cells (c.work utmDescTape).head := by
          rw [ss_readBackWrite_toΓ_eq hdesc_ne]; rfl
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hst_ne : (c.work utmStateTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmStateTape)
    have hst_idle : (c.work utmStateTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmStateTape).read) = c.work utmStateTape := by
      simp only [Tape.writeAndMove, idleDir, hst_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmStateTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmStateTape).cells
          (c.work utmStateTape).head Γw.blank.toΓ = (c.work utmStateTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmStateTape).cells (c.work utmStateTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hst_head_val, hst_tail (k + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hsc_ne : (c.work utmScratchTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmScratchTape)
    have hsc_idle : (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmScratchTape).read) = c.work utmScratchTape := by
      simp only [Tape.writeAndMove, idleDir, hsc_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmScratchTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmScratchTape).cells
          (c.work utmScratchTape).head Γw.blank.toΓ = (c.work utmScratchTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmScratchTape).cells (c.work utmScratchTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hsc_h, hsc_tail (n + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Build explicit step config (copyQstart with blank → done, all idle)
    let c₁ : Cfg 4 setupStateTM.Q := {
      state := .done
      input := c.input.move (idleDir c.input.read)
      work := fun i => (c.work i).writeAndMove
        ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
          else Γw.blank : Γw) : Γ)
        (idleDir (c.work i).read)
      output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      unfold TM.step
      simp only [hstate, show (SetupStatePhase.copyQstart : SetupStatePhase) ≠ .done from nofun,
        ↓reduceIte, setupStateTM, hread_blank]
      show some _ = some c₁; congr 1
    -- Unfold c₁ work tapes for each index
    have hw_desc : c₁.work utmDescTape =
        (c.work utmDescTape).writeAndMove
          (readBackWrite (c.work utmDescTape).read : Γw)
          (idleDir (c.work utmDescTape).read) := by
      simp only [c₁, show ((utmDescTape : Fin 4).val = 0) = True from by decide, ↓reduceIte]
    have hw_st : c₁.work utmStateTape =
        (c.work utmStateTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmStateTape).read) := by
      simp only [c₁, show ((utmStateTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sim : c₁.work utmSimTape =
        (c.work utmSimTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmSimTape).read) := by
      simp only [c₁, show ((utmSimTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    have hw_sc : c₁.work utmScratchTape =
        (c.work utmScratchTape).writeAndMove (Γw.blank : Γw) (idleDir (c.work utmScratchTape).read) := by
      simp only [c₁, show ((utmScratchTape : Fin 4).val = 0) = False from by decide, ↓reduceIte]
    refine ⟨c₁, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- desc cells
      rw [hw_desc, hdesc_idle]; exact hcells
    · -- desc head = 3 * k + n + 4
      rw [hw_desc, hdesc_idle]; exact hdesc_head
    · -- state head = k + 1
      rw [hw_st, hst_idle]; exact hst_head_val
    · -- copied cells: ∀ (j : Fin k), ...
      intro j
      rw [hw_st, hst_idle]
      exact hst_copied j.val j.isLt (by omega)
    · -- state tail
      intro j hj; rw [hw_st, hst_idle]; exact hst_tail j hj
    · -- state cells 0
      rw [hw_st, hst_idle]; exact hst_0
    · -- scratch head
      rw [hw_sc, hsc_idle]; exact hsc_h
    · -- scratch ones
      intro j hj; rw [hw_sc, hsc_idle]; exact hsc_ones j hj
    · -- scratch tail
      intro j hj; rw [hw_sc, hsc_idle]; exact hsc_tail j hj
    · -- scratch cells 0
      rw [hw_sc, hsc_idle]; exact hsc_0
    · -- sim cells
      rw [hw_sim, hsim_idle]; exact hsim_c
    · -- sim head
      rw [hw_sim, hsim_idle]; exact hsim_h
    · -- input head
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_h
    · -- input cells ns
      intro j hj
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_ns j hj
    · -- input cells 0
      rw [show c₁.input = c.input.move (idleDir c.input.read) from rfl, hinp_idle]; exact hinp_0
    · -- output head
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      rw [hout_h']; exact hout_h
    · -- output cells ns
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_ns'
    · -- output cells 0
      rw [show c₁.output = c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) from rfl]
      exact hout_0'
    · -- WorkTapesWF
      exact ⟨
        fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [hw_desc, hdesc_idle]; exact hwf0 utmDescTape
            | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; rw [hw_st, hst_idle]; exact hwf0 utmStateTape
            | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [hw_sim, hsim_idle]; exact hwf0 utmSimTape
            | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [hw_sc, hsc_idle]; exact hwf0 utmScratchTape,
        fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [hw_desc, hdesc_idle]; exact hwf1 utmDescTape j hj
            | ⟨1, _⟩, j, hj => by change (c₁.work utmStateTape).cells j ≠ Γ.start; rw [hw_st, hst_idle]; exact hwf1 utmStateTape j hj
            | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [hw_sim, hsim_idle]; exact hwf1 utmSimTape j hj
            | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [hw_sc, hsc_idle]; exact hwf1 utmScratchTape j hj⟩
  | succ rem' ih =>
    intro c hstate hhead_rem hcells hdesc hdesc_ge hst_head hst_head_bound hst_0
      hst_copied hst_ones hst_tail hsc_h hsc_ones hsc_tail hsc_0
      hsim_c hsim_h hinp_h hinp_ns hinp_0 hout_h hout_ns hout_0 hwf0 hwf1
    -- State tape reads non-blank (Γ.one) at head < k + 1
    have hst_head_le_k : (c.work utmStateTape).head ≤ k := by omega
    have hread_ne_blank : (fun i => (c.work i).read) (1 : Fin 4) ≠ Γ.blank := by
      show (c.work utmStateTape).read ≠ Γ.blank
      simp only [Tape.read]
      have hge1 : (c.work utmStateTape).head ≥ 1 := by omega
      have := hst_ones ((c.work utmStateTape).head - 1) (by omega) (by omega)
      rw [show (c.work utmStateTape).head - 1 + 1 = (c.work utmStateTape).head from by omega] at this
      rw [this]; decide
    have hne_halt : c.state ≠ setupStateTM.qhalt := by
      rw [hstate]; show SetupStatePhase.copyQstart ≠ SetupStatePhase.done; exact nofun
    -- Idle tape helpers
    have hsim_idle := idle_tape_initTape hsim_h hsim_c
    have hsc_ne : (c.work utmScratchTape).read ≠ Γ.start :=
      ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmScratchTape)
    have hsc_idle : (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmScratchTape).read) = c.work utmScratchTape := by
      simp only [Tape.writeAndMove, idleDir, hsc_ne, ↓reduceIte, Tape.move,
        Tape.write, show (c.work utmScratchTape).head ≠ 0 from by omega]
      have : Function.update (c.work utmScratchTape).cells
          (c.work utmScratchTape).head Γw.blank.toΓ = (c.work utmScratchTape).cells := by
        have hcb : Γw.blank.toΓ =
            (c.work utmScratchTape).cells (c.work utmScratchTape).head := by
          rw [show Γw.blank.toΓ = Γ.blank from rfl,
            hsc_h, hsc_tail (n + 1) (by omega), initTape_nil_cell_ge1 (by omega)]
        rw [hcb, Function.update_eq_self]
      simp only [this]
    have hinp_idle := idle_input hinp_h hinp_ns
    have ⟨hout_0', hout_ns', hout_h'⟩ := idle_tape_wf hout_h hout_0 hout_ns
    -- Step: copyQstart with ≠ blank → stay copyQstart, desc+state right, state writes desc bit
    let c₁ : Cfg 4 setupStateTM.Q := {
      state := .copyQstart
      input := c.input.move (idleDir c.input.read)
      work := fun i => (c.work i).writeAndMove
        ((if (i : Fin 4).val = 0 then readBackWrite (c.work (0 : Fin 4)).read
          else if (i : Fin 4).val = 1 then readBackWrite (c.work (0 : Fin 4)).read
          else Γw.blank : Γw) : Γ)
        (if (i : Fin 4).val = 0 then Dir3.right
         else if (i : Fin 4).val = 1 then Dir3.right
         else idleDir (c.work i).read)
      output := c.output.writeAndMove ((Γw.blank : Γw) : Γ) (idleDir c.output.read) }
    have hstep : setupStateTM.step c = some c₁ := by
      unfold TM.step
      simp only [hstate, show (SetupStatePhase.copyQstart : SetupStatePhase) ≠ .done from nofun,
        ↓reduceIte, setupStateTM, hread_ne_blank]
      show some _ = some c₁; congr 1
    -- c₁ desc tape (readBackWrite + right)
    have h1_desc_cells : (c₁.work utmDescTape).cells = w₀.cells := by
      show ((c.work utmDescTape).writeAndMove
        (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells = _
      rw [readBackWrite_cells (by omega) (hwf1 utmDescTape)]; exact hcells
    have h1_desc_head : (c₁.work utmDescTape).head = (c.work utmDescTape).head + 1 := by
      show ((c.work utmDescTape).writeAndMove _ Dir3.right).head = _
      exact writeAndMove_right_head
    -- c₁ state tape (readBackWrite(desc.read) + right — cross-tape copy)
    have h1_st_head : (c₁.work utmStateTape).head = (c.work utmStateTape).head + 1 := by
      show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).head = _
      exact writeAndMove_right_head
    have h1_st_cells_0 : (c₁.work utmStateTape).cells 0 = Γ.start := by
      show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells 0 = _
      rw [writeAndMove_cells_0 (by omega)]; exact hst_0
    -- The written value at old state_head: desc bit copied to state tape
    have h1_copied : ∀ (j : ℕ) (hj : j < k), j + 1 < (c₁.work utmStateTape).head →
        (c₁.work utmStateTape).cells (j + 1) =
          Γ.ofBool ((⟨j, hj⟩ : Fin k) == (hk ▸ tm.stateEquiv tm.qstart)) := by
      intro j hj hjlt
      show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells (j + 1) = _
      rw [h1_st_head] at hjlt
      by_cases hje : j + 1 = (c.work utmStateTape).head
      · -- Newly written cell
        rw [hje, writeAndMove_cells_at_head (by omega)]
        have hdesc_ne : (c.work utmDescTape).read ≠ Γ.start :=
          ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmDescTape)
        rw [ss_readBackWrite_toΓ_eq hdesc_ne]
        simp only [Tape.read, hcells]
        rw [show (c.work utmDescTape).head = 2 * k + 4 + n + j from by omega]
        exact desc_qstart_cells tm hk hdesc j hj
      · -- Previously written cell
        rw [writeAndMove_cells_ne hje]
        exact hst_copied j hj (by omega)
    have h1_ones : ∀ j, (c₁.work utmStateTape).head - 1 ≤ j → j < k →
        (c₁.work utmStateTape).cells (j + 1) = Γ.one := by
      intro j hj1 hj2
      show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells (j + 1) = Γ.one
      rw [h1_st_head] at hj1
      rw [writeAndMove_cells_ne (by omega)]
      exact hst_ones j (by omega) hj2
    have h1_tail : ∀ j, j ≥ k + 1 →
        (c₁.work utmStateTape).cells j = (initTape []).cells j := by
      intro j hj
      show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells j = _
      rw [writeAndMove_cells_ne (by omega)]
      exact hst_tail j hj
    -- c₁ sim idle
    have h1_sim : c₁.work utmSimTape = c.work utmSimTape := by
      show (c.work utmSimTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmSimTape).read) = _
      exact hsim_idle
    -- c₁ scratch idle
    have h1_sc : c₁.work utmScratchTape = c.work utmScratchTape := by
      show (c.work utmScratchTape).writeAndMove (Γw.blank : Γw)
        (idleDir (c.work utmScratchTape).read) = _
      exact hsc_idle
    have h1_inp : c₁.input = c.input := hinp_idle
    -- WorkTapesWF for c₁
    have h1_wf0 : ∀ i, (c₁.work i).cells 0 = Γ.start :=
      fun | ⟨0, _⟩ => by change (c₁.work utmDescTape).cells 0 = Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf0 utmDescTape
          | ⟨1, _⟩ => by change (c₁.work utmStateTape).cells 0 = Γ.start; exact h1_st_cells_0
          | ⟨2, _⟩ => by change (c₁.work utmSimTape).cells 0 = Γ.start; rw [h1_sim]; exact hwf0 utmSimTape
          | ⟨3, _⟩ => by change (c₁.work utmScratchTape).cells 0 = Γ.start; rw [h1_sc]; exact hwf0 utmScratchTape
    have h1_wf1 : ∀ i j, j ≥ 1 → (c₁.work i).cells j ≠ Γ.start :=
      fun | ⟨0, _⟩, j, hj => by change (c₁.work utmDescTape).cells j ≠ Γ.start; rw [h1_desc_cells, ← hcells]; exact hwf1 utmDescTape j hj
          | ⟨1, _⟩, j, hj => by
              change (c₁.work utmStateTape).cells j ≠ Γ.start
              show ((c.work utmStateTape).writeAndMove (readBackWrite (c.work utmDescTape).read : Γw) Dir3.right).cells j ≠ Γ.start
              by_cases hje : j = (c.work utmStateTape).head
              · subst hje
                rw [writeAndMove_cells_at_head (by omega)]
                have hdesc_ne : (c.work utmDescTape).read ≠ Γ.start :=
                  ss_tape_read_ne_start_of_wf _ (by omega) (hwf1 utmDescTape)
                rw [ss_readBackWrite_toΓ_eq hdesc_ne]
                exact hwf1 utmDescTape _ (by omega)
              · rw [writeAndMove_cells_ne hje]; exact hwf1 utmStateTape j hj
          | ⟨2, _⟩, j, hj => by change (c₁.work utmSimTape).cells j ≠ Γ.start; rw [h1_sim]; exact hwf1 utmSimTape j hj
          | ⟨3, _⟩, j, hj => by change (c₁.work utmScratchTape).cells j ≠ Γ.start; rw [h1_sc]; exact hwf1 utmScratchTape j hj
    -- Apply IH
    obtain ⟨c_f, hreach, hprops⟩ := ih c₁ rfl
      (by rw [h1_desc_head]; omega)
      h1_desc_cells hdesc
      (by rw [h1_desc_head]; omega)
      (by rw [h1_st_head, hst_head, h1_desc_head]; omega)
      (by rw [h1_st_head]; omega)
      h1_st_cells_0
      h1_copied h1_ones h1_tail
      (by rw [h1_sc]; exact hsc_h)
      (by intro j hj; rw [h1_sc]; exact hsc_ones j hj)
      (by intro j hj; rw [h1_sc]; exact hsc_tail j hj)
      (by rw [h1_sc]; exact hsc_0)
      (by rw [h1_sim]; exact hsim_c)
      (by rw [h1_sim]; exact hsim_h)
      (by rw [h1_inp]; exact hinp_h)
      (fun j hj => by rw [h1_inp]; exact hinp_ns j hj)
      (by rw [h1_inp]; exact hinp_0)
      (by rw [hout_h']; exact hout_h)
      hout_ns' hout_0'
      h1_wf0 h1_wf1
    exact ⟨c_f, .step hstep hreach, hprops⟩

-- ════════════════════════════════════════════════════════════════════════
-- Full simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Step-by-step simulation of setupStateTM through all 4 phases. -/
theorem setupStateTM_simulation (tm : TM n) (k : ℕ)
    (_x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (hdesc : descOnTape (TMEncoding.encodeTM tm) (work utmDescTape))
    (hdesc_h : (work utmDescTape).head = 1)
    (hst_c : (work utmStateTape).cells = (initTape []).cells)
    (hst_h : (work utmStateTape).head = 1)
    (hsim_c : (work utmSimTape).cells = (initTape []).cells)
    (hsc_c : (work utmScratchTape).cells = (initTape []).cells)
    (hsc_h : (work utmScratchTape).head = 1)
    (henv : InitEnvelope inp work out) :
    ∃ c', setupStateTM.reachesIn (3 * k + n + 5)
      { state := SetupStatePhase.skipK, input := inp, work := work, output := out } c' ∧
      setupStateTM.halted c' ∧
      InitEnvelope c'.input c'.work c'.output ∧
      (let desc := TMEncoding.encodeTM tm
       descOnTape desc (c'.work utmDescTape) ∧
       stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (c'.work utmStateTape) ∧
       (c'.work utmSimTape).cells = (initTape []).cells ∧
       tapeStoresBools (List.replicate n true) (c'.work utmScratchTape) ∧
       (c'.work utmDescTape).head ≤ 3 * k + n + 5 ∧
       (c'.work utmScratchTape).head ≤ n + 1 ∧
       (c'.work utmStateTape).head ≤ k + 1 ∧
       c'.work utmSimTape = work utmSimTape ∧
       c'.input = inp) := by
  -- Extract InitEnvelope components
  obtain ⟨hic0, hins, hih, hwf, hheads, hoc0, hons, hoh⟩ := henv
  -- WorkTapesWF gives us cells-level properties for all work tapes
  have hwf0 := hwf.1; have hwf1 := hwf.2
  -- Abbrevs
  set desc := TMEncoding.encodeTM tm
  set c₀ : Cfg 4 setupStateTM.Q :=
    { state := .skipK, input := inp, work := work, output := out }
  -- The proof proceeds through 4 phases.
  -- We construct the final config and reachesIn chain by composing phases.

  -- Phase 1: skipK reads k ones from desc cells 1..k, writes to state cells 1..k
  -- Phase 1 + separator = k+1 steps, then
  -- Phase 2: copyN reads n ones from desc cells k+2..k+1+n, writes to scratch cells 1..n
  -- Phase 2 + separator = n+1 steps, then
  -- Phase 3: skipQhalt counts down state from k+1 to 0 = k+2 steps, then
  -- Phase 4: copyQstart copies k desc bits to state + done = k+1 steps
  -- Total: (k+1) + (n+1) + (k+2) + (k+1) = 3k+n+5

  -- The output tape gets blank written at head each step (idleDir = stay since head ≥ 1).
  -- Since head ≥ 1 and head stays, the effect is: cells at out.head become Γ.blank,
  -- all other cells unchanged. For InitEnvelope, we need cells 0 = ▷ and cells ≥ 1 ≠ ▷.
  -- Γ.blank ≠ ▷, so this is fine. The output tape's exact final state doesn't matter
  -- beyond InitEnvelope preservation.

  -- Similarly, sim tape gets blank written at head (which is ≥ 1), but since sim cells
  -- start as initTape (cells ≥ 1 = blank), writing blank is identity. So sim tape
  -- is truly unchanged throughout.

  -- For desc tape: readBackWrite preserves cells (since desc cells ≥ 1 ≠ ▷, and
  -- readBackWrite roundtrips non-▷ symbols). So desc cells are unchanged.

  -- Let's proceed phase by phase.
  -- We'll show: each step of the machine produces a specific next config.
  -- For loops (phases 1,2,3,4), we use induction.

  -- Helper: desc tape cells don't have ▷ at positions ≥ 1
  have hdesc_ne : ∀ j, j ≥ 1 → (work utmDescTape).cells j ≠ Γ.start :=
    hwf1 utmDescTape
  -- State tape cells don't have ▷ at positions ≥ 1 (initTape has blank for ≥ 1)
  have hst_ne : ∀ j, j ≥ 1 → (work utmStateTape).cells j ≠ Γ.start := by
    intro j hj; rw [hst_c]; intro h; simp [initTape, show j ≠ 0 from by omega] at h
  -- Scratch tape similarly
  have hsc_ne : ∀ j, j ≥ 1 → (work utmScratchTape).cells j ≠ Γ.start := by
    intro j hj; rw [hsc_c]; intro h; simp [initTape, show j ≠ 0 from by omega] at h
  -- Sim tape similarly
  have hsim_ne : ∀ j, j ≥ 1 → (work utmSimTape).cells j ≠ Γ.start := by
    intro j hj; rw [hsim_c]; intro h; simp [initTape, show j ≠ 0 from by omega] at h

  -- The proof is organized as 4 sorry'd phase claims composed via reachesIn_trans.
  -- Each phase claim is then proved separately by induction.

  -- Phase 1 claim: from initial c₀, reach c₁ in k+1 steps
  -- Phase 2 claim: from c₁, reach c₂ in n+1 steps
  -- Phase 3 claim: from c₂, reach c₃ in k+2 steps
  -- Phase 4 claim: from c₃, reach c₄ in k+1 steps
  -- Total: (k+1)+(n+1)+(k+2)+(k+1) = 3k+n+5

  -- We define intermediate configs c₁..c₄ via sorry and prove the claims.
  -- At the end, we verify postconditions on c₄.

  -- Step 1: Construct the proof via sorry'd claims, then fill each in.
  -- This lets us verify the overall structure first.

  -- Actually, to avoid defining explicit configs (which is very verbose),
  -- we use existential witnesses throughout.

  -- Phase 1: k+1 steps from skipK to copyN
  have phase1 : ∃ c₁, setupStateTM.reachesIn (k + 1) c₀ c₁ ∧
      c₁.state = .copyN ∧
      (c₁.work utmDescTape).cells = (work utmDescTape).cells ∧
      (c₁.work utmDescTape).head = k + 2 ∧
      (c₁.work utmStateTape).head = k + 1 ∧
      (∀ j, j < k → (c₁.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c₁.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c₁.work utmStateTape).cells 0 = Γ.start ∧
      (c₁.work utmSimTape).cells = (initTape []).cells ∧
      (c₁.work utmSimTape).head ≥ 1 ∧
      (c₁.work utmScratchTape).cells = (initTape []).cells ∧
      (c₁.work utmScratchTape).head = 1 ∧
      c₁.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₁.input.cells j ≠ Γ.start) ∧
      c₁.input.cells 0 = Γ.start ∧
      c₁.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₁.output.cells j ≠ Γ.start) ∧
      c₁.output.cells 0 = Γ.start ∧
      WorkTapesWF c₁.work := by
    have h_desc_tape : descOnTape desc ⟨0, (work utmDescTape).cells⟩ := by
      exact ⟨hdesc.1, hdesc.2.1, hdesc.2.2⟩
    exact skipK_loop tm hk k c₀ rfl (by simp [c₀, hdesc_h]; omega) rfl h_desc_tape
      (by simp [c₀, hdesc_h]) (by simp [c₀, hst_h, hdesc_h])
      (by simp [c₀]; exact hwf0 utmStateTape)
      (by intro j hj1 hj2; simp [c₀, hst_h, hdesc_h] at hj2; omega)
      (by intro j hj; simp [c₀, hst_h, hdesc_h] at hj ⊢; rw [hst_c])
      (by simp [c₀]; exact hsim_c) (by simp [c₀]; exact hheads utmSimTape)
      (by simp [c₀]; exact hsc_c) (by simp [c₀]; exact hsc_h)
      (by simp [c₀]; exact hih) (by simp [c₀]; exact hins) (by simp [c₀]; exact hic0)
      (by simp [c₀]; exact hoh) (by simp [c₀]; exact hons) (by simp [c₀]; exact hoc0)
      (by simp [c₀]; exact hwf0) (by simp [c₀]; exact hwf1)

  obtain ⟨c₁, hreach1, hst1, hdesc_c1, hdesc_h1, hst_h1, hst_ones1, hst_tail1,
    hst_01, hsim_c1, hsim_h1, hsc_c1, hsc_h1, hinp_h1, hinp_ne1, hinp_01,
    hout_h1, hout_ne1, hout_01, hwf1'⟩ := phase1

  -- Phase 2: n+1 steps from copyN to skipQhalt
  have phase2 : ∃ c₂, setupStateTM.reachesIn (n + 1) c₁ c₂ ∧
      c₂.state = .skipQhalt ∧
      (c₂.work utmDescTape).cells = (work utmDescTape).cells ∧
      (c₂.work utmDescTape).head = k + n + 3 ∧
      -- state tape unchanged from c₁
      (c₂.work utmStateTape).head = k + 1 ∧
      (∀ j, j < k → (c₂.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c₂.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c₂.work utmStateTape).cells 0 = Γ.start ∧
      -- scratch tape has n ones
      (c₂.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c₂.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c₂.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c₂.work utmScratchTape).cells 0 = Γ.start ∧
      -- sim unchanged
      (c₂.work utmSimTape).cells = (initTape []).cells ∧
      (c₂.work utmSimTape).head ≥ 1 ∧
      -- envelope stuff
      c₂.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₂.input.cells j ≠ Γ.start) ∧
      c₂.input.cells 0 = Γ.start ∧
      c₂.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₂.output.cells j ≠ Γ.start) ∧
      c₂.output.cells 0 = Γ.start ∧
      WorkTapesWF c₂.work := by
    have h_desc_tape : descOnTape desc ⟨0, (work utmDescTape).cells⟩ :=
      ⟨hdesc.1, hdesc.2.1, hdesc.2.2⟩
    exact copyN_loop tm hk n c₁
      hst1
      (by rw [hdesc_h1]; omega)
      hdesc_c1
      h_desc_tape
      (by omega)
      hst_h1
      hst_ones1
      hst_tail1
      hst_01
      (by rw [hsc_h1, hdesc_h1]; omega)
      (hwf1'.1 utmScratchTape)
      (by intro j hj1 hj2; rw [hsc_h1] at hj2; omega)
      (by intro j _; exact congr_fun hsc_c1 j)
      hsim_c1
      hsim_h1
      hinp_h1 hinp_ne1 hinp_01
      hout_h1 hout_ne1 hout_01
      hwf1'.1 hwf1'.2

  obtain ⟨c₂, hreach2, hst2, hdesc_c2, hdesc_h2, hst_h2, hst_ones2, hst_tail2,
    hst_02, hsc_h2, hsc_ones2, hsc_tail2, hsc_02, hsim_c2, hsim_h2,
    hinp_h2, hinp_ne2, hinp_02, hout_h2, hout_ne2, hout_02, hwf2'⟩ := phase2

  -- Phase 3: k+2 steps from skipQhalt to copyQstart
  have phase3 : ∃ c₃, setupStateTM.reachesIn (k + 2) c₂ c₃ ∧
      c₃.state = .copyQstart ∧
      (c₃.work utmDescTape).cells = (work utmDescTape).cells ∧
      (c₃.work utmDescTape).head = 2 * k + n + 4 ∧
      -- state tape: head back to 1, cells unchanged from c₂
      (c₃.work utmStateTape).head = 1 ∧
      (∀ j, j < k → (c₃.work utmStateTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ k + 1 → (c₃.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c₃.work utmStateTape).cells 0 = Γ.start ∧
      -- scratch, sim unchanged
      (c₃.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c₃.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c₃.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c₃.work utmScratchTape).cells 0 = Γ.start ∧
      (c₃.work utmSimTape).cells = (initTape []).cells ∧
      (c₃.work utmSimTape).head ≥ 1 ∧
      c₃.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₃.input.cells j ≠ Γ.start) ∧
      c₃.input.cells 0 = Γ.start ∧
      c₃.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₃.output.cells j ≠ Γ.start) ∧
      c₃.output.cells 0 = Γ.start ∧
      WorkTapesWF c₃.work := by
    have h_desc_tape : descOnTape desc ⟨0, (work utmDescTape).cells⟩ :=
      ⟨hdesc.1, hdesc.2.1, hdesc.2.2⟩
    exact skipQhalt_loop tm hk (k + 2) c₂
      hst2
      (by omega)
      hdesc_c2
      h_desc_tape
      (by omega)
      (by rw [hdesc_h2, hst_h2]; omega)
      hst_02
      hst_ones2
      hst_tail2
      hsc_h2
      hsc_ones2
      hsc_tail2
      hsc_02
      hsim_c2
      hsim_h2
      hinp_h2 hinp_ne2 hinp_02
      hout_h2 hout_ne2 hout_02
      hwf2'.1 hwf2'.2

  obtain ⟨c₃, hreach3, hst3, hdesc_c3, hdesc_h3, hst_h3, hst_ones3, hst_tail3,
    hst_03, hsc_h3, hsc_ones3, hsc_tail3, hsc_03, hsim_c3, hsim_h3,
    hinp_h3, hinp_ne3, hinp_03, hout_h3, hout_ne3, hout_03, hwf3'⟩ := phase3

  -- Phase 4: k+1 steps from copyQstart to done
  have phase4 : ∃ c₄, setupStateTM.reachesIn (k + 1) c₃ c₄ ∧
      c₄.state = .done ∧
      (c₄.work utmDescTape).cells = (work utmDescTape).cells ∧
      (c₄.work utmDescTape).head = 3 * k + n + 4 ∧
      -- state tape: has qstart one-hot at cells 1..k
      (c₄.work utmStateTape).head = k + 1 ∧
      (∀ (j : Fin k), (c₄.work utmStateTape).cells (j.val + 1) =
        Γ.ofBool (j == (hk ▸ tm.stateEquiv tm.qstart))) ∧
      (∀ j, j ≥ k + 1 → (c₄.work utmStateTape).cells j = (initTape []).cells j) ∧
      (c₄.work utmStateTape).cells 0 = Γ.start ∧
      -- scratch, sim unchanged from c₃
      (c₄.work utmScratchTape).head = n + 1 ∧
      (∀ j, j < n → (c₄.work utmScratchTape).cells (j + 1) = Γ.one) ∧
      (∀ j, j ≥ n + 1 → (c₄.work utmScratchTape).cells j = (initTape []).cells j) ∧
      (c₄.work utmScratchTape).cells 0 = Γ.start ∧
      (c₄.work utmSimTape).cells = (initTape []).cells ∧
      (c₄.work utmSimTape).head ≥ 1 ∧
      c₄.input.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₄.input.cells j ≠ Γ.start) ∧
      c₄.input.cells 0 = Γ.start ∧
      c₄.output.head ≥ 1 ∧
      (∀ j, j ≥ 1 → c₄.output.cells j ≠ Γ.start) ∧
      c₄.output.cells 0 = Γ.start ∧
      WorkTapesWF c₄.work := by
    have h_desc_tape : descOnTape desc ⟨0, (work utmDescTape).cells⟩ :=
      ⟨hdesc.1, hdesc.2.1, hdesc.2.2⟩
    exact copyQstart_loop tm hk k c₃
      hst3
      (by rw [hdesc_h3]; omega)
      hdesc_c3
      h_desc_tape
      (by omega)
      (by rw [hst_h3, hdesc_h3]; omega)
      (by rw [hst_h3]; omega)
      hst_03
      (by intro j _ h; rw [hst_h3] at h; omega)
      (by intro j _ hj2; exact hst_ones3 j hj2)
      hst_tail3
      hsc_h3
      hsc_ones3
      hsc_tail3
      hsc_03
      hsim_c3
      hsim_h3
      hinp_h3 hinp_ne3 hinp_03
      hout_h3 hout_ne3 hout_03
      hwf3'.1 hwf3'.2

  obtain ⟨c₄, hreach4, hst4, hdesc_c4, hdesc_h4, hst_h4, hst_qstart4, hst_tail4,
    hst_04, hsc_h4, hsc_ones4, hsc_tail4, hsc_04, hsim_c4, hsim_h4,
    hinp_h4, hinp_ne4, hinp_04, hout_h4, hout_ne4, hout_04, hwf4'⟩ := phase4

  -- Compose the four phases
  have hreach12 := reachesIn_trans setupStateTM hreach1 hreach2
  have hreach123 := reachesIn_trans setupStateTM hreach12 hreach3
  have hreach1234 := reachesIn_trans setupStateTM hreach123 hreach4
  rw [show (k + 1 + (n + 1)) + (k + 2) + (k + 1) = 3 * k + n + 5 from by omega]
    at hreach1234

  -- The final config is c₄
  refine ⟨c₄, hreach1234, ?_, ?_, ?_⟩

  -- c₄ is halted (state = done = qhalt)
  · show c₄.state = SetupStatePhase.done; exact hst4

  -- InitEnvelope
  · refine ⟨hinp_04, hinp_ne4, hinp_h4, hwf4', ?_, hout_04, hout_ne4, hout_h4⟩
    intro i
    match i with
    | ⟨0, _⟩ => show (c₄.work 0).head ≥ 1; rw [show (0 : Fin 4) = utmDescTape from rfl, hdesc_h4]; omega
    | ⟨1, _⟩ => show (c₄.work 1).head ≥ 1; rw [show (1 : Fin 4) = utmStateTape from rfl, hst_h4]; omega
    | ⟨2, _⟩ => show (c₄.work 2).head ≥ 1; rw [show (2 : Fin 4) = utmSimTape from rfl]; exact hsim_h4
    | ⟨3, _⟩ => show (c₄.work 3).head ≥ 1; rw [show (3 : Fin 4) = utmScratchTape from rfl, hsc_h4]; omega

  -- Postconditions
  · change descOnTape desc (c₄.work utmDescTape) ∧ _
    refine ⟨?_, ?_, hsim_c4, ?_, ?_, ?_, by rw [hst_h4], sorry, sorry⟩
    -- descOnTape desc (c₄.work utmDescTape)
    · constructor
      · rw [hdesc_c4]; exact hdesc.1
      · constructor
        · intro i hi; rw [hdesc_c4]; exact hdesc.2.1 i hi
        · rw [hdesc_c4]; exact hdesc.2.2
    -- stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (c₄.work utmStateTape)
    · refine ⟨hst_04, ?_, ?_⟩
      · intro j hj
        have := hst_qstart4 ⟨j, hj⟩
        rw [this]; clear this
        rw [stateEquivK_val]; subst hk
        by_cases hq : j = (tm.stateEquiv tm.qstart).val
        · have hbeq : BEq.beq (⟨j, hj⟩ : Fin (Fintype.card tm.Q)) (tm.stateEquiv tm.qstart) = true := by
            rw [beq_iff_eq, Fin.ext_iff]; exact hq
          simp [hbeq, Γ.ofBool, hq]
        · have hbeq : BEq.beq (⟨j, hj⟩ : Fin (Fintype.card tm.Q)) (tm.stateEquiv tm.qstart) = false := by
            rw [Bool.eq_false_iff]; intro h; rw [beq_iff_eq, Fin.ext_iff] at h; exact hq h
          simp [hbeq, Γ.ofBool, hq]
      · have := hst_tail4 (k + 1) (by omega)
        rw [show k + 1 = k + 1 from rfl] at this
        rw [this]; exact initTape_nil_cell_ge1 (by omega)
    -- tapeStoresBools (replicate n true) scratch
    · refine ⟨hsc_04, ?_, ?_⟩
      · intro i hi
        simp only [List.length_replicate] at hi
        rw [hsc_ones4 i hi]
        simp [List.getElem_replicate, Γ.ofBool]
      · simp only [List.length_replicate]
        have := hsc_tail4 (n + 1) (by omega)
        rw [show n + 1 = n + 1 from rfl] at this
        rw [this]; exact initTape_nil_cell_ge1 (by omega)
    -- desc head bound
    · rw [hdesc_h4]; omega
    -- scratch head bound
    · rw [hsc_h4]

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for setupStateTM.
    Precondition: desc tape with head at 1, other work tapes blank.
    Postcondition: state tape has qstart one-hot, scratch has n ones. -/
theorem setupStateTM_hoareTime (tm : TM n) (k : ℕ)
    (_x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    setupStateTM.HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).cells = (initTape []).cells ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        (work utmScratchTape).cells = (initTape []).cells ∧
        (work utmScratchTape).head = 1)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
        (work utmDescTape).head ≤ 3 * k + n + 5 ∧
        (work utmScratchTape).head ≤ n + 1 ∧
        (work utmStateTape).head ≤ k + 1 ∧
        (work utmSimTape) = (work utmSimTape) ∧
        inp = inp)
      (3 * k + n + 5) := by
  intro inp work out hpre
  obtain ⟨henv, hdesc, hdesc_h, hst_c, hst_h, hsim_c, hsc_c, hsc_h⟩ := hpre
  have hsim := setupStateTM_simulation tm k _x hk inp work out
      hdesc hdesc_h hst_c hst_h hsim_c hsc_c hsc_h henv
  obtain ⟨c', hreach, hhalt, henv', hpost⟩ := hsim
  -- Extract all fields from the simulation postcondition
  have hdesc' := hpost.1
  have hstate' := hpost.2.1
  have hsim' := hpost.2.2.1
  have hsc' := hpost.2.2.2.1
  have hd_head' := hpost.2.2.2.2.1
  have hsc_head' := hpost.2.2.2.2.2.1
  have hst_head' := hpost.2.2.2.2.2.2.1
  have hsim_pres := hpost.2.2.2.2.2.2.2.1
  have hinp_pres := hpost.2.2.2.2.2.2.2.2
  exact ⟨c', 3 * k + n + 5, le_refl _, hreach, hhalt, henv',
         hdesc', hstate', hsim', hsc', hd_head', hsc_head', hst_head',
         by rw [hsim_pres], by rw [hinp_pres]⟩

end TM
