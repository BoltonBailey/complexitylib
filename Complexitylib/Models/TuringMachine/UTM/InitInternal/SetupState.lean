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
-- Full simulation (sorry'd)
-- ════════════════════════════════════════════════════════════════════════

/-- Step-by-step simulation of setupStateTM through all 4 phases.
    Sorry'd — requires detailed step simulation. -/
theorem setupStateTM_simulation (tm : TM n) (k : ℕ)
    (e : tm.Q ≃ Fin k) (_x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (hdesc : descOnTape (TMEncoding.encodeTM tm) (work utmDescTape))
    (hdesc_h : (work utmDescTape).head = 1)
    (hst_c : (work utmStateTape).cells = (initTape []).cells)
    (hsim_c : (work utmSimTape).cells = (initTape []).cells)
    (hsc_c : (work utmScratchTape).cells = (initTape []).cells)
    (henv : InitEnvelope inp work out) :
    ∃ c', setupStateTM.reachesIn (3 * k + n + 4)
      { state := SetupStatePhase.skipK, input := inp, work := work, output := out } c' ∧
      setupStateTM.halted c' ∧
      InitEnvelope c'.input c'.work c'.output ∧
      (let desc := TMEncoding.encodeTM tm
       descOnTape desc (c'.work utmDescTape) ∧
       stateOnTapeAt k (e tm.qstart) (c'.work utmStateTape) ∧
       (c'.work utmSimTape).cells = (initTape []).cells ∧
       tapeStoresBools (List.replicate n true) (c'.work utmScratchTape) ∧
       (c'.work utmDescTape).head ≤ 3 * k + n + 4 ∧
       (c'.work utmScratchTape).head ≤ n + 1) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for setupStateTM.
    Precondition: desc tape with head at 1, other work tapes blank.
    Postcondition: state tape has qstart one-hot, scratch has n ones. -/
theorem setupStateTM_hoareTime (tm : TM n) (k : ℕ)
    (e : tm.Q ≃ Fin k) (_x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    setupStateTM.HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).cells = (initTape []).cells ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        (work utmScratchTape).cells = (initTape []).cells)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (e tm.qstart) (work utmStateTape) ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
        (work utmDescTape).head ≤ 3 * k + n + 4 ∧
        (work utmScratchTape).head ≤ n + 1)
      (3 * k + n + 4) := by
  intro inp work out hpre
  obtain ⟨henv, hdesc, hdesc_h, hst_c, hsim_c, hsc_c⟩ := hpre
  obtain ⟨c', hreach, hhalt, henv', hpost⟩ :=
    setupStateTM_simulation tm k e _x hk inp work out
      hdesc hdesc_h hst_c hsim_c hsc_c henv
  exact ⟨c', 3 * k + n + 4, le_refl _, hreach, hhalt, henv', hpost⟩

end TM
