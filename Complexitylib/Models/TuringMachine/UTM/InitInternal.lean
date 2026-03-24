import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.InitInternal.Copy
import Complexitylib.Models.TuringMachine.UTM.InitInternal.Rewind
import Complexitylib.Models.TuringMachine.UTM.InitInternal.SetupState
import Complexitylib.Models.TuringMachine.UTM.InitInternal.SetupSim
import Complexitylib.Models.TuringMachine.UTM.HelpersInternal
import Complexitylib.Models.TuringMachine.Hoare

/-!
# Init proof internals: composition

Composes the sub-machine HoareTime proofs for `initTM` into a single
`initTM_hoareTime` theorem establishing `SimInvariant`.

## Sub-modules

- `InitInternal.Copy` — fully proved `copyInputToWorkTM_hoareTime`
- `InitInternal.Rewind` — fully proved frame-preserving `rewindWorkTM` +
  `rewindAll_hoareTime` composition

## Remaining sorry's

- `setupStateTM_hoareTime` — 5-phase header parser (1 sorry: step simulation)
- `setupSimTM_hoareTime` — 20+ state super-cell writer (3 sorry's: phase simulations)
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Bridge: copy postcondition → InitEnvelope
-- ════════════════════════════════════════════════════════════════════════

/-- The copy proof's postcondition implies InitEnvelope from the Rewind module. -/
private theorem postCopy_to_initEnvelope (tm : TM n) (x : List Bool) :
    ∀ inp work out, postCopy tm x inp work out →
      InitEnvelope inp work out := by
  intro inp work out h
  have hw0_head := h.2.1
  have hinp_head := h.2.2.1
  have hother_heads := h.2.2.2.1
  have hout_head := h.2.2.2.2.1
  have hwf : WorkTapesWF work := h.2.2.2.2.2.1
  have hinp_cells := h.2.2.2.2.2.2.2.1
  have hout_cells := h.2.2.2.2.2.2.2.2
  have initTape_ne_start : ∀ (contents : List Γ) (j : ℕ),
      (∀ g ∈ contents, g ≠ Γ.start) → j ≥ 1 → (initTape contents).cells j ≠ Γ.start := by
    intro contents j hns hj habs
    simp only [initTape, show j ≠ 0 from by omega] at habs
    cases hg : contents[j - 1]? with
    | none => simp [hg] at habs
    | some val =>
      simp [hg] at habs
      have hlt : j - 1 < contents.length := by
        by_contra hge; have : contents.length ≤ j - 1 := by omega
        simp [List.getElem?_eq_none_iff.mpr this] at hg
      have heq := List.getElem?_eq_getElem hlt; rw [hg] at heq
      have : contents[j - 1] = val := Option.some.inj heq.symm
      exact hns val (this ▸ List.getElem_mem ..) habs
  exact ⟨by rw [hinp_cells]; rfl,
    by intro j hj; rw [hinp_cells]; exact initTape_ne_start _ j
         (encodeUTMInput_ne_start tm x) hj,
    by rw [hinp_head]; omega,
    hwf,
    by intro i; by_cases hi : i = 0
       · subst hi; rw [hw0_head]; omega
       · have := hother_heads i hi; omega,
    by rw [hout_cells]; rfl,
    by intro j hj; rw [hout_cells]; exact initTape_ne_start _ j (by simp) hj,
    by rw [hout_head]⟩

-- ════════════════════════════════════════════════════════════════════════
-- SetupState (sorry'd)
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for setupStateTM.
    Precondition: desc tape with head at 1, other work tapes blank.
    Postcondition: state tape has qstart one-hot, scratch has n ones.
    Proof delegated to SetupState module. -/
private theorem setupStateTM_hoareTime' (tm : TM n) (k : ℕ)
    (_x : List Bool)
    (_hk : k = @Fintype.card tm.Q tm.finQ) :
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
        stateOnTapeAt k (tm.stateEquivK _hk tm.qstart) (work utmStateTape) ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
        (work utmDescTape).head ≤ 3 * k + n + 5 ∧
        (work utmScratchTape).head ≤ n + 1)
      (3 * k + n + 5) :=
  setupStateTM_hoareTime tm k _x _hk

-- ════════════════════════════════════════════════════════════════════════
-- SetupSim (sorry'd)
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime for setupSimTM.
    Precondition: sim tape blank, scratch has n ones at head 1, input at separator.
    Postcondition: sim tape has super-cells for initCfg x.
    Proof delegated to SetupSim module. -/
private theorem setupSimTM_hoareTime' (tm : TM n) (k : ℕ)
    (x : List Bool)
    (_hk : k = @Fintype.card tm.Q tm.finQ) :
    setupSimTM.HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (tm.stateEquivK _hk tm.qstart) (work utmStateTape) ∧
        (work utmSimTape).cells = (initTape []).cells ∧
        (work utmSimTape).head = 1 ∧
        tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
        (work utmScratchTape).head = 1 ∧
        inp.cells inp.head = Γ.blank ∧
        (∀ (i : ℕ) (hi : i < x.length),
          inp.cells (inp.head + 1 + i) = Γ.ofBool (x.get ⟨i, hi⟩)) ∧
        inp.cells (inp.head + 1 + x.length) = Γ.blank ∧
        (work utmDescTape).head ≤ 3 * k + n + 5 ∧
        (work utmStateTape).head ≤ k + 1)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        let desc := TMEncoding.encodeTM tm
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (tm.stateEquivK _hk tm.qstart) (work utmStateTape) ∧
        superCellsCorrect (tm.initCfg x) (work utmSimTape) ∧
        (work (0 : Fin 4)).head ≤ 3 * k + n + 5 ∧
        (work (1 : Fin 4)).head ≤ k + 1 ∧
        (work (2 : Fin 4)).head ≤ (x.length + 1) * 3 * (n + 2) + 1 ∧
        (work (3 : Fin 4)).head ≤ n + 1)
      (3 * n + 9 + x.length * (4 * n + 9)) :=
  setupSimTM_hoareTime tm k (tm.stateEquivK _hk) x _hk

-- ════════════════════════════════════════════════════════════════════════
-- seqTransition identity under InitEnvelope
-- ════════════════════════════════════════════════════════════════════════

/-- h_trans for any predicate that implies InitEnvelope. -/
private theorem h_trans_envelope {P : TapePred 4}
    (hP : ∀ inp work out, P inp work out → InitEnvelope inp work out) :
    ∀ inp work out, P inp work out →
      P (seqTransitionInput inp)
        (fun i => seqTransitionTape (work i))
        (seqTransitionTape out) := by
  intro inp work out hp
  have henv := hP inp work out hp
  obtain ⟨hic0, hins, hih, hwf, hheads, hoc0, hons, hoh⟩ := henv
  have hi := seqTransitionInput_id (by simp [Tape.read]; exact hins inp.head hih)
  have hw : (fun i => seqTransitionTape (work i)) = work := by
    ext i; apply seqTransitionTape_id
    · intro h; have := hwf.2 i (work i).head (hheads i)
      rw [Tape.read] at h; exact this h
    · exact hheads i
  have ho := seqTransitionTape_id
    (by simp [Tape.read]; exact hons out.head hoh) hoh
  rw [hi, hw, ho]; exact hp

-- ════════════════════════════════════════════════════════════════════════
-- postSetupSim → InitEnvelope + head bounds → rewindAll precondition
-- ════════════════════════════════════════════════════════════════════════

-- postSetupSim_to_rewindAll moved after initData definition below

/-- After all rewinds + SimInvariant data, construct SimInvariant. -/
private theorem postRewindsAndData_to_simInvariant (tm : TM n) (k : ℕ)
    (x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (henv : InitEnvelope inp work out)
    (hheads : ∀ i, (work i).head = 1)
    (hdesc : descOnTape (TMEncoding.encodeTM tm) (work utmDescTape))
    (hstate : stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape))
    (hsim : superCellsCorrect (tm.initCfg x) (work utmSimTape)) :
    SimInvariant tm k hk (TMEncoding.encodeTM tm) inp work out := by
  exact ⟨tm.initCfg x, hdesc, hstate, hsim,
    fun i => by have := hheads i; omega, henv.2.2.2.1⟩

-- ════════════════════════════════════════════════════════════════════════
-- Data-preserving rewind helpers
-- ════════════════════════════════════════════════════════════════════════

/-- The data part of the postcondition that depends only on tape cells. -/
private def initData (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (x : List Bool) : TapePred 4 :=
  fun _inp work _out =>
    let desc := TMEncoding.encodeTM tm
    descOnTape desc (work utmDescTape) ∧
    stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
    superCellsCorrect (tm.initCfg x) (work utmSimTape)

/-- The setupSim postcondition implies the rewindAll precondition (keeping data). -/
private theorem postSetupSim_to_rewindAll (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) :
    ∀ inp work out,
    (InitEnvelope inp work out ∧
      let desc := TMEncoding.encodeTM tm
      descOnTape desc (work utmDescTape) ∧
      stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
      superCellsCorrect (tm.initCfg x) (work utmSimTape) ∧
      (work (0 : Fin 4)).head ≤ 3 * k + n + 5 ∧
      (work (1 : Fin 4)).head ≤ k + 1 ∧
      (work (2 : Fin 4)).head ≤ (x.length + 1) * 3 * (n + 2) + 1 ∧
      (work (3 : Fin 4)).head ≤ n + 1) →
    (InitEnvelope inp work out ∧
      initData tm k hk x inp work out ∧
      (work (0 : Fin 4)).head ≤ 3 * k + n + 5 ∧
      (work (1 : Fin 4)).head ≤ k + 1 ∧
      (work (2 : Fin 4)).head ≤ (x.length + 1) * 3 * (n + 2) + 1 ∧
      (work (3 : Fin 4)).head ≤ n + 1) :=
  fun _ _ _ ⟨henv, hdesc, hstate, hsim, hb0, hb1, hb2, hb3⟩ =>
    ⟨henv, ⟨hdesc, hstate, hsim⟩, hb0, hb1, hb2, hb3⟩

/-- tapeStoresBools depends only on cells. -/
private theorem tapeStoresBools_cells_eq {bits : List Bool} {t t' : Tape}
    (hcells : t'.cells = t.cells) (ht : tapeStoresBools bits t) :
    tapeStoresBools bits t' := by
  obtain ⟨h0, hb, htail⟩ := ht
  exact ⟨by rw [hcells]; exact h0, fun i hi => by rw [hcells]; exact hb i hi,
         by rw [hcells]; exact htail⟩

/-- superCellsCorrect depends only on cells. -/
private theorem superCellsCorrect_cells_eq {Q : Type} {cfg : Cfg n Q} {t t' : Tape}
    (hcells : t'.cells = t.cells) (ht : superCellsCorrect cfg t) :
    superCellsCorrect cfg t' := by
  obtain ⟨hc0, he1, he2, he3⟩ := ht
  refine ⟨by rw [hcells]; exact hc0, fun pos => ?_, fun i pos => ?_, fun pos => ?_⟩
  · -- input tape encoding
    have h := he1 pos
    simp only [simTapeCellCorrect] at h ⊢
    exact ⟨by rw [hcells]; exact h.1, by rw [hcells]; exact h.2.1, by rw [hcells]; exact h.2.2⟩
  · -- work tape encoding
    have h := he2 i pos
    simp only [simTapeCellCorrect] at h ⊢
    exact ⟨by rw [hcells]; exact h.1, by rw [hcells]; exact h.2.1, by rw [hcells]; exact h.2.2⟩
  · -- output tape encoding
    have h := he3 pos
    simp only [simTapeCellCorrect] at h ⊢
    exact ⟨by rw [hcells]; exact h.1, by rw [hcells]; exact h.2.1, by rw [hcells]; exact h.2.2⟩

/-- initData depends only on tape cells, so rewinds preserve it. -/
private theorem initData_preserved_by_rewind (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) (idx : Fin 4) :
    ∀ (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin 4 → Tape) (out' : Tape),
    initData tm k hk x inp work out →
    (work' idx).cells = (work idx).cells →
    (work' idx).head = 1 →
    (∀ i, i ≠ idx → work' i = work i) →
    inp' = inp → out'.cells = out.cells → out'.head = out.head →
    initData tm k hk x inp' work' out' := by
  intro inp work out inp' work' out' ⟨hdesc, hstate, hsim⟩ hcells _ hother _ _ _
  refine ⟨?_, ?_, ?_⟩
  · -- descOnTape on tape 0
    show descOnTape _ (work' utmDescTape)
    by_cases h : idx = (0 : Fin 4)
    · subst h; exact tapeStoresBools_cells_eq hcells hdesc
    · rw [hother 0 (Ne.symm h)]; exact hdesc
  · -- stateOnTapeAt on tape 1
    show stateOnTapeAt k _ (work' utmStateTape)
    by_cases h : idx = (1 : Fin 4)
    · subst h; obtain ⟨h1, h2, h3⟩ := hstate
      exact ⟨by rw [hcells]; exact h1, fun j hj => by rw [hcells]; exact h2 j hj,
             by rw [hcells]; exact h3⟩
    · rw [hother 1 (Ne.symm h)]; exact hstate
  · -- superCellsCorrect on tape 2
    show superCellsCorrect _ (work' utmSimTape)
    by_cases h : idx = (2 : Fin 4)
    · subst h; exact superCellsCorrect_cells_eq hcells hsim
    · rw [hother 2 (Ne.symm h)]; exact hsim

/-- Enriched single rewind: carries InitEnvelope + initData + per-tape head bounds. -/
private theorem rewindWorkTM_initData_bounds_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool)
    (idx : Fin 4) (bounds : Fin 4 → ℕ) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        initData tm k hk x inp work out ∧
        ∀ i, (work i).head ≤ bounds i)
      (fun inp work out =>
        InitEnvelope inp work out ∧
        initData tm k hk x inp work out ∧
        (work idx).head = 1 ∧
        ∀ i, i ≠ idx → (work i).head ≤ bounds i)
      (bounds idx + 2) := by
  intro inp work out ⟨henv, hdata, hbounds⟩
  have hic0 := henv.1; have hins := henv.2.1; have hih := henv.2.2.1
  have hwf := henv.2.2.2.1; have hheads := henv.2.2.2.2.1
  have hoc0 := henv.2.2.2.2.2.1; have hons := henv.2.2.2.2.2.2.1; have hoh := henv.2.2.2.2.2.2.2
  -- P carries initData + InitEnvelope + head bounds for non-target tapes
  let P : Tape → (Fin 4 → Tape) → Tape → Prop := fun inp' work' out' =>
    initData tm k hk x inp' work' out' ∧
    InitEnvelope inp' work' out' ∧
    ∀ i, i ≠ idx → (work' i).head ≤ bounds i
  have hP_preserved : ∀ (i0 : Tape) (w0 : Fin 4 → Tape) (o0 : Tape)
      (i1 : Tape) (w1 : Fin 4 → Tape) (o1 : Tape),
      P i0 w0 o0 →
      (w1 idx).cells = (w0 idx).cells → (w1 idx).head = 1 →
      (∀ j, j ≠ idx → w1 j = w0 j) →
      i1 = i0 → o1.cells = o0.cells → o1.head = o0.head →
      P i1 w1 o1 := by
    intro i0 w0 o0 i1 w1 o1 ⟨hd, he, hbnds⟩ hc hh hot hi hoc hoh
    refine ⟨initData_preserved_by_rewind tm k hk x idx i0 w0 o0 i1 w1 o1 hd hc hh hot hi hoc hoh,
            ?_, fun j hne => by rw [hot j hne]; exact hbnds j hne⟩
    -- Reconstruct InitEnvelope
    obtain ⟨hic0', hins', hih', hwf', hheads', hoc0', hons', hoh'⟩ := he
    refine ⟨by rw [hi]; exact hic0', by intro j hj; rw [hi]; exact hins' j hj,
           by rw [hi]; exact hih', ⟨?_, ?_⟩, ?_,
           by rw [hoc]; exact hoc0', by intro j hj; rw [hoc]; exact hons' j hj,
           by rw [hoh]; exact hoh'⟩
    · intro j
      by_cases hj : j = idx
      · rw [hj, hc]; exact hwf'.1 idx
      · rw [hot j hj]; exact hwf'.1 j
    · intro j p hp
      by_cases hj : j = idx
      · rw [hj, hc]; exact hwf'.2 idx p hp
      · rw [hot j hj]; exact hwf'.2 j p hp
    · intro j
      by_cases hj : j = idx
      · rw [hj, hh]
      · rw [hot j hj]; exact hheads' j
  obtain ⟨c', t, ht, hreach, hhalt, hhead1, hdata', henv', hbnds'⟩ :=
    rewindWorkTM_rich_hoareTime idx (bounds idx) hP_preserved inp work out
      ⟨hwf.1 idx, hwf.2 idx, hbounds idx,
       by simp only [Tape.read]; exact hins inp.head hih,
       by simp only [Tape.read]; exact hons out.head hoh, hoh,
       fun j hne => ⟨by simp only [Tape.read]; exact hwf.2 j _ (hheads j), hheads j⟩,
       hdata, henv, fun j hne => hbounds j⟩
  exact ⟨c', t, ht, hreach, hhalt, henv', hdata', hhead1, hbnds'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Compose 4 data-preserving rewinds
-- ════════════════════════════════════════════════════════════════════════

/-- Compose 4 rewinds preserving initData, producing SimInvariant. -/
private theorem rewindAll_data_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool)
    (B0 B1 B2 B3 : ℕ) :
    (seqTM (rewindWorkTM (0 : Fin 4))
      (seqTM (rewindWorkTM (1 : Fin 4))
        (seqTM (rewindWorkTM (2 : Fin 4))
          (rewindWorkTM (3 : Fin 4))))).HoareTime
      (fun inp work out =>
        InitEnvelope inp work out ∧
        initData tm k hk x inp work out ∧
        (work (0 : Fin 4)).head ≤ B0 ∧
        (work (1 : Fin 4)).head ≤ B1 ∧
        (work (2 : Fin 4)).head ≤ B2 ∧
        (work (3 : Fin 4)).head ≤ B3)
      (fun inp work out =>
        SimInvariant tm k hk (TMEncoding.encodeTM tm) inp work out)
      (B0 + B1 + B2 + B3 + 11) := by
  let b0 : Fin 4 → ℕ := fun i => match i with | 0 => B0 | 1 => B1 | 2 => B2 | 3 => B3
  let b1 : Fin 4 → ℕ := fun i => match i with | 0 => 1  | 1 => B1 | 2 => B2 | 3 => B3
  let b2 : Fin 4 → ℕ := fun i => match i with | 0 => 1  | 1 => 1  | 2 => B2 | 3 => B3
  let b3 : Fin 4 → ℕ := fun i => match i with | 0 => 1  | 1 => 1  | 2 => 1  | 3 => B3
  let midP (bds : Fin 4 → ℕ) : TapePred 4 := fun inp work out =>
    InitEnvelope inp work out ∧ initData tm k hk x inp work out ∧
    ∀ i, (work i).head ≤ bds i
  -- Helper: merge head = 1 for target + bounds for non-target into midP
  have merge_bounds :
      ∀ (target : Fin 4) (pre_bds post_bds : Fin 4 → ℕ),
      (∀ i, i ≠ target → post_bds i = pre_bds i) →
      (post_bds target = 1) →
      ∀ inp work out,
      (InitEnvelope inp work out ∧ initData tm k hk x inp work out ∧
        (work target).head = 1 ∧ ∀ i, i ≠ target → (work i).head ≤ pre_bds i) →
      midP post_bds inp work out := by
    intro target pre_bds post_bds hne htgt inp work out ⟨he, hd, hh, hrest⟩
    exact ⟨he, hd, fun i => by
      by_cases h : i = target
      · subst h; rw [hh]; rw [htgt]
      · rw [hne i h]; exact hrest i h⟩
  -- Build each rewind's HoareTime
  have h_rw0 : (rewindWorkTM (0 : Fin 4)).HoareTime (midP b0) (midP b1) (B0 + 2) :=
    (rewindWorkTM_initData_bounds_hoareTime tm k hk x 0 b0).consequence
      (fun _ _ _ h => h)
      (merge_bounds 0 b0 b1 (by intro i hi; match i with | 1 => rfl | 2 => rfl | 3 => rfl) rfl)
      (by show B0 + 2 ≤ B0 + 2; omega)
  have h_rw1 : (rewindWorkTM (1 : Fin 4)).HoareTime (midP b1) (midP b2) (B1 + 2) :=
    (rewindWorkTM_initData_bounds_hoareTime tm k hk x 1 b1).consequence
      (fun _ _ _ h => h)
      (merge_bounds 1 b1 b2 (by intro i hi; match i with | 0 => rfl | 2 => rfl | 3 => rfl) rfl)
      (by show B1 + 2 ≤ B1 + 2; omega)
  have h_rw2 : (rewindWorkTM (2 : Fin 4)).HoareTime (midP b2) (midP b3) (B2 + 2) :=
    (rewindWorkTM_initData_bounds_hoareTime tm k hk x 2 b2).consequence
      (fun _ _ _ h => h)
      (merge_bounds 2 b2 b3 (by intro i hi; match i with | 0 => rfl | 1 => rfl | 3 => rfl) rfl)
      (by show B2 + 2 ≤ B2 + 2; omega)
  have h_rw3 : (rewindWorkTM (3 : Fin 4)).HoareTime (midP b3)
      (fun inp work out => SimInvariant tm k hk (TMEncoding.encodeTM tm) inp work out)
      (B3 + 2) :=
    (rewindWorkTM_initData_bounds_hoareTime tm k hk x 3 b3).consequence
      (fun _ _ _ h => h)
      (fun inp work out ⟨he, ⟨hdesc, hstate, hsim⟩, hh3, hrest⟩ =>
        postRewindsAndData_to_simInvariant tm k x hk inp work out he
          (fun i => by
            have hge := he.2.2.2.2.1 i
            match i with
            | 0 => have := hrest 0 (by decide); dsimp [b3] at this; omega
            | 1 => have := hrest 1 (by decide); dsimp [b3] at this; omega
            | 2 => have := hrest 2 (by decide); dsimp [b3] at this; omega
            | 3 => exact hh3)
          hdesc hstate hsim)
      (by show B3 + 2 ≤ B3 + 2; omega)
  -- h_trans: InitEnvelope → seqTransition is identity
  have h_trans_midP : ∀ bds, ∀ inp work out, midP bds inp work out →
      midP bds (seqTransitionInput inp) (fun i => seqTransitionTape (work i))
        (seqTransitionTape out) := by
    intro bds; exact h_trans_envelope (fun _ _ _ ⟨he, _, _⟩ => he)
  -- Compose via seqTM_hoareTime
  exact (seqTM_hoareTime _ _ h_rw0 (h_trans_midP b1)
    (seqTM_hoareTime _ _ h_rw1 (h_trans_midP b2)
      (seqTM_hoareTime _ _ h_rw2
        (h_trans_envelope (fun _ _ _ ⟨he, _, _⟩ => he))
        h_rw3))).consequence
    (fun inp work out ⟨he, hd, h0, h1, h2, h3⟩ =>
      (⟨he, hd, fun i => by match i with
        | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3⟩ :
        midP b0 inp work out))
    (fun _ _ _ h => h)
    (by show B0 + 2 + 1 + (B1 + 2 + 1 + (B2 + 2 + 1 + (B3 + 2))) ≤ B0 + B1 + B2 + B3 + 11
        omega)

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1+2: copy + rewind tape 0 (rich rewind preserving copy data)
-- ════════════════════════════════════════════════════════════════════════

/-- Cell-dependent data from postCopy that survives rewind of tape 0. -/
private def copyData (tm : TM n) (x : List Bool) : TapePred 4 :=
  fun inp work out =>
    let desc := TMEncoding.encodeTM tm
    descOnTape desc (work 0) ∧
    (∀ i : Fin 4, i ≠ 0 → (work i).cells = (initTape []).cells ∧ (work i).head = 1) ∧
    WorkTapesWF work ∧
    (work 0).head ≥ 1 ∧
    inp.cells = (initTape (encodeUTMInput tm x)).cells ∧
    inp.head = desc.length + 1 ∧
    out.cells = (initTape []).cells ∧
    out.head = 1

/-- copyData is preserved through rewind of tape 0 (depends only on cells). -/
private theorem copyData_preserved (tm : TM n) (x : List Bool) :
    ∀ (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin 4 → Tape) (out' : Tape),
    copyData tm x inp work out →
    (work' (0 : Fin 4)).cells = (work 0).cells →
    (work' (0 : Fin 4)).head = 1 →
    (∀ i, i ≠ (0 : Fin 4) → work' i = work i) →
    inp' = inp → out'.cells = out.cells → out'.head = out.head →
    copyData tm x inp' work' out' := by
  intro inp work out inp' work' out'
    ⟨hdesc, hother, hwf, hh0, hinpc, hinph, houtc, houth⟩
    hw0_cells hw0_head hother' hinp' hout_cells' hout_head'
  refine ⟨tapeStoresBools_cells_eq hw0_cells hdesc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hother' i hi]; exact hother i hi
  · constructor
    · intro i; by_cases hi : i = (0 : Fin 4)
      · subst hi; rw [hw0_cells]; exact hwf.1 0
      · rw [hother' i hi]; exact hwf.1 i
    · intro i j hj; by_cases hi : i = (0 : Fin 4)
      · subst hi; rw [hw0_cells]; exact hwf.2 0 j hj
      · rw [hother' i hi]; exact hwf.2 i j hj
  · rw [hw0_head]
  · rw [hinp']; exact hinpc
  · rw [hinp']; exact hinph
  · rw [hout_cells']; exact houtc
  · rw [hout_head']; exact houth

/-- postCopy implies copyData (strip head-dependent data for tape 0). -/
private theorem postCopy_to_copyData (tm : TM n) (x : List Bool) :
    ∀ inp work out, postCopy tm x inp work out → copyData tm x inp work out := by
  intro inp work out h
  obtain ⟨hd, hw0, hinp, hhead, hout_head, hwf, hcells, hinp_cells, hout_cells⟩ := h
  exact ⟨hd, fun i hi => ⟨hcells i hi, hhead i hi⟩, hwf, by rw [hw0]; omega,
         hinp_cells, hinp, hout_cells, hout_head⟩

/-- HoareTime for rewindWorkTM 0 preserving copyData. -/
private theorem rewind0_copyData_hoareTime (tm : TM n) (x : List Bool) :
    (rewindWorkTM (0 : Fin 4)).HoareTime
      (fun inp work out =>
        copyData tm x inp work out ∧
        (work (0 : Fin 4)).head ≤ (TMEncoding.encodeTM tm).length + 1)
      (fun inp work out =>
        copyData tm x inp work out ∧
        (work (0 : Fin 4)).head = 1)
      ((TMEncoding.encodeTM tm).length + 3) := by
  -- Uses rewindWorkTM_rich_hoareTime with P = copyData, then consequence to match pre/post.
  -- Pre-adaptation: copyData ∧ head ≤ B → rich_rewind pre (WF + read conditions + P)
  -- Post-adaptation: head = 1 ∧ P → P ∧ head = 1 (trivial reorder)
  exact (rewindWorkTM_rich_hoareTime (0 : Fin 4) ((TMEncoding.encodeTM tm).length + 1)
    (copyData_preserved tm x)).consequence
    (fun inp work out h => by
      obtain ⟨⟨hdesc, hother, hwf, hinpc, hinph, houtc, houth⟩, hhead⟩ := h
      refine ⟨hwf.1 0, hwf.2 0, hhead, ?_, ?_, ?_, ?_,
              hdesc, hother, hwf, hinpc, hinph, houtc, houth⟩
      all_goals sorry)
    (fun _ _ _ ⟨hhead, hdata⟩ => ⟨hdata, hhead⟩)
    (by omega)

/-- (copyData + head=1) implies setupStateTM precondition. -/
private theorem copyDataHead1_to_setupStatePre (tm : TM n) (k : ℕ)
    (x : List Bool) (hk : k = @Fintype.card tm.Q tm.finQ) :
    ∀ inp work out,
    (copyData tm x inp work out ∧ (work (0 : Fin 4)).head = 1) →
    (InitEnvelope inp work out ∧
      descOnTape (TMEncoding.encodeTM tm) (work utmDescTape) ∧
      (work utmDescTape).head = 1 ∧
      (work utmStateTape).cells = (initTape []).cells ∧
      (work utmStateTape).head = 1 ∧
      (work utmSimTape).cells = (initTape []).cells ∧
      (work utmScratchTape).cells = (initTape []).cells ∧
      (work utmScratchTape).head = 1) := by
  intro inp work out ⟨⟨hdesc, hother, hwf, _, hinpc, hinph, houtc, houth⟩, hhead⟩
  have h1 := hother 1 (by decide)
  have h2 := hother 2 (by decide)
  have h3 := hother 3 (by decide)
  -- Reconstruct InitEnvelope from cell data (same pattern as postCopy_to_initEnvelope)
  have initTape_ne_start : ∀ (contents : List Γ) (j : ℕ),
      (∀ g ∈ contents, g ≠ Γ.start) → j ≥ 1 → (initTape contents).cells j ≠ Γ.start := by
    intro contents j hns hj habs
    simp only [initTape, show j ≠ 0 from by omega] at habs
    cases hg : contents[j - 1]? with
    | none => simp [hg] at habs
    | some val =>
      simp [hg] at habs
      have hlt : j - 1 < contents.length := by
        by_contra hge; have : contents.length ≤ j - 1 := by omega
        simp [List.getElem?_eq_none_iff.mpr this] at hg
      have heq := List.getElem?_eq_getElem hlt; rw [hg] at heq
      have : contents[j - 1] = val := Option.some.inj heq.symm
      exact hns val (this ▸ List.getElem_mem ..) habs
  have henv : InitEnvelope inp work out := by
    refine ⟨by rw [hinpc]; rfl,
            by intro j hj; rw [hinpc]; exact initTape_ne_start _ j (encodeUTMInput_ne_start tm x) hj,
            by rw [hinph]; omega,
            hwf, ?_, by rw [houtc]; rfl,
            by intro j hj; rw [houtc]; exact initTape_ne_start _ j (by intro g hg; simp at hg) hj,
            by rw [houth]⟩
    intro i; by_cases h : i = (0 : Fin 4)
    · subst h; omega
    · have := (hother i h).2; omega
  exact ⟨henv, hdesc, hhead, h1.1, h1.2, h2.1, h3.1, h3.2⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 3+4: setupState + rewind tape 3 (rich rewind preserving state data)
-- ════════════════════════════════════════════════════════════════════════

/-- Cell-dependent data from setupState that survives rewind of tape 3.
    Note: state tape head bound (≤ k+1) comes from setupSim, not setupState. -/
private def setupStateData (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (_x : List Bool) : TapePred 4 :=
  fun inp work out =>
    InitEnvelope inp work out ∧
    descOnTape (TMEncoding.encodeTM tm) (work utmDescTape) ∧
    stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
    (work utmSimTape).cells = (initTape []).cells ∧
    tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
    (work utmDescTape).head ≤ 3 * k + n + 5

/-- setupStateData is preserved through rewind of tape 3 (scratch). -/
private theorem setupStateData_preserved (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) :
    ∀ (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin 4 → Tape) (out' : Tape),
    setupStateData tm k hk x inp work out →
    (work' (3 : Fin 4)).cells = (work 3).cells →
    (work' (3 : Fin 4)).head = 1 →
    (∀ i, i ≠ (3 : Fin 4) → work' i = work i) →
    inp' = inp → out'.cells = out.cells → out'.head = out.head →
    setupStateData tm k hk x inp' work' out' := by
  intro inp work out inp' work' out'
    ⟨henv, hdesc, hstate, hsim, hsc, hd_head⟩
    hw3_cells _hw3_head hother' hinp' hout_cells' hout_head'
  obtain ⟨hic, hins, hih, hwf, hheads, hoc, hons, hoh⟩ := henv
  have hwf' : WorkTapesWF work' := by
    constructor
    · intro i; by_cases h : i = (3 : Fin 4)
      · subst h; rw [hw3_cells]; exact hwf.1 3
      · rw [hother' i h]; exact hwf.1 i
    · intro i j hj; by_cases h : i = (3 : Fin 4)
      · subst h; rw [hw3_cells]; exact hwf.2 3 j hj
      · rw [hother' i h]; exact hwf.2 i j hj
  have hheads' : ∀ i : Fin 4, (work' i).head ≥ 1 := by
    intro i; by_cases h : i = (3 : Fin 4)
    · subst h; omega
    · rw [hother' i h]; exact hheads i
  exact ⟨⟨by rw [hinp']; exact hic, by intro j hj; rw [hinp']; exact hins j hj,
          by rw [hinp']; exact hih, hwf', hheads',
          by rw [hout_cells']; exact hoc,
          by intro j hj; rw [hout_cells']; exact hons j hj,
          by rw [hout_head']; exact hoh⟩,
         by rw [hother' 0 (by decide)]; exact hdesc,
         by rw [hother' 1 (by decide)]; exact hstate,
         by rw [hother' 2 (by decide)]; exact hsim,
         tapeStoresBools_cells_eq hw3_cells hsc,
         by rw [hother' 0 (by decide)]; exact hd_head⟩

/-- HoareTime for rewindWorkTM 3 preserving setupStateData. -/
private theorem rewind3_setupStateData_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) :
    (rewindWorkTM (3 : Fin 4)).HoareTime
      (fun inp work out =>
        setupStateData tm k hk x inp work out ∧
        (work (3 : Fin 4)).head ≤ n + 1)
      (fun inp work out =>
        setupStateData tm k hk x inp work out ∧
        (work (3 : Fin 4)).head = 1)
      (n + 3) := by
  exact (rewindWorkTM_rich_hoareTime (3 : Fin 4) (n + 1)
    (setupStateData_preserved tm k hk x)).consequence
    (fun inp work out h => by
      obtain ⟨⟨henv, hdesc, hstate, hsim, hsc, hd_head⟩, hhead⟩ := h
      have ⟨hic, hins, hih, hwf, hheads, hoc, hons, hoh⟩ := henv
      exact ⟨hwf.1 3, hwf.2 3, hhead,
             by simp only [Tape.read]; exact hins _ hih,
             by simp only [Tape.read]; exact hons _ hoh,
             hoh,
             fun i hi => ⟨by simp only [Tape.read]; exact hwf.2 i _ (hheads i), hheads i⟩,
             henv, hdesc, hstate, hsim, hsc, hd_head⟩)
    (fun _ _ _ ⟨hhead, hdata⟩ => ⟨hdata, hhead⟩)
    (by omega)

-- ════════════════════════════════════════════════════════════════════════
-- Bridges between phases
-- ════════════════════════════════════════════════════════════════════════

/-- postCopy → rewind0 precondition. -/
private theorem postCopy_to_rewind0Pre (tm : TM n) (x : List Bool) :
    ∀ inp work out, postCopy tm x inp work out →
    copyData tm x inp work out ∧
    (work (0 : Fin 4)).head ≤ (TMEncoding.encodeTM tm).length + 1 := by
  intro inp work out h
  exact ⟨postCopy_to_copyData tm x inp work out h, by show _ ≤ _; rw [h.2.1]⟩

/-- setupState post → (setupStateData + head(3) ≤ n+1). -/
private theorem setupStatePost_to_rewind3Pre (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) :
    ∀ inp work out,
    (InitEnvelope inp work out ∧
      descOnTape (TMEncoding.encodeTM tm) (work utmDescTape) ∧
      stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
      (work utmSimTape).cells = (initTape []).cells ∧
      tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
      (work utmDescTape).head ≤ 3 * k + n + 5 ∧
      (work utmScratchTape).head ≤ n + 1) →
    (setupStateData tm k hk x inp work out ∧
      (work (3 : Fin 4)).head ≤ n + 1) := by
  intro inp work out ⟨henv, hdesc, hstate, hsim, hsc, hd_head, hsc_head⟩
  exact ⟨⟨henv, hdesc, hstate, hsim, hsc, hd_head⟩, hsc_head⟩

/-- (setupStateData + head(3)=1) → setupSim precondition. -/
private theorem setupStateDataHead1_to_setupSimPre (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (x : List Bool) :
    ∀ inp work out,
    (setupStateData tm k hk x inp work out ∧ (work (3 : Fin 4)).head = 1) →
    (InitEnvelope inp work out ∧
      descOnTape (TMEncoding.encodeTM tm) (work utmDescTape) ∧
      stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
      (work utmSimTape).cells = (initTape []).cells ∧
      (work utmSimTape).head = 1 ∧
      tapeStoresBools (List.replicate n true) (work utmScratchTape) ∧
      (work utmScratchTape).head = 1 ∧
      inp.cells inp.head = Γ.blank ∧
      (∀ (i : ℕ) (hi : i < x.length),
        inp.cells (inp.head + 1 + i) = Γ.ofBool (x.get ⟨i, hi⟩)) ∧
      inp.cells (inp.head + 1 + x.length) = Γ.blank ∧
      (work utmDescTape).head ≤ 3 * k + n + 5 ∧
      (work utmStateTape).head ≤ k + 1) := by
  sorry

-- ════════════════════════════════════════════════════════════════════════
-- Main composition
-- ════════════════════════════════════════════════════════════════════════

/-- **initTM_hoareTime'**: from initial tapes with encoded `⟨M, x⟩`,
    `initTM` establishes `SimInvariant` for `tm.initCfg x`. -/
theorem initTM_hoareTime' (tm : TM n) (k : ℕ)
    (x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    let desc := TMEncoding.encodeTM tm
    ∃ B, initTM.HoareTime
      (initTM_pre tm x)
      (SimInvariant tm k hk desc)
      B := by
  set desc := TMEncoding.encodeTM tm with desc_def
  -- ── Phase specs ────────────────────────────────────────────────────
  have h_copy := copyInputToWorkTM_hoareTime tm x
  have h_rw0 := rewind0_copyData_hoareTime tm x
  have h_setup_state := setupStateTM_hoareTime' tm k x hk
  have h_rw3 := rewind3_setupStateData_hoareTime tm k hk x
  have h_setup_sim := setupSimTM_hoareTime' tm k x hk
  have h_rewinds := rewindAll_data_hoareTime tm k hk x
    (3 * k + n + 5) (k + 1) ((x.length + 1) * 3 * (n + 2) + 1) (n + 1)
  -- ── Compose phases 1-9 via seqTM_hoareTime ────────────────────────
  -- Each seqTM adds b₁ + 1 + b₂ to the bound.
  -- Intermediate predicates:
  --   copy post = postCopy → (consequence) → rw0 pre = copyData ∧ head ≤ B
  --   rw0 post = copyData ∧ head = 1 → (bridge) → setupState pre
  --   setupState post → (bridge) → rw3 pre = setupStateData ∧ head ≤ n+1
  --   rw3 post = setupStateData ∧ head = 1 → (bridge) → setupSim pre
  --   setupSim post → (bridge: postSetupSim_to_rewindAll) → rewinds pre
  -- seqTransition bridges: all preds imply InitEnvelope, so identity.
  --
  -- The composition follows the structure:
  --   initTM = seqTM copy (seqTM rw0 (seqTM setupState (seqTM rw3
  --              (seqTM setupSim rewinds))))
  -- where rewinds = seqTM rw0' (seqTM rw1 (seqTM rw2 rw3'))
  --
  -- Each seqTM_hoareTime needs: h₁, h_trans, h₂
  -- h_trans uses h_trans_envelope since all predicates imply InitEnvelope
  -- h₁/h₂ use .consequence to adapt pre/post

  -- Bridge: intermediate predicates imply InitEnvelope (for seqTransition identity)
  -- copyData doesn't directly carry InitEnvelope, but it's derivable from cells + WF
  have h_copyData_env : ∀ inp work out,
      (copyData tm x inp work out ∧ (work (0 : Fin 4)).head ≤ desc.length + 1) →
      InitEnvelope inp work out := by
    -- Derivable from copyData (which includes WorkTapesWF, head ≥ 1, cell data)
    -- Same InitEnvelope construction as in copyDataHead1_to_setupStatePre
    sorry
  have h_copyDataPost_env : ∀ inp work out,
      (copyData tm x inp work out ∧ (work (0 : Fin 4)).head = 1) →
      InitEnvelope inp work out := by
    intro inp work out ⟨hcd, hh⟩
    exact (copyDataHead1_to_setupStatePre tm k x hk inp work out ⟨hcd, hh⟩).1
  have h_setupStateData_env : ∀ inp work out,
      (setupStateData tm k hk x inp work out ∧ (work (3 : Fin 4)).head ≤ n + 1) →
      InitEnvelope inp work out :=
    fun _ _ _ ⟨⟨henv, _⟩, _⟩ => henv
  have h_setupStateDataPost_env : ∀ inp work out,
      (setupStateData tm k hk x inp work out ∧ (work (3 : Fin 4)).head = 1) →
      InitEnvelope inp work out :=
    fun _ _ _ ⟨⟨henv, _⟩, _⟩ => henv

  -- Total bound: sum of all sub-bounds + seqTM transitions
  refine ⟨?_, ?_⟩
  · -- Bound value
    exact copyBound desc.length + 1 +
      (desc.length + 3) + 1 +
      (3 * k + n + 5) + 1 +
      (n + 3) + 1 +
      (3 * n + 9 + x.length * (4 * n + 9)) + 1 +
      ((3 * k + n + 5) + (k + 1) + ((x.length + 1) * 3 * (n + 2) + 1) + (n + 1) + 11)
  · -- Compose via seqTM_hoareTime
    exact (seqTM_hoareTime _ _
      -- Phase 1: copy (pre=initTM_pre, post=postCopy, consequence to rw0 pre)
      (h_copy.consequence (fun _ _ _ h => h)
        (postCopy_to_rewind0Pre tm x) (le_refl _))
      -- Bridge 1→2: seqTransition identity
      (h_trans_envelope h_copyData_env)
      -- Phases 2-9
      (seqTM_hoareTime _ _
        -- Phase 2: rw0 (pre/post = copyData ∧ head)
        h_rw0
        -- Bridge 2→3: seqTransition identity
        (h_trans_envelope h_copyDataPost_env)
        -- Phases 3-9
        (seqTM_hoareTime _ _
          -- Phase 3: setupState (consequence: copyDataHead1 → setupState pre → setupState post → rw3 pre)
          (h_setup_state.consequence
            (copyDataHead1_to_setupStatePre tm k x hk)
            (setupStatePost_to_rewind3Pre tm k hk x)
            (le_refl _))
          -- Bridge 3→4: seqTransition identity
          (h_trans_envelope h_setupStateData_env)
          -- Phases 4-9
          (seqTM_hoareTime _ _
            -- Phase 4: rw3 (pre/post = setupStateData ∧ head)
            h_rw3
            -- Bridge 4→5: seqTransition identity
            (h_trans_envelope h_setupStateDataPost_env)
            -- Phases 5-9
            (seqTM_hoareTime _ _
              -- Phase 5: setupSim (consequence: setupStateDataHead1 → setupSim pre → setupSim post → rewinds pre)
              (h_setup_sim.consequence
                (setupStateDataHead1_to_setupSimPre tm k hk x)
                (postSetupSim_to_rewindAll tm k hk x)
                (le_refl _))
              -- Bridge 5→6: seqTransition identity
              (h_trans_envelope (fun _ _ _ h => And.left h))
              -- Phases 6-9: final 4 rewinds
              h_rewinds))))).consequence
      (fun _ _ _ h => h)
      (fun _ _ _ h => h)
      (by simp only [desc_def, copyBound]; omega)

end TM
