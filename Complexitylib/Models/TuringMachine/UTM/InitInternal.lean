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

/-- The setupSim postcondition implies the rewindAll precondition. -/
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
      (work (0 : Fin 4)).head ≤ 3 * k + n + 5 ∧
      (work (1 : Fin 4)).head ≤ k + 1 ∧
      (work (2 : Fin 4)).head ≤ (x.length + 1) * 3 * (n + 2) + 1 ∧
      (work (3 : Fin 4)).head ≤ n + 1) :=
  fun _ _ _ ⟨henv, _, _, _, hb0, hb1, hb2, hb3⟩ =>
    ⟨henv, hb0, hb1, hb2, hb3⟩

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
-- Main composition (sorry'd due to bridge lemma)
-- ════════════════════════════════════════════════════════════════════════

/-- **initTM_hoareTime**: from initial tapes with encoded `⟨M, x⟩`,
    `initTM` establishes `SimInvariant` for `tm.initCfg x`. -/
theorem initTM_hoareTime' (tm : TM n) (k : ℕ)
    (x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    let desc := TMEncoding.encodeTM tm
    ∃ B, initTM.HoareTime
      (initTM_pre tm x)
      (SimInvariant tm k hk desc)
      B := by
  have h := (copyInputToWorkTM_hoareTime tm x).toHoare
  sorry

end TM
