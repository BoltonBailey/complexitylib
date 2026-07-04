import Complexitylib.Models.TuringMachine.UTM.BodyMatch
import Complexitylib.Models.TuringMachine.UTM.BodyApply
import Complexitylib.Models.TuringMachine.UTM.DescLayout
import Complexitylib.Models.TuringMachine.UTM.Verdict

/-!
# Body correctness: phase assembly

The per-iteration proof of the body machine, assembled from the phase
lemmas. This file starts with the standing invariant `SimInv` (the tape
shape between loop iterations, relative to the interpreted machine's
configuration) and the halt-check phase: from the body's start state, a
halted interpreted machine makes the body a bounded-time no-op, and a
running one brings it to the peek phase with all tapes restored.
-/

namespace TM.UTMBody

open BodyQ

/-- `Γw.toΓ` is injective. -/
theorem Γw.toΓ_inj {x y : Γw} (h : x.toΓ = y.toΓ) : x = y := by
  cases x <;> cases y <;> simp_all [Γw.toΓ]

/-- `Γw.toΓ` hits `Γ.blank` only at `□`. -/
theorem Γw.toΓ_eq_blank {x : Γw} : x.toΓ = Γ.blank ↔ x = Γw.blank := by
  cases x <;> simp [Γw.toΓ]

/-- The body's standing tape shape between loop iterations, relative to a
    configuration `mc` of the interpreted machine `(decodeDesc α).toTM`.
    The state-tape clause is a disjunction: the running shape (the `w`-bit
    encoding of the current state) or the post-default shape (the qhalt
    field verbatim — the machine is then halted). -/
structure SimInv (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (inp : Tape) (work : Fin 6 → Tape) (out : Tape) : Prop where
  vin : VShift mc.input (work vIn)
  vwk : VShift (mc.work 0) (work vWk)
  vout : VShift mc.output (work vOut)
  wf_in : mc.input.WFCells
  wf_wk : (mc.work 0).WFCells
  wf_out : mc.output.WFCells
  state : (mc.state.val < 2 ^ (decodeDesc α).w ∧
      (work stT).HoldsExact
        (bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)))
    ∨ (mc.state = (decodeDesc α).toTM.qhalt ∧
      (work stT).HoldsExact (qhaltField (groupPairs α)))
  state_head : (work stT).head = 1
  desc : (work dsT).HoldsExact (groupPairs α)
  desc_head : (work dsT).head = 1
  scratch : (work scT).HoldsExact []
  scratch_head : (work scT).head = 1
  inp_read : inp.read ≠ Γ.start
  out_read : out.read ≠ Γ.start

namespace SimInv

/-- The state tape's contents (either disjunct) are blank-free. -/
theorem state_syms_ne_blank {α mc inp work out}
    (h : SimInv α mc inp work out) :
    ∃ S : List Γw, (work stT).HoldsExact S ∧ (∀ s ∈ S, s ≠ Γw.blank) ∧
      ((mc.state.val < 2 ^ (decodeDesc α).w ∧
        S = bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)) ∨
       (mc.state = (decodeDesc α).toTM.qhalt ∧
        S = qhaltField (groupPairs α))) := by
  rcases h.state with ⟨hlt, hh⟩ | ⟨hq, hh⟩
  · exact ⟨_, hh, fun s hs => bitsToSyms_ne_blank hs, Or.inl ⟨hlt, rfl⟩⟩
  · exact ⟨_, hh, fun s hs => takeField_fst_ne_blank _ s hs, Or.inr ⟨hq, rfl⟩⟩

/-- Standard parked-reads package for the non-state, non-desc work tapes. -/
theorem others_read {α mc inp work out} (h : SimInv α mc inp work out) :
    ∀ i : Fin 6, i ≠ stT → i ≠ dsT → (work i).read ≠ Γ.start := by
  intro i hiS hiD
  rcases i with ⟨iv, hv⟩
  rcases iv with _ | _ | _ | _ | _ | _ | n
  · exact h.vin.read_ne_start h.wf_in
  · exact h.vwk.read_ne_start h.wf_wk
  · exact h.vout.read_ne_start h.wf_out
  · exact absurd rfl hiS
  · exact absurd rfl hiD
  · show (work scT).read ≠ Γ.start
    rw [Tape.read, h.scratch_head, show (1 : ℕ) = 0 + 1 from rfl,
      (Tape.HoldsExact.nil_iff.mp h.scratch).2 0]
    simp
  · exact absurd hv (by omega)

/-- Any `HoldsExact` tape with head off `▷` reads a non-`▷` symbol. -/
theorem read_ne_start_of_holdsExact {t : Tape} {l : List Γw}
    (h : t.HoldsExact l) (hh : 1 ≤ t.head) : t.read ≠ Γ.start :=
  (Tape.HoldsExact.wfCells h).2 _ hh

end SimInv

-- ════════════════════════════════════════════════════════════════════════
-- Phase 0: the halt check
-- ════════════════════════════════════════════════════════════════════════

section HcPhase

variable {α : List Bool} {mc : Cfg 1 (decodeDesc α).toTM.Q}

/-- A tape whose head is known equals the literal rebuild. -/
private theorem tape_mk_eq {t : Tape} {h : ℕ} (hh : t.head = h) :
    (⟨h, t.cells⟩ : Tape) = t := by
  cases t
  subst hh
  rfl

private theorem takeField_fst_length_le (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem takeField_snd_length_le (l : List Γw) :
    (takeField l).2.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨-, hsp⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · rw [hsp]
    simp

private theorem qhaltField_length_le (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le (takeField l).2) (takeField_snd_length_le l)

/-- **Halt-check phase, halted case**: when the interpreted machine sits at
    its halt state, the body runs from its start state to `bodyDone` as a
    pure no-op — every tape is exactly restored — within
    `5·|groupPairs α| + 7` steps. -/
theorem hcPhase_halted (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc0)
    (hinv : SimInv α mc c.input c.work c.output)
    (hhalt : mc.state = (decodeDesc α).toTM.qhalt) :
    ∃ c' t, t ≤ 5 * (groupPairs α).length + 7 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = bodyDone ∧
      c'.input = c.input ∧ (∀ i, c'.work i = c.work i) ∧
      c'.output = c.output := by
  obtain ⟨S, hS_hold, hS_nb, hS_which⟩ := hinv.state_syms_ne_blank
  -- in the halted case the state tape holds exactly the qhalt field
  have hSq : S = qhaltField (groupPairs α) := by
    rcases hS_which with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
    · exact (verdict_running α hlt).mpr (by rw [hhalt]; rfl)
    · rfl
  subst hSq
  have hS_wns : ∀ j, 1 ≤ j → (c.work stT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.wfCells hS_hold).2
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.wfCells hinv.desc).2
  have hoth_d : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS
      exact SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
    · exact hinv.others_read i hiS hiD
  -- Phase hc0: scan past field 1
  obtain ⟨c₁, hr₁, hst₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    scanRight_loop (cur := hc0) (next := hc1) (t := dsT)
      (fun hcon => nomatch hcon) arm_hc0
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c hst rfl hinv.desc_head hinv.inp_read hinv.out_read
      (fun i hi => hoth_d i hi)
  have hstS₁ : c₁.work stT = c.work stT := hoth₁ stT (by decide)
  -- Phase hc1: lockstep match against the qhalt field
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    hc1_match_loop (c.work stT).cells (c.work dsT).cells hS_wns hW_wns
      (qhaltField (groupPairs α)).length 1
      ((takeField (groupPairs α)).1.length + 2) (by omega) (by omega)
      (fun j hj => by
        constructor
        · rw [show 1 + j = j + 1 by omega,
            Tape.HoldsExact.cells_lt hS_hold hj]
          exact (descLayout_field2_val hinv.desc j hj).symm
        · rw [show 1 + j = j + 1 by omega,
            Tape.HoldsExact.cells_lt hS_hold hj]
          intro hcon
          exact (hS_nb _ (List.getElem_mem hj)) (Γw.toΓ_eq_blank.mp hcon)
      )
      (by
        rw [show 1 + (qhaltField (groupPairs α)).length
            = (qhaltField (groupPairs α)).length + 1 by omega]
        exact Tape.HoldsExact.cells_ge hS_hold (Nat.le_refl _))
      (descLayout_sep2 hinv.desc)
      c₁ hst₁
      (by rw [hstS₁]) (by rw [hstS₁, hinv.state_head])
      (by rw [hwtD₁]) (by rw [hwtD₁]; dsimp only; omega)
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hiS hiD => by rw [hoth₁ i hiD]; exact hoth_d i hiD)
  -- Phase haltRewS: rewind the state head
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hin₃, hout₃, hoth₃⟩ :=
    rewStep_loop (cur := haltRewS) (next := haltRewD) (t := stT)
      (fun hcon => nomatch hcon) arm_haltRewS
      (c.work stT).cells hS_hold.1 hS_wns
      (1 + (qhaltField (groupPairs α)).length) c₂ hst₂
      (by rw [hwtS₂]) (by rw [hwtS₂])
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hwtD₂]
          exact hW_wns ((takeField (groupPairs α)).1.length + 2
            + (qhaltField (groupPairs α)).length) (by omega)
        · rw [hoth₂ i hi hiD, hoth₁ i hiD]
          exact hoth_d i hiD)
  -- Phase haltRewD: rewind the desc head
  obtain ⟨c₄, hr₄, hst₄, hwtD₄, hin₄, hout₄, hoth₄⟩ :=
    rewStep_loop (cur := haltRewD) (next := bodyDone) (t := dsT)
      (fun hcon => nomatch hcon) arm_haltRewD
      (c.work dsT).cells hinv.desc.1 hW_wns
      ((takeField (groupPairs α)).1.length + 2
        + (qhaltField (groupPairs α)).length) c₃ hst₃
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₃]
          exact hS_wns 1 (by omega)
        · rw [hoth₃ i hiS, hoth₂ i hiS hi, hoth₁ i hi]
          exact hoth_d i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₄,
    ((takeField (groupPairs α)).1.length + 1)
      + ((qhaltField (groupPairs α)).length + 1)
      + ((1 + (qhaltField (groupPairs α)).length) + 1)
      + (((takeField (groupPairs α)).1.length + 2
          + (qhaltField (groupPairs α)).length) + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, by rw [hin₄, hin₃, hin₂, hin₁], ?_,
    by rw [hout₄, hout₃, hout₂, hout₁]⟩
  intro i
  by_cases hiS : i = stT
  · subst hiS
    rw [hoth₄ stT (by decide), hwtS₃]
    exact tape_mk_eq hinv.state_head
  · by_cases hiD : i = dsT
    · subst hiD
      rw [hwtD₄]
      exact tape_mk_eq hinv.desc_head
    · rw [hoth₄ i hiD, hoth₃ i hiS, hoth₂ i hiS hiD, hoth₁ i hiD]

/-- **Halt-check phase, running case**: when the interpreted machine is not
    at its halt state, the body's halt check falls through to the peek
    phase with every tape exactly restored, within
    `5·|groupPairs α| + 7` steps. -/
theorem hcPhase_running (c : Cfg 6 bodyTM.Q)
    (hst : c.state = hc0)
    (hinv : SimInv α mc c.input c.work c.output)
    (hrun : mc.state ≠ (decodeDesc α).toTM.qhalt) :
    ∃ c' t, t ≤ 5 * (groupPairs α).length + 7 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = peek1 ∧
      c'.input = c.input ∧ (∀ i, c'.work i = c.work i) ∧
      c'.output = c.output := by
  -- the state clause must be the running disjunct
  rcases hinv.state with ⟨hlt, hS_hold⟩ | ⟨hq, -⟩
  swap
  · exact absurd hq hrun
  have hS_nb : ∀ s ∈ bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val),
      s ≠ Γw.blank := fun s hs => bitsToSyms_ne_blank hs
  -- the state encoding differs from the qhalt field
  have hne_list : bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val)
      ≠ qhaltField (groupPairs α) := by
    intro hcon
    exact hrun (Fin.val_injective ((verdict_running α hlt).mp hcon))
  obtain ⟨n, hnA, hnB, hagree, hmm⟩ :=
    exists_first_mismatch hS_nb
      (fun s hs => takeField_fst_ne_blank _ s hs) hne_list
  have hnB' : n ≤ (qhaltField (groupPairs α)).length := hnB
  have hS_wns : ∀ j, 1 ≤ j → (c.work stT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.wfCells hS_hold).2
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.wfCells hinv.desc).2
  have hoth_d : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS
      exact SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
    · exact hinv.others_read i hiS hiD
  -- Phase hc0: scan past field 1
  obtain ⟨c₁, hr₁, hst₁, hwtD₁, hin₁, hout₁, hoth₁⟩ :=
    scanRight_loop (cur := hc0) (next := hc1) (t := dsT)
      (fun hcon => nomatch hcon) arm_hc0
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c hst rfl hinv.desc_head hinv.inp_read hinv.out_read
      (fun i hi => hoth_d i hi)
  have hstS₁ : c₁.work stT = c.work stT := hoth₁ stT (by decide)
  -- state and desc cell values in blank-default form
  have hScell : ∀ j, (c.work stT).cells (1 + j)
      = (((bitsToSyms (Nat.toBits (decodeDesc α).w mc.state.val))[j]?).getD
          Γw.blank).toΓ := by
    intro j
    rw [show 1 + j = j + 1 by omega]
    exact holdsExact_cells_getD hS_hold j
  have hWcell : ∀ j, j ≤ (qhaltField (groupPairs α)).length →
      (c.work dsT).cells ((takeField (groupPairs α)).1.length + 2 + j)
        = (((qhaltField (groupPairs α))[j]?).getD Γw.blank).toΓ :=
    fun j hj => descLayout_field2_getD hinv.desc j hj
  -- Phase hc1: lockstep compare, first mismatch at offset n
  obtain ⟨c₂, hr₂, hst₂, hwtS₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    hc1_mismatch_loop (c.work stT).cells (c.work dsT).cells hS_wns hW_wns
      n 1 ((takeField (groupPairs α)).1.length + 2) (by omega) (by omega)
      (fun j hj => by
        obtain ⟨hje, hjb⟩ := hagree j hj
        constructor
        · rw [hScell j, hWcell j (by omega)]
          exact congrArg Γw.toΓ hje
        · rw [hScell j]
          intro hcon
          exact hjb (Γw.toΓ_eq_blank.mp hcon))
      (by
        rw [hScell n, hWcell n hnB']
        rintro ⟨h1, h2⟩
        exact hmm ((Γw.toΓ_eq_blank.mp h1).trans (Γw.toΓ_eq_blank.mp h2).symm))
      (by
        rw [hScell n, hWcell n hnB']
        rintro ⟨-, -, h3⟩
        exact hmm (Γw.toΓ_inj h3))
      c₁ hst₁
      (by rw [hstS₁]) (by rw [hstS₁, hinv.state_head])
      (by rw [hwtD₁]) (by rw [hwtD₁]; dsimp only; omega)
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hiS hiD => by rw [hoth₁ i hiD]; exact hoth_d i hiD)
  -- Phase preRewS: rewind the state head
  obtain ⟨c₃, hr₃, hst₃, hwtS₃, hin₃, hout₃, hoth₃⟩ :=
    rewStep_loop (cur := preRewS) (next := preRewD) (t := stT)
      (fun hcon => nomatch hcon) arm_preRewS
      (c.work stT).cells hS_hold.1 hS_wns
      (1 + n) c₂ hst₂
      (by rw [hwtS₂]) (by rw [hwtS₂])
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiD : i = dsT
        · subst hiD
          rw [hwtD₂]
          exact hW_wns ((takeField (groupPairs α)).1.length + 2 + n) (by omega)
        · rw [hoth₂ i hi hiD, hoth₁ i hiD]
          exact hoth_d i hiD)
  -- Phase preRewD: rewind the desc head
  obtain ⟨c₄, hr₄, hst₄, hwtD₄, hin₄, hout₄, hoth₄⟩ :=
    rewStep_loop (cur := preRewD) (next := peek1) (t := dsT)
      (fun hcon => nomatch hcon) arm_preRewD
      (c.work dsT).cells hinv.desc.1 hW_wns
      ((takeField (groupPairs α)).1.length + 2 + n) c₃ hst₃
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hoth₃ dsT (by decide), hwtD₂])
      (by rw [hin₃, hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₃, hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by
        by_cases hiS : i = stT
        · subst hiS
          rw [hwtS₃]
          exact hS_wns 1 (by omega)
        · rw [hoth₃ i hiS, hoth₂ i hiS hi, hoth₁ i hi]
          exact hoth_d i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₄,
    ((takeField (groupPairs α)).1.length + 1) + (n + 1) + ((1 + n) + 1)
      + (((takeField (groupPairs α)).1.length + 2 + n) + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃) hr₄,
    hst₄, by rw [hin₄, hin₃, hin₂, hin₁], ?_,
    by rw [hout₄, hout₃, hout₂, hout₁]⟩
  intro i
  by_cases hiS : i = stT
  · subst hiS
    rw [hoth₄ stT (by decide), hwtS₃]
    exact tape_mk_eq hinv.state_head
  · by_cases hiD : i = dsT
    · subst hiD
      rw [hwtD₄]
      exact tape_mk_eq hinv.desc_head
    · rw [hoth₄ i hiD, hoth₃ i hiS, hoth₂ i hiS hiD, hoth₁ i hiD]

/-- **Peek and seek phases**: from `peek1`, capture the (honest) at-origin
    flags and walk the desc head to the start of the entry region
    (`|F1| + |F2| + 3`), all other tapes exactly restored, within
    `2·|groupPairs α| + 4` steps. -/
theorem peekSeekPhase (c : Cfg 6 bodyTM.Q)
    (hst : c.state = peek1)
    (hinv : SimInv α mc c.input c.work c.output) :
    ∃ c' t, t ≤ 2 * (groupPairs α).length + 4 ∧
      bodyTM.reachesIn t c c' ∧
      c'.state = cmpQ (decide (mc.input.head = 0), decide ((mc.work 0).head = 0),
        decide (mc.output.head = 0)) ∧
      (∀ i, i ≠ dsT → c'.work i = c.work i) ∧
      c'.work dsT = ⟨(takeField (groupPairs α)).1.length
        + (qhaltField (groupPairs α)).length + 3, (c.work dsT).cells⟩ ∧
      c'.input = c.input ∧ c'.output = c.output := by
  obtain ⟨S, hS_hold, hS_nb, hS_which⟩ := hinv.state_syms_ne_blank
  have hst_read : (c.work stT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hS_hold (by rw [hinv.state_head])
  have hds_read : (c.work dsT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hinv.desc (by rw [hinv.desc_head])
  have hsc_read : (c.work scT).read ≠ Γ.start :=
    SimInv.read_ne_start_of_holdsExact hinv.scratch (by rw [hinv.scratch_head])
  have hW_wns : ∀ j, 1 ≤ j → (c.work dsT).cells j ≠ Γ.start :=
    (Tape.HoldsExact.wfCells hinv.desc).2
  -- peek: two steps, all tapes restored
  obtain ⟨c₁, hr₁, hst₁, hv0₁, hv1₁, hv2₁, hstT₁, hdsT₁, hscT₁, hin₁, hout₁⟩ :=
    peek_correct hinv.vin hinv.vwk hinv.vout hinv.wf_in hinv.wf_wk hinv.wf_out
      hst hst_read hds_read hsc_read hinv.inp_read hinv.out_read
  have hoth_d₁ : ∀ i, i ≠ dsT → c₁.work i = c.work i := by
    intro i hiD
    rcases i with ⟨iv, hv⟩
    rcases iv with _ | _ | _ | _ | _ | _ | m
    · exact hv0₁
    · exact hv1₁
    · exact hv2₁
    · exact hstT₁
    · exact absurd rfl hiD
    · exact hscT₁
    · exact absurd hv (by omega)
  have hoth_read : ∀ i, i ≠ dsT → (c.work i).read ≠ Γ.start := by
    intro i hiD
    by_cases hiS : i = stT
    · subst hiS; exact hst_read
    · exact hinv.others_read i hiS hiD
  -- seek1: past the first separator
  obtain ⟨c₂, hr₂, hst₂, hwtD₂, hin₂, hout₂, hoth₂⟩ :=
    scanRight_loop (cur := seek1 _) (next := seek2 _) (t := dsT)
      (fun hcon => nomatch hcon) (arm_seek1 · · · _)
      (c.work dsT).cells hW_wns
      (takeField (groupPairs α)).1.length 1 (by omega)
      (fun j hj => descLayout_field1 hinv.desc j hj)
      (descLayout_sep1 hinv.desc)
      c₁ hst₁ (by rw [hdsT₁]) (by rw [hdsT₁, hinv.desc_head])
      (by rw [hin₁]; exact hinv.inp_read) (by rw [hout₁]; exact hinv.out_read)
      (fun i hi => by rw [hoth_d₁ i hi]; exact hoth_read i hi)
  -- seek2: past the second separator
  obtain ⟨c₃, hr₃, hst₃, hwtD₃, hin₃, hout₃, hoth₃⟩ :=
    scanRight_loop (cur := seek2 _) (next := cmpQ _) (t := dsT)
      (fun hcon => nomatch hcon) (arm_seek2 · · · _)
      (c.work dsT).cells hW_wns
      (qhaltField (groupPairs α)).length
      ((takeField (groupPairs α)).1.length + 2) (by omega)
      (fun j hj => descLayout_field2 hinv.desc j hj)
      (descLayout_sep2 hinv.desc)
      c₂ hst₂ (by rw [hwtD₂]) (by rw [hwtD₂]; dsimp only; omega)
      (by rw [hin₂, hin₁]; exact hinv.inp_read)
      (by rw [hout₂, hout₁]; exact hinv.out_read)
      (fun i hi => by rw [hoth₂ i hi, hoth_d₁ i hi]; exact hoth_read i hi)
  have hF1 := takeField_fst_length_le (groupPairs α)
  have hqh := qhaltField_length_le (groupPairs α)
  refine ⟨c₃, 2 + ((takeField (groupPairs α)).1.length + 1)
      + ((qhaltField (groupPairs α)).length + 1),
    by omega,
    reachesIn_trans _ (reachesIn_trans _ hr₁ hr₂) hr₃,
    hst₃,
    (fun i hi => by rw [hoth₃ i hi, hoth₂ i hi, hoth_d₁ i hi]),
    (by rw [hwtD₃]
        exact congrArg (fun m => (⟨m, (c.work dsT).cells⟩ : Tape)) (by omega)),
    by rw [hin₃, hin₂, hin₁], by rw [hout₃, hout₂, hout₁]⟩

end HcPhase

end TM.UTMBody
