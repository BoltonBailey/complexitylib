import Complexitylib.Models.TuringMachine
import Mathlib.Data.Finset.Lattice.Fold

/-!
# TM–NTM embedding: proof internals

Helper lemmas for `TM.toNTM_accepts_iff`, showing that the DTM step function
and the NTM trace on `toNTM` compute the same thing.
-/

variable {n : ℕ}

private lemma TM.toNTM_trace_step (tm : TM n) {c : Cfg n tm.Q}
    (T : ℕ) (choices : Fin (T + 1) → Bool) (hne : c.state ≠ tm.qhalt) :
    tm.toNTM.trace (T + 1) choices c =
    tm.toNTM.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
      ((tm.step c).get (by simp [TM.step, hne])) := by
  simp [NTM.trace, hne, TM.toNTM, TM.step]

private lemma TM.reaches_toNTM_trace (tm : TM n) {a c' : Cfg n tm.Q}
    (hreach : tm.reaches a c') :
    ∃ T, ∀ (ch : Fin T → Bool), tm.toNTM.trace T ch a = c' := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => rfl⟩
  | @head a₀ b₀ hstep _ ih =>
    obtain ⟨T, hT⟩ := ih
    have hne : a₀.state ≠ tm.qhalt := by
      rw [TM.stepRel] at hstep; exact ne_qhalt_of_step hstep
    refine ⟨T + 1, fun ch => ?_⟩
    rw [tm.toNTM_trace_step T ch hne]
    have : (tm.step a₀).get (by simp [TM.step, hne]) = b₀ := by
      simp [TM.stepRel] at hstep; simp [hstep]
    rw [this]; exact hT _

lemma TM.toNTM_trace_reaches (tm : TM n) (c : Cfg n tm.Q)
    (T : ℕ) (choices : Fin T → Bool) :
    tm.reaches c (tm.toNTM.trace T choices c) := by
  induction T generalizing c with
  | zero => exact Relation.ReflTransGen.refl
  | succ T ih =>
    simp only [NTM.trace]
    split
    · exact Relation.ReflTransGen.refl
    · next hne =>
      have hne : c.state ≠ tm.qhalt := hne
      exact Relation.ReflTransGen.head
        (show tm.stepRel c _ by simp [TM.stepRel, TM.step, hne, TM.toNTM])
        (ih _ _)

/-- For `toNTM`, the trace is independent of the choice sequence since both
    transition functions are identical. -/
lemma TM.toNTM_trace_choice_irrel (tm : TM n) (T : ℕ) (c : Cfg n tm.Q)
    (ch₁ ch₂ : Fin T → Bool) :
    tm.toNTM.trace T ch₁ c = tm.toNTM.trace T ch₂ c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    simp only [NTM.trace]
    split
    · rfl
    · simp only [TM.toNTM]; exact ih _ _ _

/-- If a DTM reaches `c'` in exactly `t` steps, then `toNTM.trace t` agrees. -/
private lemma TM.toNTM_reachesIn_trace (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') (ch : Fin t → Bool) :
    tm.toNTM.trace t ch c = c' := by
  induction h with
  | zero => rfl
  | @step c₀ c_mid _ _ hstep _ ih =>
    have hne := ne_qhalt_of_step hstep
    rw [tm.toNTM_trace_step _ ch hne]
    have : (tm.step c₀).get (by simp [TM.step, hne]) = c_mid := by
      simp [TM.step, hne] at hstep ⊢; exact hstep
    rw [this]; exact ih _

/-- If a DTM halts within `t ≤ T` steps, then `toNTM.trace T` reaches the same
    halted configuration regardless of choices. -/
lemma TM.toNTM_trace_of_reachesIn (tm : TM n) {c c' : Cfg n tm.Q}
    {t T : ℕ} (h : tm.reachesIn t c c') (hhalt : tm.halted c')
    (hle : t ≤ T) (ch : Fin T → Bool) :
    tm.toNTM.trace T ch c = c' := by
  induction T generalizing c t with
  | zero =>
    have : t = 0 := by omega
    subst this; cases h; rfl
  | succ T ih =>
    by_cases hh : c.state = tm.qhalt
    · -- c is halted → t = 0 → c = c'
      have : t = 0 := by
        by_contra hp; obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
        cases h with | step hs _ => simp [TM.step, hh] at hs
      subst this; cases h; simp [NTM.trace, TM.toNTM, hh]
    · -- c not halted → t > 0 → peel one step
      have ht_pos : t ≠ 0 := by
        intro h0; subst h0; cases h; exact hh hhalt
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_pos
      obtain ⟨c_mid, hstep, hrest⟩ : ∃ c_mid, tm.step c = some c_mid ∧ tm.reachesIn t' c_mid c' := by
        cases h with | step hs hr => exact ⟨_, hs, hr⟩
      rw [tm.toNTM_trace_step T ch hh]
      have : (tm.step c).get (by simp [TM.step, hh]) = c_mid := by
        simp [hstep]
      rw [this]
      exact ih hrest (by omega) _

/-- The DTM and its NTM embedding agree on acceptance. -/
theorem TM.toNTM_accepts_iff (tm : TM n) (x : List Bool) :
    tm.Accepts x ↔ (tm.toNTM).Accepts x := by
  constructor
  · rintro ⟨c', hreach, hhalt, hout⟩
    obtain ⟨T, hT⟩ := tm.reaches_toNTM_trace hreach
    exact ⟨T, fun _ => false,
      by change (tm.toNTM.trace T _ (tm.initCfg x)).state = _; rw [hT]; exact hhalt,
      by change (tm.toNTM.trace T _ (tm.initCfg x)).output.cells 1 = _; rw [hT]; exact hout⟩
  · rintro ⟨T, choices, hhalt, hout⟩
    exact ⟨_, tm.toNTM_trace_reaches _ T choices, hhalt, hout⟩

/-- If a DTM decides `L` in time `f`, then its NTM embedding also decides `L`
    in time `f`. This is the key internal lemma for `DTIME ⊆ NTIME`. -/
theorem TM.toNTM_decidesInTime (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (h : tm.DecidesInTime L f) : tm.toNTM.DecidesInTime L f := by
  refine ⟨?_, ?_⟩
  · -- AllPathsHaltIn
    intro x choices
    obtain ⟨c', t, hle, hreach, hhalt, _, _⟩ := h x
    have htrace := tm.toNTM_trace_of_reachesIn hreach hhalt hle choices
    change (tm.toNTM.trace _ choices (tm.initCfg x)).state = tm.qhalt
    rw [htrace]; exact hhalt
  · -- x ∈ L ↔ AcceptsInTime
    intro x; constructor
    · -- x ∈ L → AcceptsInTime
      intro hx
      obtain ⟨c', t, hle, hreach, hhalt, hyes, _⟩ := h x
      refine ⟨fun _ => false, ?_, ?_⟩
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).state = _
        rw [tm.toNTM_trace_of_reachesIn hreach hhalt hle]; exact hhalt
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).output.cells 1 = _
        rw [tm.toNTM_trace_of_reachesIn hreach hhalt hle]; exact hyes hx
    · -- AcceptsInTime → x ∈ L
      intro ⟨choices, hhalt_ch, hout_ch⟩
      obtain ⟨c', t, hle, hreach, hhalt, _, hno⟩ := h x
      by_contra hxL
      have htrace := tm.toNTM_trace_of_reachesIn hreach hhalt hle choices
      change (tm.toNTM.trace _ choices (tm.initCfg x)).output.cells 1 = _ at hout_ch
      rw [htrace] at hout_ch
      have := hno hxL
      simp_all

/-- `write` does not change the head position. -/
private lemma Tape.head_write (t : Tape) (s : Γ) : (t.write s).head = t.head := by
  simp [Tape.write]; split <;> rfl

/-- Tape head changes by at most 1 per `move` operation. -/
private lemma Tape.head_move_le (t : Tape) (d : Dir3) :
    (t.move d).head ≤ t.head + 1 := by
  cases d <;> simp [Tape.move]; try omega

/-- `writeAndMove` changes head by at most 1. -/
private lemma Tape.head_writeAndMove_le (t : Tape) (s : Γ) (d : Dir3) :
    (t.writeAndMove s d).head ≤ t.head + 1 := by
  unfold Tape.writeAndMove
  have h1 := Tape.head_move_le (t.write s) d
  rw [Tape.head_write] at h1; exact h1

/-- Work tape heads grow by at most 1 per step. -/
private lemma TM.work_head_step_bound (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.step c = some c') (i : Fin n) :
    (c'.work i).head ≤ (c.work i).head + 1 := by
  simp only [TM.step] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact Tape.head_writeAndMove_le _ _ _

/-- After `t` steps, each work tape head is at most `t` plus its initial value. -/
theorem TM.work_head_reachesIn_bound (tm : TM n) {c c' : Cfg n tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') (i : Fin n) :
    (c'.work i).head ≤ (c.work i).head + t := by
  induction h with
  | zero => omega
  | @step c₀ c_mid _ _ hstep _ ih =>
    have := tm.work_head_step_bound hstep i
    omega

/-- Convert `reaches` to `reachesIn`. -/
theorem TM.reaches_to_reachesIn (tm : TM n) {c c' : Cfg n tm.Q}
    (h : tm.reaches c c') : ∃ t, tm.reachesIn t c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero⟩
  | head hstep _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + 1, .step hstep ht⟩

/-- A DTM step is deterministic: `step` is a function. -/
private lemma TM.step_det (tm : TM n) {c c₁ c₂ : Cfg n tm.Q}
    (h₁ : tm.step c = some c₁) (h₂ : tm.step c = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- If a DTM halts at step `t_halt`, then any `reachesIn t` has `t ≤ t_halt`. -/
theorem TM.reachesIn_le_halt (tm : TM n) {c c' c_halt : Cfg n tm.Q}
    {t t_halt : ℕ} (hr : tm.reachesIn t c c')
    (hh : tm.reachesIn t_halt c c_halt) (hhalt : tm.halted c_halt) :
    t ≤ t_halt := by
  induction t generalizing c t_halt with
  | zero => omega
  | succ t ih =>
    cases hr with | @step c₀ c_mid _ _ hs hr' =>
    cases t_halt with
    | zero =>
      cases hh
      simp [TM.step, hhalt] at hs
    | succ t_halt' =>
      cases hh with | step hs' hh' =>
      have := tm.step_det hs hs'
      subst this
      exact Nat.succ_le_succ (ih hr' hh')

/-- Initial work tape heads are all at position 0. -/
lemma TM.initCfg_work_head_zero (tm : TM n) (x : List Bool) (i : Fin n) :
    ((tm.initCfg x).work i).head = 0 := by
  simp [initTape]

/-- If a DTM is a transducer, so is its NTM embedding. -/
theorem TM.toNTM_isTransducer (tm : TM n) (h : tm.IsTransducer) : tm.toNTM.IsTransducer := by
  intro b q iHead wHeads oHead
  simp only [TM.toNTM]
  exact h q iHead wHeads oHead

/-- If a DTM decides `L` in space `f`, then its NTM embedding also decides `L`
    in space `f`. The uniform time bound is constructed as the maximum halting
    time over all inputs of each length. -/
theorem TM.toNTM_decidesInSpace (tm : TM n) {L : Language} {f : ℕ → ℕ}
    (h : tm.DecidesInSpace L f) : tm.toNTM.DecidesInSpace L f := by
  -- Extract per-input halting times
  have hdata : ∀ x, ∃ t c', tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero) := by
    intro x
    obtain ⟨c', hreach, hhalt, hyes, hno⟩ := h.2 x
    obtain ⟨t, hreachIn⟩ := tm.reaches_to_reachesIn hreach
    exact ⟨t, c', hreachIn, hhalt, hyes, hno⟩
  choose t_fn c_fn hreachIn hhalt hyes hno using hdata
  -- Uniform time bound: max halting time over all inputs of each length
  let T : ℕ → ℕ := fun m =>
    Finset.sup (Finset.univ : Finset (Fin m → Bool)) (fun v => t_fn (List.ofFn v))
  have hle_T : ∀ x, t_fn x ≤ T x.length := by
    intro x
    show t_fn x ≤ Finset.sup Finset.univ (fun v => t_fn (List.ofFn v))
    conv_lhs => rw [show x = List.ofFn (fun i : Fin x.length => x[↑i]) from
      (List.ofFn_getElem (l := x)).symm]
    exact Finset.le_sup (f := fun v => t_fn (List.ofFn v))
      (Finset.mem_univ (fun i : Fin x.length => x[↑i]))
  refine ⟨T, ⟨?_, ?_⟩, ?_⟩
  · -- AllPathsHaltIn
    intro x choices
    have htrace := tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x) choices
    change (tm.toNTM.trace _ choices (tm.initCfg x)).state = tm.qhalt
    rw [htrace]; exact hhalt x
  · -- x ∈ L ↔ AcceptsInTime
    intro x; constructor
    · intro hx
      refine ⟨fun _ => false, ?_, ?_⟩
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).state = tm.qhalt
        rw [tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x)]
        exact hhalt x
      · change (tm.toNTM.trace _ _ (tm.initCfg x)).output.cells 1 = Γ.one
        rw [tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x)]
        exact hyes x hx
    · intro ⟨choices, hhalt_ch, hout_ch⟩
      by_contra hxL
      have htrace := tm.toNTM_trace_of_reachesIn (hreachIn x) (hhalt x) (hle_T x) choices
      change (tm.toNTM.trace _ choices (tm.initCfg x)).output.cells 1 = _ at hout_ch
      rw [htrace] at hout_ch
      have := hno x hxL
      simp_all
  · -- Space bound
    intro x choices t' ht' i
    have hreach := tm.toNTM_trace_reaches (tm.initCfg x) t'
      (fun j : Fin t' => choices ⟨j.val, by omega⟩)
    exact h.1 x _ hreach i
