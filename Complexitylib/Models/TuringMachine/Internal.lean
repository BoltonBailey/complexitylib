import Complexitylib.Models.TuringMachine

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
      intro heq; simp [TM.stepRel, TM.step, heq] at hstep
    refine ⟨T + 1, fun ch => ?_⟩
    rw [tm.toNTM_trace_step T ch hne]
    have : (tm.step a₀).get (by simp [TM.step, hne]) = b₀ := by
      simp [TM.stepRel] at hstep; simp [hstep]
    rw [this]; exact hT _

private lemma TM.toNTM_trace_reaches (tm : TM n) (c : Cfg n tm.Q)
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
