import Complexitylib.Classes.P.Defs
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Internal
import Mathlib.Analysis.Asymptotics.Defs

/-!
# P closure properties — proof internals

This file contains the proofs behind `DTIME_union` (DTIME closed under union).
The key simulation theorem `unionTM_decidesInTime` establishes that the
composite machine from `TM.unionTM` correctly decides `L₁ ∪ L₂`.
-/

open Complexity Asymptotics Filter

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Auxiliary lemma: DecidesInTime implies qstart ≠ qhalt
-- ════════════════════════════════════════════════════════════════════════

/-- A TM that decides a language must have distinct start and halt states.
    If `qstart = qhalt`, the machine halts at step 0 with output `□`,
    which equals neither `Γ.one` nor `Γ.zero`. -/
private theorem qstart_ne_qhalt_of_decidesInTime {tm : TM n₁}
    {L : Language} {f : ℕ → ℕ} (h : tm.DecidesInTime L f) :
    tm.qstart ≠ tm.qhalt := by
  intro heq
  -- Pick any input, e.g., []
  obtain ⟨c', t, _, hreach, hhalt, hmem, hnmem⟩ := h []
  -- Since qstart = qhalt, initCfg is halted, so reachesIn can only give t=0, c'=initCfg
  have hhalted_init : (tm.initCfg []).state = tm.qhalt := by
    simp [initCfg, heq]
  -- step returns none for halted configs, so reachesIn must be zero
  have : c' = tm.initCfg [] ∧ t = 0 := by
    cases hreach with
    | zero => exact ⟨rfl, rfl⟩
    | step hstep _ =>
      simp [step, hhalted_init] at hstep
  obtain ⟨rfl, _⟩ := this
  -- output cell 1 of initCfg is blank
  have hblank : (tm.initCfg []).output.cells 1 = Γ.blank := by
    simp [initCfg, initTape]
  -- But DecidesInTime requires it to be either one or zero
  by_cases hx : ([] : List Bool) ∈ L
  · have := hmem hx; rw [hblank] at this; exact absurd this (by decide)
  · have := hnmem hx; rw [hblank] at this; exact absurd this (by decide)

-- ════════════════════════════════════════════════════════════════════════
-- Core simulation theorem
-- ════════════════════════════════════════════════════════════════════════

/-- The union TM correctly decides `L₁ ∪ L₂` with time bound `10·f₁ + f₂`.

    The factor 10 arises from Phase 1 (f₁ steps), transition (≤ 2·f₁ + 7 steps
    absorbed into 9·f₁ since f₁ ≥ 1), and Phase 2 (f₂ steps). -/
theorem unionTM_decidesInTime {tm₁ : TM n₁} {tm₂ : TM n₂}
    {L₁ L₂ : Language} {f₁ f₂ : ℕ → ℕ}
    (h₁ : tm₁.DecidesInTime L₁ f₁) (h₂ : tm₂.DecidesInTime L₂ f₂) :
    (unionTM tm₁ tm₂).DecidesInTime (L₁ ∪ L₂) (fun n => 10 * f₁ n + f₂ n) := by
  have hne₁ := qstart_ne_qhalt_of_decidesInTime h₁
  have hne₂ := qstart_ne_qhalt_of_decidesInTime h₂
  intro x
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hmem₁, hnmem₁⟩ := h₁ x
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hmem₂, hnmem₂⟩ := h₂ x
  -- t₁ ≥ 1 since qstart ≠ qhalt (halting at step 0 means qstart = qhalt)
  have ht₁_pos : t₁ ≥ 1 := by
    rcases t₁ with _ | t₁
    · cases hreach₁; simp [halted, initCfg] at hhalt₁; exact absurd hhalt₁ hne₁
    · omega
  have ht₂_pos : t₂ ≥ 1 := by
    rcases t₂ with _ | t₂
    · cases hreach₂; simp [halted, initCfg] at hhalt₂; exact absurd hhalt₂ hne₂
    · omega
  -- Head bounds: tape heads are ≤ t₁ after Phase 1
  have hbounds := head_bound_of_reachesIn tm₁ hreach₁
  -- Phase 1: union machine simulates tm₁ for t₁ steps
  have hphase1 := phase1_simulation tm₁ tm₂ x hreach₁ ht₁_pos
  -- Case split on whether tm₁ accepted
  by_cases hx₁ : x ∈ L₁
  · -- tm₁ accepted: output cell 1 = Γ.one
    have hcell := hmem₁ hx₁
    -- Derive output tape invariants from reachesIn
    have hcell0_out := output_cell0_of_reachesIn hreach₁ (initTape_cell0 _)
    have hnostart_out := output_noStart_of_reachesIn hreach₁
      (fun i hi => initTape_nil_noStart hi)
    -- Transition: rewind fake output, check, write Γ.one to real output, halt
    obtain ⟨t_tr, c_final, htrans, hhalt_f, hout_f, htr_bound⟩ :=
      transition_accept tm₁ tm₂ hhalt₁ hcell hcell0_out hnostart_out
    -- Combine Phase 1 + transition
    have hoh := hbounds.2.1  -- c₁.output.head ≤ t₁
    refine ⟨c_final, t₁ + t_tr, ?_, reachesIn_trans _ hphase1 htrans, hhalt_f, ?_, ?_⟩
    · show t₁ + t_tr ≤ 10 * f₁ x.length + f₂ x.length; omega
    · intro _; exact hout_f
    · intro hx; exfalso; exact hx (Or.inl hx₁)
  · -- tm₁ rejected: output cell 1 = Γ.zero
    have hcell := hnmem₁ hx₁
    -- Derive output tape and input tape invariants from reachesIn
    have hcell0_out := output_cell0_of_reachesIn hreach₁ (initTape_cell0 _)
    have hnostart_out := output_noStart_of_reachesIn hreach₁
      (fun i hi => initTape_nil_noStart hi)
    have hinput_cells := input_cells_of_reachesIn hreach₁
    -- Transition: full transition to Phase 2
    obtain ⟨t_tr, c_mid, htrans, hmid_state, hmid_input, hmid_work, hmid_output, htr_bound⟩ :=
      transition_reject tm₁ tm₂ x hhalt₁ hcell hcell0_out hnostart_out hinput_cells
    -- Phase 2: union machine simulates tm₂ for t₂ steps
    obtain ⟨c_end, hphase2, hend_state, hend_output⟩ :=
      phase2_simulation tm₁ tm₂ x hreach₂ hmid_state hmid_input hmid_work hmid_output
    -- Combine Phase 1 + transition + Phase 2
    have hfull := reachesIn_trans _ (reachesIn_trans _ hphase1 htrans) hphase2
    -- The final config is halted
    have hfinal_halted : (unionTM tm₁ tm₂).halted c_end := by
      show c_end.state = Sum.inr (Sum.inr tm₂.qhalt)
      rw [hend_state, hhalt₂]
    have hih := hbounds.1    -- c₁.input.head ≤ t₁
    have hoh := hbounds.2.1  -- c₁.output.head ≤ t₁
    refine ⟨c_end, t₁ + t_tr + t₂, ?_, hfull, hfinal_halted, ?_, ?_⟩
    · show t₁ + t_tr + t₂ ≤ 10 * f₁ x.length + f₂ x.length; omega
    · intro hx; rw [hend_output]; cases hx with
      | inl h => exact absurd h hx₁
      | inr h => exact hmem₂ h
    · intro hx; rw [hend_output]
      have : x ∉ L₂ := fun h => hx (Set.mem_union_right _ h)
      exact hnmem₂ this

end TM

-- ════════════════════════════════════════════════════════════════════════
-- BigO arithmetic: 8·f₁ + f₂ =O (T₁ + T₂)
-- ════════════════════════════════════════════════════════════════════════

/-- If `f₁ =O T₁` and `f₂ =O T₂`, then `10·f₁ + f₂ =O (T₁ + T₂)`. -/
private theorem bigO_union_bound {f₁ f₂ T₁ T₂ : ℕ → ℕ}
    (ho₁ : f₁ =O T₁) (ho₂ : f₂ =O T₂) :
    (fun n => 10 * f₁ n + f₂ n) =O (fun n => T₁ n + T₂ n) := by
  -- Unfold our BigO to Mathlib's IsBigO
  show (fun n => ((10 * f₁ n + f₂ n : ℕ) : ℝ)) =O[atTop]
       (fun n => ((T₁ n + T₂ n : ℕ) : ℝ))
  -- Cast to ℝ and decompose
  have h1 : (fun n => ((f₁ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₁ n : ℕ) : ℝ)) := ho₁
  have h2 : (fun n => ((f₂ n : ℕ) : ℝ)) =O[atTop] (fun n => ((T₂ n : ℕ) : ℝ)) := ho₂
  -- T₁ =O (T₁ + T₂) since T₁ ≤ T₁ + T₂
  have hT₁_le : (fun n => ((T₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    simp only [Nat.cast_add, one_mul, Real.norm_natCast]
    exact le_of_le_of_eq (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) (T₂ n)))
      (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm
  -- T₂ =O (T₁ + T₂) since T₂ ≤ T₁ + T₂
  have hT₂_le : (fun n => ((T₂ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    simp only [Nat.cast_add, one_mul, Real.norm_natCast]
    exact le_of_le_of_eq (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) (T₁ n)))
      (abs_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).symm
  -- f₁ =O (T₁ + T₂) by transitivity
  have hf₁ : (fun n => ((f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := h1.trans hT₁_le
  -- 10 * f₁ =O (T₁ + T₂) by constant factor
  have h7f₁ : (fun n => ((10 * f₁ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := by
    have : (fun n => (10 : ℝ) * ((f₁ n : ℕ) : ℝ)) =O[atTop]
        (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) :=
      hf₁.const_mul_left 10
    convert this using 1
    ext n; push_cast; ring
  -- f₂ =O (T₁ + T₂) by transitivity
  have hf₂ : (fun n => ((f₂ n : ℕ) : ℝ)) =O[atTop]
      (fun n => ((T₁ n + T₂ n : ℕ) : ℝ)) := h2.trans hT₂_le
  -- 10 * f₁ + f₂ =O (T₁ + T₂) by sum
  have := h7f₁.add hf₂
  convert this using 1
  ext n; push_cast; ring

-- ════════════════════════════════════════════════════════════════════════
-- DTIME_union
-- ════════════════════════════════════════════════════════════════════════

/-- **DTIME is closed under union** (AB Claim 1.5): if `L₁ ∈ DTIME(T₁)` and
    `L₂ ∈ DTIME(T₂)`, then `L₁ ∪ L₂ ∈ DTIME(T₁ + T₂)`. -/
theorem DTIME_union {T₁ T₂ : ℕ → ℕ} {L₁ L₂ : Language}
    (h₁ : L₁ ∈ DTIME T₁) (h₂ : L₂ ∈ DTIME T₂) :
    L₁ ∪ L₂ ∈ DTIME (fun n => T₁ n + T₂ n) := by
  obtain ⟨k₁, tm₁, f₁, hd₁, ho₁⟩ := h₁
  obtain ⟨k₂, tm₂, f₂, hd₂, ho₂⟩ := h₂
  exact ⟨k₁ + 1 + k₂, TM.unionTM tm₁ tm₂, fun n => 10 * f₁ n + f₂ n,
    TM.unionTM_decidesInTime hd₁ hd₂,
    bigO_union_bound ho₁ ho₂⟩
