/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Randomized
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.Internal.PolyWindow
public import Complexitylib.Classes.Containments.Internal.PPParts
public import Complexitylib.Classes.Containments.Internal.PPTest
public import Complexitylib.Classes.Containments.Internal.PPBody
public import Complexitylib.Classes.Containments.Internal.PPSim
public import Complexitylib.Models.TuringMachine.Subroutines.ParkRewind
public import Complexitylib.Models.TuringMachine.Subroutines.WipeRewind
public import Complexitylib.Classes.Containments.Internal.PPLayout
public import Complexitylib.Classes.Containments.Internal.PPAssemble

/-!
# `PP ⊆ PSPACE` — removing the rational threshold

⚠️ Unreviewed by Bolton

Membership in `PP` is stated as `acceptProb > 1/2`, a comparison of rationals. A machine has no
rationals; it has a counter. Since `acceptProb x T` is `acceptCount x T / 2 ^ T` by definition,
the threshold is equivalent to the integer comparison `2 ^ T < 2 · acceptCount x T`, and both
sides of that are things a machine can hold: the count needs `T + 1` bits and the choice
sequences it ranges over are `T` bits each.

What remains for the containment is the enumeration itself — a counter over the `2 ^ T` choice
sequences, one simulation per sequence, and a running tally — with the space reused between
sequences.

## Main results

- `NTM.acceptProb_gt_half_iff` — the threshold as an integer comparison
- `PP_integer_characterization_internal` — `PP` with no rational arithmetic left in it
- `PP_subset_PSPACE_of_counter_internal` — the containment, modulo one machine
- `PP_subset_PSPACE_of_tallyMachine_internal` — the same, with the obligation reduced to a
  machine deciding one arithmetic predicate
- `PP_subset_PSPACE_of_iterateMachine_internal` — and reduced further, to realising one iterated
  step function
- `PP_subset_PSPACE_internal` — the containment itself
-/

@[expose] public section

namespace Complexity

namespace NTM

/-- **The `PP` threshold is an integer comparison.** More than half of the `2 ^ T` choice
sequences accept exactly when twice the accepting count exceeds `2 ^ T`. -/
theorem acceptProb_gt_half_iff {k : ℕ} (tm : NTM k) (x : List Bool) (T : ℕ) :
    tm.acceptProb x T > 1 / 2 ↔ 2 ^ T < 2 * tm.acceptCount x T := by
  have hpos : (0 : ℚ) < 2 ^ T := by positivity
  rw [NTM.acceptProb, gt_iff_lt, div_lt_div_iff₀ (by norm_num) hpos]
  constructor
  · intro h
    have : ((2 ^ T : ℕ) : ℚ) < ((2 * tm.acceptCount x T : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((2 ^ T : ℕ) : ℚ) < ((2 * tm.acceptCount x T : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this
    linarith

end NTM

/-- **`PP` with no rational arithmetic left.** A language of `PP` is decided by comparing twice
the number of accepting choice sequences against their total count — a comparison of two
naturals of polynomially many bits. -/
theorem PP_integer_characterization_internal {L : Language} (hL : L ∈ PP) :
    ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ) (m : ℕ),
      tm.AllPathsHaltIn f ∧ f =O (· ^ m) ∧
      ∀ x : List Bool, x ∈ L ↔
        2 ^ f x.length < 2 * tm.acceptCount x (f x.length) := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, f, hhalt, hacc, hf⟩ := hm
  exact ⟨k, tm, f, m, hhalt, hf,
    fun x => (hacc x).trans (NTM.acceptProb_gt_half_iff tm x (f x.length))⟩


/-- **`PP ⊆ PSPACE`, reduced to the existence of one machine.** For each probabilistic machine
and time bound, exhibit a deterministic machine that keeps a polynomial window and decides the
integer comparison `2 ^ T < 2 · acceptCount` — the rational threshold having already been
eliminated. No probability, and no asymptotics, survive in the obligation. -/
theorem PP_subset_PSPACE_of_counter_internal
    (h : ∀ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ), tm.AllPathsHaltIn f → (∃ m, f =O (· ^ m)) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          (2 ^ f x.length < 2 * tm.acceptCount x (f x.length) →
            c'.output.cells 1 = Γ.one) ∧
          (¬ (2 ^ f x.length < 2 * tm.acceptCount x (f x.length)) →
            c'.output.cells 1 = Γ.zero))) :
    PP ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, tm, f, m, hhalt, hf, hchar⟩ := PP_integer_characterization_internal hL
  obtain ⟨k', M, q, hwin, hdec⟩ := h k tm f hhalt ⟨m, hf⟩
  refine mem_PSPACE_of_polyWindow M q hwin fun x => ?_
  obtain ⟨c', hreach, hhalted, hone, hzero⟩ := hdec x
  exact ⟨c', hreach, hhalted, fun hx => hone ((hchar x).mp hx),
    fun hx => hzero fun hc => hx ((hchar x).mpr hc)⟩


/-- **`PP ⊆ PSPACE`, reduced to a machine deciding one arithmetic predicate.** The obligation no
longer mentions probability, rationals, the function space `Fin T → Bool`, or the protocol's own
time function: exhibit a machine keeping a polynomial window that decides whether the accepting
tally exceeds the rejecting one over a computable horizon. -/
theorem PP_subset_PSPACE_of_tallyMachine_internal
    (h : ∀ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ) (p : Polynomial ℕ),
      tm.AllPathsHaltIn f → (∀ n, f n ≤ p.eval n) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          ((NTM.tally (fun v => !NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length) <
            NTM.tally (fun v => NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length)) → c'.output.cells 1 = Γ.one) ∧
          (¬ (NTM.tally (fun v => !NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length) <
            NTM.tally (fun v => NTM.acceptsAt tm x (p.eval x.length) v)
              (2 ^ p.eval x.length)) → c'.output.cells 1 = Γ.zero))) :
    PP ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, tm, f, m, hall, hf, hchar⟩ := PP_integer_characterization_internal hL
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hf
  obtain ⟨k', M, q, hwin, hdec⟩ := h k tm f p hall hp
  refine mem_PSPACE_of_polyWindow M q hwin fun x => ?_
  obtain ⟨c', hr, hh, hone, hzero⟩ := hdec x
  have hiff := NTM.mem_iff_tally_lt_tally_poly (L := L) hall hp hchar x
  exact ⟨c', hr, hh, fun hx => hone (hiff.mp hx), fun hx => hzero fun hc => hx (hiff.mpr hc)⟩


/-- **`PP ⊆ PSPACE`, reduced to realising one iterated step function.** The obligation is now as
small as it can be made without building the machine: exhibit a machine keeping a polynomial
window that decides whether, after `2 ^ p |x|` iterations of `NTM.tallyStep` from the zero state,
the accepting component exceeds the rejecting one. The machine's correctness proof therefore has
to reason only about a single loop body, not about counting. -/
theorem PP_subset_PSPACE_of_iterateMachine_internal
    (h : ∀ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ) (p : Polynomial ℕ),
      tm.AllPathsHaltIn f → (∀ n, f n ≤ p.eval n) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (q.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          ((((NTM.tallyStep fun v => NTM.acceptsAt tm x (p.eval x.length) v)^[
              2 ^ p.eval x.length] (0, 0, 0)).2.2 <
            (((NTM.tallyStep fun v => NTM.acceptsAt tm x (p.eval x.length) v)^[
              2 ^ p.eval x.length] (0, 0, 0)).2.1)) → c'.output.cells 1 = Γ.one) ∧
          (¬ (((NTM.tallyStep fun v => NTM.acceptsAt tm x (p.eval x.length) v)^[
              2 ^ p.eval x.length] (0, 0, 0)).2.2 <
            (((NTM.tallyStep fun v => NTM.acceptsAt tm x (p.eval x.length) v)^[
              2 ^ p.eval x.length] (0, 0, 0)).2.1)) → c'.output.cells 1 = Γ.zero))) :
    PP ⊆ PSPACE := by
  intro L hL
  obtain ⟨k, tm, f, m, hall, hf, hchar⟩ := PP_integer_characterization_internal hL
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hf
  obtain ⟨k', M, q, hwin, hdec⟩ := h k tm f p hall hp
  refine mem_PSPACE_of_polyWindow M q hwin fun x => ?_
  obtain ⟨c', hr, hh, hone, hzero⟩ := hdec x
  have hiff := NTM.mem_iff_iterate_tallyStep (L := L) hall hp hchar x
  exact ⟨c', hr, hh, fun hx => hone (hiff.mp hx), fun hx => hzero fun hc => hx (hiff.mpr hc)⟩

/-- **`PP ⊆ PSPACE`.** The obligation of `PP_subset_PSPACE_of_iterateMachine_internal` is met by
`NTM.ppMachine`: park, evaluate the horizon, then loop one simulation per counter value, keeping
two tallies, and compare them. A source machine that starts halted has no accepting path at all,
so that case is decided by `NTM.zeroTM`, which publishes `0` and stops. -/
theorem PP_subset_PSPACE_internal : PP ⊆ PSPACE := by
  refine PP_subset_PSPACE_of_iterateMachine_internal ?_
  intro k tm f p hall hle
  by_cases heq : tm.qstart = tm.qhalt
  · refine ⟨NTM.bodyTapes k, NTM.zeroTM k, NTM.zeroSpacePoly,
      fun x c' hr => NTM.zeroTM_space k x c' hr, fun x => ?_⟩
    obtain ⟨c', hr, hh, hz⟩ := NTM.zeroTM_decides k x
    exact ⟨c', hr, hh, fun hc => absurd hc (NTM.not_ppCond_of_qstart_eq_qhalt k tm heq p x),
      fun _ => hz⟩
  · exact ⟨NTM.bodyTapes k, NTM.ppMachine k tm (p + 1), NTM.ppSpacePoly k (p + 1),
      fun x c' hr => NTM.ppMachine_space k tm hall p hle heq x c' hr,
      fun x => NTM.ppMachine_decides k tm hall p hle heq x⟩

end Complexity
