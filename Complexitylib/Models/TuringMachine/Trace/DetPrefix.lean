/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Deterministic prefixes of nondeterministic traces

Many NTM constructions (guess-and-verify, deterministic preprocessing before
a nondeterministic phase) run through a *deterministic prefix*: a region of
configurations on which the two transition branches agree. On that region the
trace is independent of the choice bits and follows an ordinary DTM run.

This file provides the generic transport for that pattern:

- `NTM.det` — project an NTM onto the DTM that always follows branch `b`.
- `NTM.det_step_congr` — on a configuration where the branches agree, the two
  projections take the same step.
- `NTM.trace_succ_det` — one non-halted trace step is one step of the
  `det`-projection selected by the current choice bit.
- `NTM.trace_of_det_prefix` — the workhorse: given an invariant `P` that is
  preserved by `det false` steps and forces branch agreement, a `det false`
  run of `t ≤ T` steps to `c'` lets any length-`T` trace restart from `c'`
  with the first `t` choices discarded.
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-- Project an NTM onto the deterministic machine that always follows
    branch `b`. The projection shares the NTM's state space, so its
    configurations coincide with the NTM's. -/
def det (N : NTM n) (b : Bool) : TM n where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := N.δ b
  δ_right_of_start := N.δ_right_of_start b

/-- The two transition branches of `N` agree at configuration `c` (on the
    symbols actually under the heads). This is the pointwise hypothesis under
    which a trace step is choice-independent. -/
def BranchesAgreeAt (N : NTM n) (c : Cfg n N.Q) : Prop :=
  N.δ true c.state c.input.read (fun i => (c.work i).read) c.output.read =
    N.δ false c.state c.input.read (fun i => (c.work i).read) c.output.read

/-- On a configuration where the branches agree, every `det`-projection takes
    the same step as `det false`. -/
theorem det_step_congr {N : NTM n} {c : Cfg n N.Q}
    (h : N.BranchesAgreeAt c) (b : Bool) :
    (N.det b).step c = (N.det false).step c := by
  cases b
  · rfl
  · simp only [TM.step, det]
    rw [show N.δ true c.state c.input.read (fun i => (c.work i).read)
      c.output.read = _ from h]

/-- One non-halted trace step applies the `det`-projection selected by the
    current choice bit. -/
theorem trace_succ_det {N : NTM n} {c : Cfg n N.Q} {T : ℕ}
    (choices : Fin (T + 1) → Bool) (hne : c.state ≠ N.qhalt) :
    N.trace (T + 1) choices c =
      N.trace T (fun i => choices ⟨i.val + 1, by omega⟩)
        (((N.det (choices ⟨0, Nat.zero_lt_succ T⟩)).step c).get
          (by simp [TM.step, det, hne])) := by
  simp [NTM.trace, det, TM.step, hne]

/-- **Deterministic-prefix transport.** Let `P` be an invariant that forces
    the two transition branches to agree and is preserved by `det false`
    steps. If `det false` runs `t` steps from `c` to `c'`, then along *any*
    choice sequence of length `s + t` the trace passes through `c'`:
    it equals the trace of the remaining `s` steps from `c'` with the
    first `t` choices discarded. -/
theorem trace_of_det_prefix {N : NTM n} {P : Cfg n N.Q → Prop}
    (hagree : ∀ c, P c → N.BranchesAgreeAt c)
    (hpres : ∀ {c c'}, P c → (N.det false).step c = some c' → P c')
    {t : ℕ} {c c' : Cfg n N.Q}
    (hreach : (N.det false).reachesIn t c c') (hP : P c)
    (s : ℕ) (choices : Fin (s + t) → Bool) :
    N.trace (s + t) choices c =
      N.trace s (fun i => choices ⟨i.val + t, by omega⟩) c' := by
  induction t generalizing c with
  | zero =>
    obtain rfl := TM.reachesIn_zero_iff.mp hreach
    rfl
  | succ t ih =>
    obtain ⟨c'', hstep, hrest⟩ := TM.reachesIn_succ_iff.mp hreach
    have hne := TM.state_ne_qhalt_of_step hstep
    change N.trace ((s + t) + 1) choices c = _
    rw [trace_succ_det (N := N) (T := s + t) (c := c) choices hne]
    have hstep' :=
      (det_step_congr (hagree _ hP) (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).trans hstep
    have hisSome : ((N.det (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).step c).isSome := by
      rw [hstep']; rfl
    have hget : ((N.det (choices ⟨0, Nat.zero_lt_succ (s + t)⟩)).step c).get hisSome = c'' :=
      Option.some_injective _ ((Option.some_get hisSome).trans hstep')
    rw [hget]
    exact ih hrest (hpres hP hstep) _
