/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Internal
public import Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Pointwise output semantics -- proof internals

Proofs supporting the public API in
`Complexitylib.Models.TuringMachine.OutputSemantics`.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

theorem runCfg_add_internal (tm : TM n) (c : Cfg n tm.Q) (first second : ℕ) :
    tm.runCfg c (first + second) = tm.runCfg (tm.runCfg c first) second := by
  induction second with
  | zero => rfl
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 from by omega, runCfg, ih,
        runCfg]

theorem runCfg_of_halted_internal (tm : TM n) {c : Cfg n tm.Q}
    (hhalt : tm.halted c) (steps : ℕ) : tm.runCfg c steps = c := by
  induction steps with
  | zero => rfl
  | succ steps ih => rw [runCfg, ih, TM.step, if_pos hhalt, Option.getD_none]

theorem runCfg_of_reachesIn_internal (tm : TM n) {c c' : Cfg n tm.Q} {steps : ℕ}
    (hreach : tm.reachesIn steps c c') : tm.runCfg c steps = c' := by
  induction hreach with
  | zero => rfl
  | @step c c'' steps c' hstep _ ih =>
      rw [show steps + 1 = 1 + steps from by omega, runCfg_add_internal, runCfg, runCfg,
        hstep, Option.getD_some, ih]

/-- The bounded evaluator's endpoint is reachable in some number of actual
transitions no greater than its clock. -/
theorem runCfg_reachesIn_internal (tm : TM n) (c : Cfg n tm.Q) (time : ℕ) :
    ∃ steps, steps ≤ time ∧ tm.reachesIn steps c (tm.runCfg c time) := by
  induction time with
  | zero => exact ⟨0, le_rfl, reachesIn.zero⟩
  | succ time ih =>
      obtain ⟨steps, hsteps, hreach⟩ := ih
      rw [runCfg]
      cases hstep : tm.step (tm.runCfg c time) with
      | none =>
          rw [Option.getD_none]
          exact ⟨steps, hsteps.trans (Nat.le_succ time), hreach⟩
      | some c' =>
          rw [Option.getD_some]
          exact ⟨steps + 1, by omega, reachesIn_snoc hreach hstep⟩

/-- A halted exact-step endpoint is the bounded evaluator's endpoint at every
larger clock. -/
theorem runCfg_eq_of_reachesIn_halted_internal (tm : TM n) {c c' : Cfg n tm.Q}
    {steps time : ℕ} (hreach : tm.reachesIn steps c c') (hhalt : tm.halted c')
    (hsteps : steps ≤ time) : tm.runCfg c time = c' := by
  rw [show time = steps + (time - steps) from by omega, runCfg_add_internal,
    runCfg_of_reachesIn_internal tm hreach, runCfg_of_halted_internal tm hhalt]

theorem producesInTime_iff_runCfg_internal (tm : TM n) (program output : List Bool)
    (time : ℕ) :
    tm.ProducesInTime program output time ↔
      tm.halted (tm.runCfg (tm.initCfg program) time) ∧
        (tm.runCfg (tm.initCfg program) time).output.HasOutput output := by
  constructor
  · rintro ⟨c, steps, hsteps, hreach, hhalt, hout⟩
    rw [runCfg_eq_of_reachesIn_halted_internal tm hreach hhalt hsteps]
    exact ⟨hhalt, hout⟩
  · rintro ⟨hhalt, hout⟩
    obtain ⟨steps, hsteps, hreach⟩ :=
      runCfg_reachesIn_internal tm (tm.initCfg program) time
    exact ⟨_, steps, hsteps, hreach, hhalt, hout⟩

theorem producesInTime_mono_internal {tm : TM n} {program output : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hproduce : tm.ProducesInTime program output first) :
    tm.ProducesInTime program output second := by
  obtain ⟨c, steps, hsteps, hreach, hhalt, hout⟩ := hproduce
  exact ⟨c, steps, hsteps.trans hbound, hreach, hhalt, hout⟩

theorem produces_of_producesInTime_internal {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.Produces program output := by
  obtain ⟨c, _steps, _hsteps, hreach, hhalt, hout⟩ := hproduce
  exact ⟨c, reaches_of_reachesIn hreach, hhalt, hout⟩

theorem produces_iff_exists_producesInTime_internal (tm : TM n)
    (program output : List Bool) :
    tm.Produces program output ↔ ∃ time, tm.ProducesInTime program output time := by
  constructor
  · rintro ⟨c, hreach, hhalt, hout⟩
    obtain ⟨steps, hsteps⟩ := tm.reaches_to_reachesIn hreach
    exact ⟨steps, c, steps, le_rfl, hsteps, hhalt, hout⟩
  · rintro ⟨time, hproduce⟩
    exact produces_of_producesInTime_internal hproduce

private theorem ofBool_injective_internal {left right : Bool}
    (h : Γ.ofBool left = Γ.ofBool right) : left = right := by
  cases left <;> cases right <;> simp [Γ.ofBool] at h ⊢

theorem hasOutput_length_eq_internal {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) :
    left.length = right.length := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : right.length < left.length := Nat.lt_of_not_ge hnot
    have hbit := hleft.1 right.length hlt
    rw [hright.2] at hbit
    exact Γ.ofBool_ne_blank _ hbit.symm
  · by_contra hnot
    have hlt : left.length < right.length := Nat.lt_of_not_ge hnot
    have hbit := hright.1 left.length hlt
    rw [hleft.2] at hbit
    exact Γ.ofBool_ne_blank _ hbit.symm

theorem hasOutput_eq_internal {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) : left = right := by
  have hlength := hasOutput_length_eq_internal hleft hright
  apply List.ext_get hlength
  intro index hindexLeft hindexRight
  apply ofBool_injective_internal
  exact (hleft.1 index hindexLeft).symm.trans (hright.1 index hindexRight)

theorem producesInTime_output_unique_internal {tm : TM n}
    {program left right : List Bool} {leftTime rightTime : ℕ}
    (hleft : tm.ProducesInTime program left leftTime)
    (hright : tm.ProducesInTime program right rightTime) : left = right := by
  let time := max leftTime rightTime
  have hleft' := producesInTime_mono_internal (le_max_left leftTime rightTime) hleft
  have hright' := producesInTime_mono_internal (le_max_right leftTime rightTime) hright
  have hleftRun :=
    (producesInTime_iff_runCfg_internal tm program left time).mp hleft'
  have hrightRun :=
    (producesInTime_iff_runCfg_internal tm program right time).mp hright'
  exact hasOutput_eq_internal hleftRun.2 hrightRun.2

theorem produces_output_unique_internal {tm : TM n} {program left right : List Bool}
    (hleft : tm.Produces program left) (hright : tm.Produces program right) : left = right := by
  obtain ⟨leftTime, hleftTime⟩ :=
    (produces_iff_exists_producesInTime_internal tm program left).mp hleft
  obtain ⟨rightTime, hrightTime⟩ :=
    (produces_iff_exists_producesInTime_internal tm program right).mp hright
  exact producesInTime_output_unique_internal hleftTime hrightTime

theorem computesInTime_iff_forall_producesInTime_internal (tm : TM n)
    (function : List Bool → List Bool) (time : ℕ → ℕ) :
    tm.ComputesInTime function time ↔
      ∀ input, tm.ProducesInTime input (function input) (time input.length) :=
  Iff.rfl

theorem computes_iff_forall_produces_internal (tm : TM n)
    (function : List Bool → List Bool) :
    tm.Computes function ↔ ∀ input, tm.Produces input (function input) := by
  classical
  constructor
  · rintro ⟨time, hcompute⟩ input
    exact produces_of_producesInTime_internal (hcompute input)
  · intro hproduce
    have hbounded : ∀ input, ∃ time, tm.ProducesInTime input (function input) time :=
      fun input =>
        (produces_iff_exists_producesInTime_internal tm input (function input)).mp
          (hproduce input)
    choose inputTime hinputTime using hbounded
    let time : ℕ → ℕ := fun length =>
      Finset.sup (Finset.univ : Finset (Fin length → Bool))
        (fun input => inputTime (List.ofFn input))
    have hleTime : ∀ input, inputTime input ≤ time input.length := by
      intro input
      show inputTime input ≤
        Finset.sup Finset.univ (fun bits => inputTime (List.ofFn bits))
      conv_lhs =>
        rw [show input = List.ofFn (fun i : Fin input.length => input[↑i]) from
          (List.ofFn_getElem (xs := input)).symm]
      exact Finset.le_sup (f := fun bits => inputTime (List.ofFn bits))
        (Finset.mem_univ (fun i : Fin input.length => input[↑i]))
    refine ⟨time, (computesInTime_iff_forall_producesInTime_internal
      tm function time).mpr ?_⟩
    intro input
    exact producesInTime_mono_internal (hleTime input) (hinputTime input)

end TM

end Complexity
