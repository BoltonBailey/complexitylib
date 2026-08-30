/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Metacomplexity.MINKT.Defs
public import Complexitylib.Models.TuringMachine.OutputSemantics

/-!
# Gap MINKT -- definitions

The decision instance `(x, 1^t, 1^s)` has the following promised sides:

- yes: `C_U^t(x) <= s`;
- no: `C_U^(tau(|x|,t))(x) > sigma(|x|,s)`.

The description transformation `sigma` and clock transformation `tau` are
independent parameters. `Parameters.IsWidening` is kept as a separate property:
it is required to prove the two sides disjoint, but not to state either side or
the associated search relation.

The search relation follows the optimization form: relative to the exact finite
value `C_U^t(x) = s`, output a program of length at most `sigma(|x|,s)` that
produces `x` within `tau(|x|,t)` steps.
-/


@[expose] public section

namespace Complexity

namespace GapMINKT

/-- Independent quantitative transformations for description loss and clock
blow-up. -/
structure Parameters where
  /-- Allowed output-program length from input length and source complexity. -/
  description : ℕ → ℕ → ℕ
  /-- Allowed target clock from input length and source clock. -/
  clock : ℕ → ℕ → ℕ

namespace Parameters

/-- Both resources weakly increase. This suffices to make the gap sides
disjoint and to reuse an exact source description as a search witness. -/
def IsWidening (parameters : Parameters) : Prop :=
  (∀ length threshold, threshold ≤ parameters.description length threshold) ∧
    ∀ length time, time ≤ parameters.clock length time

/-- For each output length, increasing the source threshold cannot decrease
the allowed target description length. -/
def DescriptionMonotone (parameters : Parameters) : Prop :=
  ∀ length, Monotone (parameters.description length)

end Parameters

/-- A decoded gap-decision instance `(x, 1^t, 1^s)`. -/
structure Instance where
  /-- String whose bounded description complexity is measured. -/
  output : List Bool
  /-- Source primitive machine-step budget. -/
  time : ℕ
  /-- Source description-length threshold. -/
  threshold : ℕ

namespace Instance

/-- Forget the decision threshold, retaining the underlying MINKT instance. -/
def base (inst : Instance) : MINKT.Instance where
  output := inst.output
  time := inst.time

/-- Unary encoding of the decision threshold. -/
def unaryThreshold (inst : Instance) : List Bool :=
  List.replicate inst.threshold true

/-- Canonical nested-pair encoding of `(x, 1^t, 1^s)`. -/
def encode (inst : Instance) : List Bool :=
  pair inst.base.encode inst.unaryThreshold

/-- Decode one canonical gap instance, rejecting malformed pairing and every
non-unary threshold field. -/
def decode? (bits : List Bool) : Option Instance := do
  let (baseBits, thresholdBits) ← unpair? bits
  let base ← MINKT.Instance.decode? baseBits
  if thresholdBits = List.replicate thresholdBits.length true then
    some
      { output := base.output
        time := base.time
        threshold := thresholdBits.length }
  else
    none

/-- Replace only the source description threshold. -/
def withThreshold (inst : Instance) (threshold : ℕ) : Instance :=
  { inst with threshold }

/-- Promised yes condition `C_U^t(x) <= s`. -/
def IsYes {tapes : ℕ} (inst : Instance) (machine : TM tapes) : Prop :=
  machine.timeBoundedKolmogorovComplexity inst.output inst.time ≤
    (inst.threshold : WithTop ℕ)

/-- Promised no condition
`C_U^(tau(|x|,t))(x) > sigma(|x|,s)`. -/
def IsNo {tapes : ℕ} (inst : Instance) (machine : TM tapes)
    (parameters : Parameters) : Prop :=
  (parameters.description inst.output.length inst.threshold : WithTop ℕ) <
    machine.timeBoundedKolmogorovComplexity inst.output
      (parameters.clock inst.output.length inst.time)

/-- A program witnessing the relaxed target resources of a gap instance. -/
def IsRelaxedWitness {tapes : ℕ} (inst : Instance) (machine : TM tapes)
    (parameters : Parameters) (program : List Bool) : Prop :=
  program.length ≤ parameters.description inst.output.length inst.threshold ∧
    machine.ProducesInTime program inst.output
      (parameters.clock inst.output.length inst.time)

end Instance

/-- Canonically encoded promised yes language. Malformed codes are outside the
promise rather than being assigned to the no side. -/
def yesLanguage {tapes : ℕ} (machine : TM tapes) : Language :=
  {bits | match Instance.decode? bits with
    | some inst => inst.IsYes machine
    | none => False}

/-- Canonically encoded promised no language for the quantitative gap. -/
def noLanguage {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) : Language :=
  {bits | match Instance.decode? bits with
    | some inst => inst.IsNo machine parameters
    | none => False}

/-- Direct source-threshold witness relation for the promised yes language. -/
def YesWitnessRelation {tapes : ℕ} (machine : TM tapes)
    (bits program : List Bool) : Prop :=
  ∃ inst : Instance,
    Instance.decode? bits = some inst ∧
      program.length ≤ inst.threshold ∧
      machine.ProducesInTime program inst.output inst.time

/-- Search approximation relative to the exact finite source complexity.

On input `(x, 1^t)`, a related program has length at most
`sigma(|x|, C_U^t(x))` and produces `x` within `tau(|x|,t)`. -/
def SearchRelation {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) (inst : MINKT.Instance)
    (program : List Bool) : Prop :=
  ∃ optimum : ℕ,
    machine.timeBoundedKolmogorovComplexity inst.output inst.time =
        (optimum : WithTop ℕ) ∧
      program.length ≤ parameters.description inst.output.length optimum ∧
      machine.ProducesInTime program inst.output
        (parameters.clock inst.output.length inst.time)

/-- Semantic search algorithm returning a candidate program from `(x,1^t)`. -/
abbrev SearchAlgorithm := MINKT.Instance → List Bool

/-- A search algorithm satisfies the approximation relation on every input
whose source time-bounded complexity is finite. -/
def SolvesSearchOnFinite {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) (search : SearchAlgorithm) : Prop :=
  ∀ inst,
    machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ →
      SearchRelation machine parameters inst (search inst)

/-- Executably check whether a candidate meets a gap instance's relaxed target
resources. -/
def verifyRelaxedWitness {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) (inst : Instance) (program : List Bool) : Bool :=
  decide
      (program.length ≤ parameters.description inst.output.length inst.threshold) &&
    decide
      (machine.ProducesInTime program inst.output
        (parameters.clock inst.output.length inst.time))

/-- Convert a search algorithm into a total Boolean decision function by
decoding a gap instance and checking the returned candidate program. -/
def decisionOfSearch {tapes : ℕ} (machine : TM tapes)
    (parameters : Parameters) (search : SearchAlgorithm) : List Bool → Bool :=
  fun bits => match Instance.decode? bits with
    | some inst => verifyRelaxedWitness machine parameters inst (search inst.base)
    | none => false

end GapMINKT

end Complexity
