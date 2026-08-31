/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.FixedWidth.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding.Defs

/-!
# Anti-checker counter relation -- definitions

The approximate counter estimates the number of canonical small-circuit codes
consistent with an arbitrary fixed-width vector of labeled samples. Defining
this relation independently of a target function also gives contradictory
labels their intended zero-survivor semantics.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- One encoded circuit agrees with one explicitly labeled sample. Malformed
or non-evaluating codes do not agree. -/
def CodeMatchesLabeledSample {arity : ℕ} (code : List Bool)
    (sample : SuccinctMCSP.Sample arity) : Prop :=
  CircuitCode.evalCode arity code sample.input.toList = some sample.output

instance {arity : ℕ} (code : List Bool)
    (sample : SuccinctMCSP.Sample arity) :
    Decidable (CodeMatchesLabeledSample code sample) := by
  unfold CodeMatchesLabeledSample
  exact inferInstance

/-- One encoded circuit agrees with every sample in a fixed-width vector. -/
def CodeMatchesLabeledSamples {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (code : List Bool) : Prop :=
  ∀ sample, CodeMatchesLabeledSample code (samples sample)

instance {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (code : List Bool) : Decidable (CodeMatchesLabeledSamples samples code) := by
  unfold CodeMatchesLabeledSamples
  exact inferInstance

/-- Canonical small-circuit codes surviving an arbitrary labeled-sample
vector. -/
def candidateLabeledSurvivorCodes {count : ℕ} (arity threshold : ℕ)
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    Finset (List Bool) :=
  (AntiChecker.candidateCodes arity threshold).filter
    (CodeMatchesLabeledSamples samples)

/-- Number of canonical small-circuit codes surviving an arbitrary
labeled-sample vector. -/
def candidateLabeledSurvivorCount {count : ℕ} (arity threshold : ℕ)
    (samples : Fin count → SuccinctMCSP.Sample arity) : ℕ :=
  (candidateLabeledSurvivorCodes arity threshold samples).card

/-- One valid fixed-width description agrees with one explicitly labeled
sample through its parser-free raw-circuit view. -/
def DescriptionMatchesLabeledSample {arity threshold : ℕ}
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold)
    (sample : SuccinctMCSP.Sample arity) : Prop :=
  description.val.toRawCircuit.eval? sample.input.toList =
    some sample.output

instance {arity threshold : ℕ}
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold)
    (sample : SuccinctMCSP.Sample arity) :
    Decidable (DescriptionMatchesLabeledSample description sample) := by
  unfold DescriptionMatchesLabeledSample
  infer_instance

/-- One valid fixed-width description agrees with every sample in a vector. -/
def DescriptionMatchesLabeledSamples {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold) :
    Prop :=
  ∀ sample, DescriptionMatchesLabeledSample description (samples sample)

instance {count arity threshold : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity)
    (description : CircuitCode.FixedWidth.ValidDescription arity threshold) :
    Decidable (DescriptionMatchesLabeledSamples samples description) := by
  unfold DescriptionMatchesLabeledSamples
  infer_instance

/-- Valid fixed-width descriptions surviving an arbitrary labeled-sample
vector. -/
noncomputable def candidateLabeledSurvivorDescriptions {count : ℕ}
    (arity threshold : ℕ)
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    Finset (CircuitCode.FixedWidth.ValidDescription arity threshold) :=
  Finset.univ.filter (DescriptionMatchesLabeledSamples samples)

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
