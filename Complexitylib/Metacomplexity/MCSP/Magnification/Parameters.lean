/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.CircuitSize
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters.Internal
public import Complexitylib.Metacomplexity.MCSP.Raw
public import Complexitylib.Metacomplexity.ScaledExponent

/-!
# GapMCSP hardness-magnification parameters

This module exposes the exact finite raw GapMCSP family selected for the first
hardness-magnification target. Its floor-rounded yes/no thresholds always form a
promise gap, floor-to-ceiling exponent changes cost at most a factor of two, and
the rounded solver bound agrees exactly with its arity form on `N = 2^n` inputs.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace Parameters

/-- At arity zero, division by `c*n` makes the yes threshold zero. -/
@[simp] theorem yesThreshold_zero (parameters : Parameters) :
    parameters.yesThreshold 0 = 0 :=
  yesThreshold_zero_internal parameters

/-- At arity zero, the no threshold is `2^0 = 1`. -/
@[simp] theorem noThreshold_zero (parameters : Parameters) :
    parameters.noThreshold 0 = 1 :=
  noThreshold_zero_internal parameters

/-- The finite yes threshold never exceeds the no threshold. -/
theorem yesThreshold_le_noThreshold
    (parameters : Parameters) (arity : ℕ) :
    parameters.yesThreshold arity ≤ parameters.noThreshold arity :=
  yesThreshold_le_noThreshold_internal parameters arity

/-- The selected thresholds form a valid GapMCSP slice at every arity. -/
theorem sliceParameters_isGap (parameters : Parameters) :
    parameters.sliceParameters.IsGap :=
  sliceParameters_isGap_internal parameters

@[simp] theorem sliceParameters_yesThreshold
    (parameters : Parameters) :
    parameters.sliceParameters.yesThreshold = parameters.yesThreshold := rfl

@[simp] theorem sliceParameters_noThreshold
    (parameters : Parameters) :
    parameters.sliceParameters.noThreshold = parameters.noThreshold := rfl

/-- Restoring the denominator after natural division stays below the no
threshold. -/
theorem yesThreshold_mul_denominator_le_noThreshold
    (parameters : Parameters) (arity : ℕ) :
    parameters.yesThreshold arity * (parameters.constant * arity) ≤
      parameters.noThreshold arity :=
  yesThreshold_mul_denominator_le_noThreshold_internal parameters arity

/-- The large-circuit threshold is always positive. -/
theorem noThreshold_pos (parameters : Parameters) (arity : ℕ) :
    0 < parameters.noThreshold arity :=
  noThreshold_pos_internal parameters arity

/-- The small-circuit threshold is positive once its natural divisor fits below
the rounded binary exponential. -/
theorem yesThreshold_pos_of_denominator_le
    (parameters : Parameters) {arity : ℕ} (harity : 0 < arity)
    (hdenominator : parameters.constant * arity ≤
      parameters.beta.powFloor arity) :
    0 < parameters.yesThreshold arity :=
  yesThreshold_pos_of_denominator_le_internal
    parameters harity hdenominator

/-- The rounded binary exponential eventually dominates the selected linear
denominator `c*n`. -/
theorem eventually_denominator_le_powFloor (parameters : Parameters) :
    ∀ᶠ arity in Filter.atTop,
      parameters.constant * arity ≤ parameters.beta.powFloor arity :=
  eventually_denominator_le_powFloor_internal parameters

/-- The selected small-circuit threshold is positive at every sufficiently
large arity. -/
theorem eventually_yesThreshold_pos (parameters : Parameters) :
    ∀ᶠ arity in Filter.atTop, 0 < parameters.yesThreshold arity :=
  eventually_yesThreshold_pos_internal parameters

/-- Floor rounding puts the no threshold below the ceiling-rounded power. -/
theorem noThreshold_le_powCeil
    (parameters : Parameters) (arity : ℕ) :
    parameters.noThreshold arity ≤ parameters.beta.powCeil arity :=
  noThreshold_le_powCeil_internal parameters arity

/-- Ceiling rounding increases the no threshold by at most a factor of two. -/
theorem powCeil_le_two_mul_noThreshold
    (parameters : Parameters) (arity : ℕ) :
    parameters.beta.powCeil arity ≤ 2 * parameters.noThreshold arity :=
  powCeil_le_two_mul_noThreshold_internal parameters arity

end Parameters

/-- On raw length `N = 2^n`, the rounded `N^(1+epsilon)` bound agrees exactly
with its arity-indexed presentation. -/
@[simp] theorem circuitBound_pow
    (epsilon : PositiveRationalScale) (arity : ℕ) :
    circuitBound epsilon (2 ^ arity) = circuitBoundAtArity epsilon arity :=
  circuitBound_pow_internal epsilon arity

/-- The solver bound on a canonical table payload depends on its represented
arity exactly as intended. -/
theorem circuitBound_tableBits
    (epsilon : PositiveRationalScale) (inst : MCSP.Instance) :
    circuitBound epsilon inst.tableBits.length =
      circuitBoundAtArity epsilon inst.arity :=
  circuitBound_tableBits_internal epsilon inst

/-- A slightly-superlinear solver bound is at least the raw truth-table length. -/
theorem truthTableLength_le_circuitBoundAtArity
    (epsilon : PositiveRationalScale) (arity : ℕ) :
    2 ^ arity ≤ circuitBoundAtArity epsilon arity :=
  truthTableLength_le_circuitBoundAtArity_internal epsilon arity

namespace Parameters

/-- The selected finite raw GapMCSP promise at exponent `beta` and constant
`c`. -/
@[expose] def rawProblem (parameters : Parameters) : PromiseProblem :=
  rawSliceProblem parameters.sliceParameters parameters.sliceParameters_isGap

@[simp] theorem rawProblem_yesInstances (parameters : Parameters) :
    parameters.rawProblem.yesInstances =
      rawSliceYesLanguage parameters.sliceParameters := rfl

@[simp] theorem rawProblem_noInstances (parameters : Parameters) :
    parameters.rawProblem.noInstances =
      rawSliceNoLanguage parameters.sliceParameters := rfl

/-- Exact minimum-size semantics of the selected yes side. -/
theorem mem_rawProblem_yesInstances_tableBits_iff
    (parameters : Parameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ parameters.rawProblem.yesInstances ↔
      inst.minimumSize ≤ parameters.yesThreshold inst.arity := by
  exact mem_rawSliceYesLanguage_tableBits_iff
    parameters.sliceParameters inst

/-- Exact minimum-size semantics of the selected no side. -/
theorem mem_rawProblem_noInstances_tableBits_iff
    (parameters : Parameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ parameters.rawProblem.noInstances ↔
      parameters.noThreshold inst.arity < inst.minimumSize := by
  exact mem_rawSliceNoLanguage_tableBits_iff
    parameters.sliceParameters inst

/-- Every promised input in the selected finite family has raw length `2^n`. -/
theorem mem_rawProblem_promise_imp_isRawTruthTable
    (parameters : Parameters) {bits : List Bool}
    (hmem : bits ∈ parameters.rawProblem.promise) :
    MCSP.IsRawTruthTable bits :=
  mem_rawSliceProblem_promise_imp_isRawTruthTable
    parameters.sliceParameters parameters.sliceParameters_isGap hmem

/-- The selected raw problem has a pointwise circuit lower bound at exponent
`1+epsilon`. -/
def HasPointwiseCircuitLowerBound
    (parameters : Parameters) (epsilon : PositiveRationalScale) : Prop :=
  parameters.rawProblem ∉ PromiseSIZE (circuitBound epsilon)

/-- The selected raw problem has a circuit lower bound even when finitely many
exceptional input lengths are allowed. -/
def HasEventualCircuitLowerBound
    (parameters : Parameters) (epsilon : PositiveRationalScale) : Prop :=
  parameters.rawProblem ∉ PromiseEventuallySIZE (circuitBound epsilon)

/-- An eventual lower bound implies the corresponding pointwise lower bound. -/
theorem HasEventualCircuitLowerBound.pointwise
    {parameters : Parameters} {epsilon : PositiveRationalScale}
    (hlower : parameters.HasEventualCircuitLowerBound epsilon) :
    parameters.HasPointwiseCircuitLowerBound epsilon := by
  intro hpointwise
  exact hlower (PromiseSIZE_subset_PromiseEventuallySIZE
    (circuitBound epsilon) hpointwise)

end Parameters

end Magnification

end GapMCSP

end Complexity
