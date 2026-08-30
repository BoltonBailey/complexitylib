/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters

/-!
# The selected GapMCSP magnification frontier -- definitions

This layer states the nested lower-bound quantifiers from the selected
Oliveira--Pich--Santhanam frontier without asserting the magnification theorem.
The denominator constant is fixed first. A positive solver exponent is then
chosen, and every sufficiently small positive threshold exponent must give an
eventual-in-input-length circuit lower bound.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

/-- A positive candidate for the universal denominator constant `c` in the
selected GapMCSP thresholds. -/
structure DenominatorConstant where
  /-- The natural value of the constant. -/
  value : ℕ
  /-- The constant is at least one. -/
  value_pos : 0 < value

namespace DenominatorConstant

/-- Instantiate the selected finite parameters at one positive exponent
`beta`, keeping the denominator constant fixed. -/
def parametersAt
    (constant : DenominatorConstant) (beta : PositiveRationalScale) :
    Parameters where
  beta := beta
  constant := constant.value
  constant_pos := constant.value_pos

/-- At fixed `c` and `epsilon`, every sufficiently small positive `beta` gives
a raw GapMCSP problem outside eventual circuit size `N^(1+epsilon)`.

The outer filter is over `beta`; `HasEventualCircuitLowerBound` separately
allows finitely many exceptional input lengths for each selected problem. -/
def HasSmallBetaCircuitLowerBound
    (constant : DenominatorConstant) (epsilon : PositiveRationalScale) : Prop :=
  ∀ᶠ beta in PositiveRationalScale.atZeroFromPositive,
    (constant.parametersAt beta).HasEventualCircuitLowerBound epsilon

/-- The complete lower-bound antecedent at one fixed denominator constant:
some positive `epsilon` works for every sufficiently small positive `beta`. -/
def HasMagnificationLowerBoundHypothesis
    (constant : DenominatorConstant) : Prop :=
  ∃ epsilon, constant.HasSmallBetaCircuitLowerBound epsilon

end DenominatorConstant

end Magnification

end GapMCSP

end Complexity
