/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Defs
public import Complexitylib.Metacomplexity.MCSP.Threshold.Defs

/-!
# Arity-indexed Gap MCSP slices -- definitions

These are the explicit `GapMCSP[s_yes, s_no]` promise problems used in
hardness-magnification statements. Both thresholds are functions of the
represented Boolean-function arity. The input remains a canonical full MCSP
code, with its threshold field forced to `s_yes`.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

/-- The two arity-indexed thresholds of a Gap MCSP slice. -/
structure SliceParameters where
  /-- Circuit-size threshold on the yes side. -/
  yesThreshold : ℕ → ℕ
  /-- Strict circuit-size threshold on the no side. -/
  noThreshold : ℕ → ℕ

namespace SliceParameters

/-- The no threshold is at least the yes threshold at every arity. -/
def IsGap (parameters : SliceParameters) : Prop :=
  ∀ arity, parameters.yesThreshold arity ≤ parameters.noThreshold arity

/-- Exact parameter order supporting table-preserving rethreshold reductions.
The target accepts at least as many small functions and rejects at least as
many large functions as the source. -/
def ReducesTo (source target : SliceParameters) : Prop :=
  (∀ arity, source.yesThreshold arity ≤ target.yesThreshold arity) ∧
    ∀ arity, target.noThreshold arity ≤ source.noThreshold arity

end SliceParameters

/-- Yes side of `GapMCSP[s_yes, s_no]`. -/
def sliceYesLanguage (parameters : SliceParameters) : Language :=
  MCSP.atThreshold parameters.yesThreshold

/-- No side of `GapMCSP[s_yes, s_no]`. The encoded threshold is forced to the
yes threshold; the second parameter only determines the semantic no cutoff. -/
def sliceNoLanguage (parameters : SliceParameters) : Language :=
  {bits | match MCSP.Instance.decode? bits with
    | some inst =>
        inst.threshold = parameters.yesThreshold inst.arity ∧
          parameters.noThreshold inst.arity < inst.minimumSize
    | none => False}

end GapMCSP

end Complexity
