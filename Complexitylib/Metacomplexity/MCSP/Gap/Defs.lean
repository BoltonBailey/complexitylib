/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Promise.Defs
public import Complexitylib.Metacomplexity.MCSP.Defs

/-!
# Gap MCSP -- definitions

A canonical MCSP instance already contains a source threshold `s`. Gap MCSP
keeps the yes side `minimumSize ≤ s` and parameterizes the no side by an
explicit relaxed threshold `sigma(arity, s)`. This retains both scales needed
by hardness magnification instead of collapsing the promise to an ordinary
language.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

/-- Quantitative relaxation of an MCSP source threshold. -/
structure Parameters where
  /-- No-instances must have minimum size strictly above this threshold. -/
  relaxedThreshold : ℕ → ℕ → ℕ

namespace Parameters

/-- The target threshold is never smaller than the source threshold. This is
exactly what makes the two promised sides disjoint. -/
def IsWidening (parameters : Parameters) : Prop :=
  ∀ arity threshold,
    threshold ≤ parameters.relaxedThreshold arity threshold

/-- Increasing the source threshold cannot decrease its relaxed image. -/
def ThresholdMonotone (parameters : Parameters) : Prop :=
  ∀ arity, Monotone (parameters.relaxedThreshold arity)

/-- Pointwise order on relaxed-threshold maps. -/
def RelaxesTo (first second : Parameters) : Prop :=
  ∀ arity threshold,
    first.relaxedThreshold arity threshold ≤
      second.relaxedThreshold arity threshold

end Parameters

/-- Promised yes condition at the source threshold stored in the instance. -/
def IsYes (inst : MCSP.Instance) : Prop :=
  inst.minimumSize ≤ inst.threshold

/-- Promised no condition above the relaxed target threshold. -/
def IsNo (parameters : Parameters) (inst : MCSP.Instance) : Prop :=
  parameters.relaxedThreshold inst.arity inst.threshold < inst.minimumSize

/-- Canonically encoded yes language. Malformed MCSP encodings lie outside the
promise rather than being assigned to the no side. -/
def yesLanguage : Language :=
  {bits | match MCSP.Instance.decode? bits with
    | some inst => IsYes inst
    | none => False}

/-- Canonically encoded no language for a chosen threshold relaxation. -/
def noLanguage (parameters : Parameters) : Language :=
  {bits | match MCSP.Instance.decode? bits with
    | some inst => IsNo parameters inst
    | none => False}

end GapMCSP

end Complexity
