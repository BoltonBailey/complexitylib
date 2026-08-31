/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

/-!
# Weak approximate counting -- definitions

The weak Stockmeyer estimator probes hash-cell occupancy at every relevant
output width. It returns the power of two indexed by the largest positive
answer, with four extra levels supplying the constant-factor slack.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

/-- Hash output widths probed by the weak estimator. -/
abbrev Level (domainWidth : ℕ) : Type := Fin (domainWidth + 4)

/-- The level-zero hash output width. -/
def zeroLevel (domainWidth : ℕ) : Fin (domainWidth + 4) :=
  ⟨0, by omega⟩

/-- Levels at which the amplified occupancy test answers positively. -/
def trueLevels {domainWidth : ℕ}
    (responses : Fin (domainWidth + 4) → Bool) :
    Finset (Fin (domainWidth + 4)) :=
  Finset.univ.filter fun level => responses level = true

/-- Largest level at which the occupancy test answers positively, or level
zero if there is no positive answer. -/
def selectedLevel {domainWidth : ℕ}
    (responses : Fin (domainWidth + 4) → Bool) : Fin (domainWidth + 4) :=
  if h : (trueLevels responses).Nonempty then
    (trueLevels responses).max' h
  else
    zeroLevel domainWidth

/-- Constant-factor estimate selected from amplified occupancy responses. -/
def estimate {domainWidth : ℕ}
    (responses : Fin (domainWidth + 4) → Bool) : ℕ :=
  if responses (zeroLevel domainWidth) then
    2 ^ (selectedLevel responses).val
  else
    0

/-- The response contract needed by the weak estimator. Levels whose expected
cell size is at least `8` answer positively, levels whose expected cell size is
at most `1/8` answer negatively, and level zero detects an empty set exactly. -/
def ResponsesAccurate {domainWidth cardinality : ℕ}
    (responses : Fin (domainWidth + 4) → Bool) : Prop :=
  responses (zeroLevel domainWidth) = decide (0 < cardinality) ∧
    (∀ level, 8 * 2 ^ level.val ≤ cardinality → responses level = true) ∧
    ∀ level, 8 * cardinality ≤ 2 ^ level.val → responses level = false

instance instDecidableResponsesAccurate {domainWidth cardinality : ℕ}
    (responses : Fin (domainWidth + 4) → Bool) :
    Decidable (ResponsesAccurate (cardinality := cardinality) responses) := by
  unfold ResponsesAccurate
  infer_instance

end Weak

end ApproximateCounting

end Complexity
