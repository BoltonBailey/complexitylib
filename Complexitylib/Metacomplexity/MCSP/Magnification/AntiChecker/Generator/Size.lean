/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Size.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Size.Internal

/-!
# Anti-checker generator size bounds

This module accounts for the complete exhaustive selector, its dependent
round composition, and its final output padding. It converts a counter-family
overhead `k` into the explicit generator overhead `k + 32`; the added exponent
absorbs three sample-count factors and two rounds of fixed polynomial slack.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The explicit additive slack in the counter-to-generator overhead lift. -/
@[simp] theorem generatorOverheadSlack_eq : generatorOverheadSlack = 32 := by
  rfl

/-- The full generator uses the counter overhead plus the fixed construction
slack. -/
@[simp] theorem generatorOverheadFromCounter_eq (counterOverhead : ℕ) :
    generatorOverheadFromCounter counterOverhead = counterOverhead + 32 := by
  rfl

/-- Every used selection round has one common size bound once the required
round count fits inside the published sample budget. -/
theorem size_selectionRoundStateCircuit_le_common
    {counterOverhead arity prefixLength : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (counter :
      ApproximateCounterCircuit counterOverhead beta arity prefixLength)
    (hprefix : prefixLength + 1 ≤ requiredRoundCount beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (selectionRoundStateCircuit counter).2.size ≤
      64 * 2 ^ arity *
        (counterSizeBound counterOverhead beta arity +
          (sampleCount beta arity + arity + 1) ^ 2) :=
  size_selectionRoundStateCircuit_le_common_internal
    counter hprefix hbudget

/-- The dependent prefix composition costs at most its truth-table copy plus
the number of rounds times the common round bound. -/
theorem size_selectionPrefixCircuit_le
    {counterOverhead arity rounds : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily counterOverhead beta arity)
    (hrounds : rounds ≤ requiredRoundCount beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (selectionPrefixCircuit family rounds hrounds).2.size ≤
      2 ^ arity + rounds *
        (64 * 2 ^ arity *
          (counterSizeBound counterOverhead beta arity +
            (sampleCount beta arity + arity + 1) ^ 2)) :=
  size_selectionPrefixCircuit_le_internal family hrounds hbudget

/-- The complete padded circuit lies below the explicit finite construction
bound. -/
theorem size_paddedSelectionCircuit_le_paddedSelectionSizeBound
    {counterOverhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity]
    (family : ApproximateCounterFamily counterOverhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    (paddedSelectionCircuit family hbudget).2.size ≤
      paddedSelectionSizeBound counterOverhead beta arity :=
  size_paddedSelectionCircuit_le_paddedSelectionSizeBound_internal
    family hbudget

/-- The finite construction bound is eventually at most the generator bound
with the explicitly lifted overhead. -/
theorem eventually_paddedSelectionSizeBound_le_generatorSizeBound
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      paddedSelectionSizeBound counterOverhead beta arity ≤
        generatorSizeBound (generatorOverheadFromCounter counterOverhead)
          beta arity :=
  eventually_paddedSelectionSizeBound_le_generatorSizeBound_internal
    counterOverhead beta

/-- For every sufficiently large positive arity, the actual padded selector
circuit satisfies the generator interface's rounded size bound. -/
theorem eventually_size_paddedSelectionCircuit_le_generatorSizeBound
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (family : ApproximateCounterFamily counterOverhead beta arity)
          (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity),
          (paddedSelectionCircuit family hbudget).2.size ≤
            generatorSizeBound
              (generatorOverheadFromCounter counterOverhead) beta arity :=
  eventually_size_paddedSelectionCircuit_le_generatorSizeBound_internal
    counterOverhead beta

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
