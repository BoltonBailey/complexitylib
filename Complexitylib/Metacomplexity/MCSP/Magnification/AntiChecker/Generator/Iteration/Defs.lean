/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round.Defs

/-!
# Finite iteration of anti-checker selection rounds -- definitions

The counter family is indexed by the current labeled-prefix length. This
module composes the corresponding width-changing state circuit for any bounded
number of rounds, retaining exact types at every intermediate prefix length.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The empty row-major labeled-prefix encoding. -/
def emptyLabeledPrefix (arity : ℕ) : BitString (0 * (arity + 1)) :=
  fun coordinate =>
    Fin.elim0 ⟨coordinate.val, by simpa using coordinate.isLt⟩

/-- Reindex the zero-round state width to the bare truth-table width. -/
def selectionEmptyStateInputMap (arity : ℕ) :
    Fin (selectionRoundInputWidth arity 0) → Fin (2 ^ arity) :=
  fun input =>
    ⟨input.val, by
      have hinput := input.isLt
      simpa [selectionRoundInputWidth] using hinput⟩

/-- Removing the final round preserves the required-round upper bound. -/
theorem selectionPrefixPriorBound
    {beta : PositiveRationalScale} {arity rounds : ℕ}
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    rounds ≤ requiredRoundCount beta arity := by
  omega

/-- Counter-family index used by the final step of a nonempty bounded prefix. -/
def selectionPrefixCounterIndex
    {beta : PositiveRationalScale} {arity rounds : ℕ}
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    Fin (requiredRoundCount beta arity) :=
  ⟨rounds, by omega⟩

/-- Compose the first `rounds` counter-selection state transitions. -/
noncomputable def selectionPrefixCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity) :
    (rounds : ℕ) → rounds ≤ requiredRoundCount beta arity →
      Σ internalGates,
        Circuit Basis.andOr2 (2 ^ arity)
          (selectionRoundInputWidth arity rounds) internalGates
  | 0, _ => ⟨0, Circuit.projectInputs (selectionEmptyStateInputMap arity)⟩
  | rounds + 1, hrounds =>
      let previous := selectionPrefixCircuit family rounds
        (selectionPrefixPriorBound hrounds)
      let round := selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))
      ⟨_, round.2.compose previous.2⟩

/-- State circuit after every required counter-selection round. -/
noncomputable def fullSelectionStateCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity) :
    Σ internalGates,
      Circuit Basis.andOr2 (2 ^ arity)
        (selectionRoundInputWidth arity
          (requiredRoundCount beta arity)) internalGates :=
  selectionPrefixCircuit family (requiredRoundCount beta arity) le_rfl

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
