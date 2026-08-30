/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator.Defs
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

/-- Circuit state represented by a target truth table and an ordered vector of
target-labeled selected inputs. -/
def selectionTraceState {arity rounds : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin rounds → BitString arity) :
    BitString (selectionRoundInputWidth arity rounds) :=
  selectionRoundInput (truthTable target)
    (packTargetSamples target inputs)

/-- Project the input coordinates from the labeled rows carried by a selection
state, discarding the preserved truth table and every output label. -/
def selectionSampleOutputMap (arity rounds : ℕ) :
    Fin (rounds * arity) → Fin (selectionRoundInputWidth arity rounds) :=
  fun output =>
    let position := finProdFinEquiv.symm output
    Fin.natAdd (2 ^ arity)
      (finProdFinEquiv (position.1, position.2.castSucc))

instance (beta : PositiveRationalScale) (arity : ℕ) [NeZero arity] :
    NeZero (requiredRoundCount beta arity * arity) :=
  ⟨by
    simp [requiredRoundCount, roundShrinkDenominator, roundBlockCount,
      NeZero.ne arity]⟩

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

/-- Full selection circuit with its carried state projected down to the packed
input coordinates of the required-round sample vector. -/
noncomputable def fullSelectionSamplesCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity) :
    Σ internalGates,
      Circuit Basis.andOr2 (2 ^ arity)
        (requiredRoundCount beta arity * arity) internalGates := by
  let state := fullSelectionStateCircuit family
  let samples := Circuit.projectInputs
    (selectionSampleOutputMap arity (requiredRoundCount beta arity))
  exact ⟨_, samples.compose state.2⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
