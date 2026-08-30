/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputProjection.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection.Defs

/-!
# Iterable anti-checker selection rounds -- definitions

One round preserves the target truth table and prepends the labeled sample
chosen by exhaustive counter minimization to the carried prefix. Its output
therefore has exactly the state layout expected by the next prefix-length
counter.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- State obtained by prepending one fixed candidate sample to a labeled
prefix while preserving the target truth table. -/
def selectionRoundSuccessorInput {arity prefixLength : ℕ}
    (candidate : Fin (2 ^ arity)) (table : BitString (2 ^ arity))
    (packedPrefix : BitString (prefixLength * (arity + 1))) :
    BitString (selectionRoundInputWidth arity (prefixLength + 1)) :=
  selectionRoundInput table
    (packLabeledSamples
      (candidateLabeledSamples candidate table packedPrefix))

/-- Reorder the preserved state and minimum key-payload record into the next
round's truth-table-plus-labeled-prefix layout. -/
def selectionRoundSuccessorInputMap
    (beta : PositiveRationalScale) (arity prefixLength : ℕ) :
    Fin (selectionRoundInputWidth arity (prefixLength + 1)) →
      Fin (selectionRoundInputWidth arity prefixLength +
        (counterOutputWidth beta arity + (arity + 1))) :=
  fun output =>
    Fin.addCases
      (fun tableCoordinate =>
        ⟨tableCoordinate.val, by
          simp only [selectionRoundInputWidth]
          omega⟩)
      (fun packedCoordinate =>
        let position := finProdFinEquiv.symm packedCoordinate
        Fin.cases
          ⟨selectionRoundInputWidth arity prefixLength +
              counterOutputWidth beta arity + position.2.val, by
            simp only [selectionRoundInputWidth]
            omega⟩
          (fun prefixRow =>
            ⟨2 ^ arity +
                (finProdFinEquiv (prefixRow, position.2)).val, by
              simp only [selectionRoundInputWidth]
              omega⟩)
          position.1)
      output

/-- Preserve the current state in parallel with exhaustive counter
minimization. -/
noncomputable def selectionRoundCombinedCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    Σ internalGates,
      Circuit Basis.andOr2 (selectionRoundInputWidth arity prefixLength)
        (selectionRoundInputWidth arity prefixLength +
          (counterOutputWidth beta arity + (arity + 1))) internalGates :=
  let state := Circuit.projectInputs (fun input => input)
  let minimum := minimumCounterRecordCircuit counter
  ⟨_, state.parallel minimum.2⟩

/-- One iterable selection round, returning the preserved truth table followed
by the newly selected labeled sample and the old labeled prefix. -/
noncomputable def selectionRoundStateCircuit
    {overhead arity prefixLength : ℕ} {beta : PositiveRationalScale}
    (counter : ApproximateCounterCircuit overhead beta arity prefixLength) :
    Σ internalGates,
      Circuit Basis.andOr2 (selectionRoundInputWidth arity prefixLength)
        (selectionRoundInputWidth arity (prefixLength + 1)) internalGates :=
  let combined := selectionRoundCombinedCircuit counter
  let successor := Circuit.projectInputs
    (selectionRoundSuccessorInputMap beta arity prefixLength)
  ⟨_, successor.compose combined.2⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
