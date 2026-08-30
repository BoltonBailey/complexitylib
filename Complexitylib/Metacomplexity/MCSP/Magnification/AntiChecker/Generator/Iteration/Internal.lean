/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs
import Complexitylib.Circuits.Composition
import Complexitylib.Circuits.InputProjection

/-!
# Finite iteration of anti-checker selection rounds -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem eval_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family 0 hrounds).2.eval table =
      selectionRoundInput table (emptyLabeledPrefix arity) := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.eval_projectInputs]
  funext coordinate
  change table (selectionEmptyStateInputMap arity coordinate) =
    Fin.append table (emptyLabeledPrefix arity) coordinate
  have hcoordinate : coordinate =
      Fin.castAdd (0 * (arity + 1))
        (selectionEmptyStateInputMap arity coordinate) := by
    apply Fin.ext
    rfl
  rw [hcoordinate, Fin.append_left]
  apply congrArg table
  apply Fin.ext
  rfl

theorem size_selectionPrefixCircuit_zero_internal
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family 0 hrounds).2.size = 2 ^ arity := by
  simp only [selectionPrefixCircuit]
  rw [Circuit.size_projectInputs]
  simp [selectionRoundInputWidth]

theorem eval_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval table =
      (selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))).2.eval
          ((selectionPrefixCircuit family rounds
            (selectionPrefixPriorBound hrounds)).2.eval table) := by
  simp only [selectionPrefixCircuit]
  exact Circuit.eval_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2 table

theorem size_selectionPrefixCircuit_succ_internal
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.size =
      (selectionPrefixCircuit family rounds
          (selectionPrefixPriorBound hrounds)).2.size +
        (selectionRoundStateCircuit
          (family.counter (selectionPrefixCounterIndex hrounds))).2.size := by
  simp only [selectionPrefixCircuit]
  exact Circuit.size_compose
    (selectionRoundStateCircuit
      (family.counter (selectionPrefixCounterIndex hrounds))).2
    (selectionPrefixCircuit family rounds
      (selectionPrefixPriorBound hrounds)).2

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
