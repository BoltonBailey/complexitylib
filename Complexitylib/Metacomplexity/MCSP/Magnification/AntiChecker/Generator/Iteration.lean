/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Internal

/-!
# Finite iteration of anti-checker selection rounds

This module exposes exact base and successor equations for the dependent
composition of prefix-length counter-selection circuits.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Zero selection rounds preserve the truth table and attach the empty
labeled prefix. -/
@[simp] theorem eval_selectionPrefixCircuit_zero
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family 0 hrounds).2.eval table =
      selectionRoundInput table (emptyLabeledPrefix arity) :=
  eval_selectionPrefixCircuit_zero_internal family hrounds table

/-- The initial state-copy circuit has exactly one output gate per truth-table
bit. -/
@[simp] theorem size_selectionPrefixCircuit_zero
    {overhead arity : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : 0 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family 0 hrounds).2.size = 2 ^ arity :=
  size_selectionPrefixCircuit_zero_internal family hrounds

/-- A nonempty prefix circuit evaluates the previous prefix circuit and then
the counter-selection round indexed by that prefix length. -/
@[simp] theorem eval_selectionPrefixCircuit_succ
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity)
    (table : BitString (2 ^ arity)) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.eval table =
      (selectionRoundStateCircuit
        (family.counter (selectionPrefixCounterIndex hrounds))).2.eval
          ((selectionPrefixCircuit family rounds
            (selectionPrefixPriorBound hrounds)).2.eval table) :=
  eval_selectionPrefixCircuit_succ_internal family hrounds table

/-- Serial composition gives exact additive size at every successor round. -/
@[simp] theorem size_selectionPrefixCircuit_succ
    {overhead arity rounds : ℕ} {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (hrounds : rounds + 1 ≤ requiredRoundCount beta arity) :
    (selectionPrefixCircuit family (rounds + 1) hrounds).2.size =
      (selectionPrefixCircuit family rounds
          (selectionPrefixPriorBound hrounds)).2.size +
        (selectionRoundStateCircuit
          (family.counter (selectionPrefixCounterIndex hrounds))).2.size :=
  size_selectionPrefixCircuit_succ_internal family hrounds

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
