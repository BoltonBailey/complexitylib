/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Defs
public import
  Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Affine
public import Complexitylib.SAT.CircuitSatisfiability
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.HashCell.Circuit.Internal

/-!
# Circuit predicates for anti-checker hash cells

The canonical fixed-prefix circuit-satisfiability query associated with an
implementing predicate circuit is accepted exactly when its semantic affine
zero cell contains a powered survivor tuple.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace HashCellPredicateCircuit

/-- The existential-witness ruler has exactly the powered-survivor width. -/
theorem ruler_length (beta : PositiveRationalScale) (arity : ℕ) :
    (ruler beta arity).length = counterSurvivorPowerWidth beta arity :=
  ruler_length_internal beta arity

/-- Evaluating a predicate's tagged code on its public prefix followed by a
witness returns the semantic hash-cell predicate. -/
theorem evalFamilyCode_code
    {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth))
    (witness : BitString (counterSurvivorPowerWidth beta arity)) :
    CircuitCode.evalFamilyCode predicate.code
        ((hashCellPublicInput beta input seed).toList ++ witness.toList) =
      some (decide (HashCellWitness arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed witness)) :=
  evalFamilyCode_code_internal predicate input seed witness

/-- The canonical extension-language query is accepted exactly when the
selected affine zero cell contains a powered survivor witness. -/
theorem query_mem_extensionLanguage_iff
    {beta : PositiveRationalScale} {arity prefixLength rangeWidth : ℕ}
    (predicate : HashCellPredicateCircuit beta arity prefixLength rangeWidth)
    (input : BitString (counterInputWidth arity prefixLength))
    (seed : BitString (PairwiseIndependentHash.affineSeedWidth
      (counterSurvivorPowerWidth beta arity) rangeWidth)) :
    predicate.query input seed ∈ CircuitSAT.extensionLanguage ↔
      HashCellNonempty arity (smallThreshold beta arity)
        (roundPrecision arity) rangeWidth input seed :=
  query_mem_extensionLanguage_iff_internal predicate input seed

end HashCellPredicateCircuit

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
