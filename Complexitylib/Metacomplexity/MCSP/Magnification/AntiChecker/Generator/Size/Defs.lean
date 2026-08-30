/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Padding.Defs

/-!
# Anti-checker generator size bounds -- definitions

The full selector repeats an exhaustive minimum circuit and then pads its
output. These definitions give a coarse finite bound for that construction
and an explicit overhead transformation suitable for the published
`2^n * 2^(k * beta * n)` generator interface.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Additive exponent slack used to absorb the sample-count factors and fixed
polynomial overhead of the exhaustive selector. -/
def generatorOverheadSlack : ℕ := 3 * fixedConstant + 2

/-- Generator overhead obtained from the per-counter overhead. -/
def generatorOverheadFromCounter (counterOverhead : ℕ) : ℕ :=
  counterOverhead + generatorOverheadSlack

/-- Coarse factor accounting for every selection round and its counter. -/
def selectionSizeFactor (counterOverhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  (sampleCount beta arity + 1) *
    (counterSizeBound counterOverhead beta arity +
      (sampleCount beta arity + arity + 1) ^ 2)

/-- Finite upper bound used for the complete padded selection circuit. -/
def paddedSelectionSizeBound (counterOverhead : ℕ)
    (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  67 * 2 ^ arity * selectionSizeFactor counterOverhead beta arity

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
