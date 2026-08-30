/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Size.Defs

/-!
# Anti-checker generator assembly -- definitions

This layer packages the padded selection circuit as a `Generator` once its
eventual finite size inequality has been supplied.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Package a padded selector built from one approximate-counter family as a
generator with the explicitly lifted overhead. -/
noncomputable def generatorOfCounterFamily
    {counterOverhead arity : ℕ} {beta : PositiveRationalScale}
    [NeZero arity]
    (family : ApproximateCounterFamily counterOverhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity)
    (hsize : (paddedSelectionCircuit family hbudget).2.size ≤
      generatorSizeBound (generatorOverheadFromCounter counterOverhead)
        beta arity) :
    Generator (generatorOverheadFromCounter counterOverhead) beta arity where
  internalGates := (paddedSelectionCircuit family hbudget).1
  circuit := (paddedSelectionCircuit family hbudget).2
  size_le := hsize

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
