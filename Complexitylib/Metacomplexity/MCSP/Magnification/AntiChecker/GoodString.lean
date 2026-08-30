/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.GoodString.Internal

/-!
# Anti-Checker good-string parameter bridge

The generic good-string argument packs one small circuit for each tuple entry
and composes their outputs with strict majority. This module verifies that its
explicit size bound fits the Anti-Checker Lemma's hard-function threshold at
all sufficiently large arities.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The packed survivor-tuple majority circuit fits the hard-function threshold
at every sufficiently large arity. -/
theorem eventually_survivorTupleMajoritySizeBound_le_hardThreshold
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      AntiChecker.survivorTupleMajoritySizeBound arity
          (smallThreshold beta arity) ≤
        hardThreshold beta arity :=
  eventually_survivorTupleMajoritySizeBound_le_hardThreshold_internal beta

/-- At every sufficiently large arity, hardness at the Anti-Checker Lemma's
threshold guarantees a one-input `1/(2n)` survivor shrink from any prefix. -/
theorem eventually_hasShrinkExtension_of_isHardAt
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (target : BitString arity → Bool)
          (inputs : List (BitString arity)),
        IsHardAt beta target →
          AntiChecker.HasShrinkExtension (2 * arity) target
            (smallThreshold beta arity) inputs :=
  eventually_hasShrinkExtension_of_isHardAt_internal beta

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
