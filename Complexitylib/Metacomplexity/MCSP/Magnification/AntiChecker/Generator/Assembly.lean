/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Assembly.Defs
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Assembly.Internal

/-!
# Anti-checker generator assembly

This module packages the padded selector into the public generator interface.
It proves the complete conditional construction: correct approximate-counter
families yield correct size-bounded anti-checker generators with overhead
`k + 32`.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- At every sufficiently large positive arity, each correct counter family
packages as a correct generator with the lifted overhead. -/
theorem eventually_exists_generatorOfCounterFamily_isCorrect
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (family : ApproximateCounterFamily counterOverhead beta arity),
          family.IsCorrect →
            ∃ generator :
                Generator (generatorOverheadFromCounter counterOverhead)
                  beta arity,
              generator.IsCorrect :=
  eventually_exists_generatorOfCounterFamily_isCorrect_internal
    counterOverhead beta

/-- Eventually, existence of a correct counter family at one arity implies
existence of a correct generator at that arity. -/
theorem eventually_existsCorrectGeneratorAt_of_existsCorrectCounterFamilyAt
    (counterOverhead : ℕ) (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ExistsCorrectCounterFamilyAt counterOverhead beta arity →
        ExistsCorrectGeneratorAt
          (generatorOverheadFromCounter counterOverhead) beta arity :=
  eventually_existsCorrectGeneratorAt_of_existsCorrectCounterFamilyAt_internal
    counterOverhead beta

/-- The conditional approximate-counter conclusion implies the complete
Anti-Checker Lemma generator conclusion. No complexity-class containment is
used in this circuit-assembly implication. -/
theorem hasGenerators_of_hasApproximateCounterFamilies :
    HasApproximateCounterFamilies → HasGenerators :=
  hasGenerators_of_hasApproximateCounterFamilies_internal

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
