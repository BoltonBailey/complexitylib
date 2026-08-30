/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Growth.Internal

/-!
# Growth bounds for the iterated-clock schedule

Finite iteration preserves the library's explicit polynomial-growth contract.
In particular, an admissible primitive clock makes both the one-step ordinary
gap transform and the four-step conditional gap transform admissible.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

/-- Every fixed finite iterate of a polynomially bounded clock is again
polynomially bounded. -/
theorem clockIterate_polynomiallyBounded
    {clock : ℕ → ℕ}
    (hclock : ∃ coefficient exponent, ∀ time,
      clock time ≤ coefficient * (time + 1) ^ exponent)
    (iterations : ℕ) :
    ∃ coefficient exponent, ∀ time,
      clockIterate clock iterations time ≤
        coefficient * (time + 1) ^ exponent :=
  clockIterate_polynomiallyBounded_internal hclock iterations

/-- An admissible primitive clock induces admissible ordinary logarithmic-gap
parameters. -/
theorem IsAdmissibleClock.ordinaryParameters_admissible
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock) :
    (ordinaryParameters clock).IsAdmissible :=
  hclock.ordinaryParameters_admissible_internal

/-- An admissible primitive clock induces admissible fourfold conditional-gap
parameters. -/
theorem IsAdmissibleClock.conditionalParameters_admissible
    {clock : ℕ → ℕ} (hclock : IsAdmissibleClock clock) :
    (conditionalParameters clock).IsAdmissible :=
  hclock.conditionalParameters_admissible_internal

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
