/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit.Defs

/-!
# Counter-family extension estimators -- definitions

A finite approximate-counter family induces the total semantic estimator
expected by the round-selection API. Prefixes inside the required range are
packed with one candidate extension and evaluated by the corresponding
counter. Values outside that finite range are deliberately set to zero and
are never queried by the bounded accuracy contract.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace ApproximateCounterFamily

/-- Total extension estimator induced by a finite counter family. -/
def extensionEstimator {overhead arity : ℕ}
    {beta : PositiveRationalScale}
    (family : ApproximateCounterFamily overhead beta arity)
    (target : BitString arity → Bool) :
    List (BitString arity) → BitString arity → ℕ :=
  fun inputs input =>
    if hlength : inputs.length < requiredRoundCount beta arity then
      (family.counter ⟨inputs.length, hlength⟩).estimate
        (packTargetSamples target (input :: inputs).get)
    else
      0

end ApproximateCounterFamily

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
