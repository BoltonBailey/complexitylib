/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Hashing.Internal

/-!
# Hashing-based weak approximate counting

Independent amplified affine-hash probes produce a factor-`16` estimate with
constant success probability. The generic bound keeps the amplification error
explicit; choosing `domainWidth + 4` error bits gives success at least `3/4`.
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

/-- Union bound for all hash widths: every bad response has total probability
at most `(domainWidth + 4) / 2^errorBits`. -/
theorem eventProb_badHashingEvent_le
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    eventProb (badHashingEvent (errorBits := errorBits) set) ≤
      (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits :=
  eventProb_badHashingEvent_le_internal set

/-- The hashing-based weak estimator is within factor `16` except with the
union-bound error accumulated over all `domainWidth + 4` levels. -/
theorem one_sub_error_le_eventProb_factorApproximationEvent
    {domainWidth errorBits : ℕ} (set : Finset (BitString domainWidth)) :
    1 - (domainWidth + 4 : ℚ) / (2 : ℚ) ^ errorBits ≤
      eventProb (factorApproximationEvent (errorBits := errorBits) set) :=
  one_sub_error_le_eventProb_factorApproximationEvent_internal set

/-- With `domainWidth + 4` amplification bits, the hashing-based weak
estimator gives a factor-`16` approximation with probability at least `3/4`. -/
theorem three_fourths_le_eventProb_factorApproximationEvent
    {domainWidth : ℕ} (set : Finset (BitString domainWidth)) :
    3 / 4 ≤ eventProb
      (factorApproximationEvent (errorBits := domainWidth + 4) set) :=
  three_fourths_le_eventProb_factorApproximationEvent_internal set

end Weak

end ApproximateCounting

end Complexity
