/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Defs
import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.Internal

/-!
# Relative approximate counting

Cartesian-power amplification followed by integer upper-root recovery turns
the weak hashing estimator into a relative estimator. Its internal hash-probe
majorities directly reduce the total failure probability to `2^-failureBits`;
the constant-success `3/4` bound is the specialization at two bits.
-/


public section

namespace Complexity

namespace ApproximateCounting

namespace Relative

/-- The amplified relative hashing estimator fails with probability at most
`2^-failureBits`. -/
theorem one_sub_two_pow_le_eventProb_successEvent
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    1 - 1 / (2 : ℚ) ^ failureBits ≤
      eventProb (successEvent precision failureBits set) :=
  one_sub_two_pow_le_eventProb_successEvent_internal set hprecision

/-- Equivalently, inaccurate seeds have probability at most
`2^-failureBits`. -/
theorem eventProb_failureEvent_le_two_pow
    {domainWidth precision failureBits : ℕ}
    (set : Finset (BitString domainWidth)) (hprecision : 0 < precision) :
    eventProb (failureEvent precision failureBits set) ≤
      1 / (2 : ℚ) ^ failureBits :=
  eventProb_failureEvent_le_two_pow_internal set hprecision

/-- One run of the relative hashing estimator is accurate with probability at
least `3/4`. -/
theorem three_fourths_le_eventProb_successEvent
    {domainWidth precision : ℕ} (set : Finset (BitString domainWidth))
    (hprecision : 0 < precision) :
    3 / 4 ≤ eventProb (successEvent precision 2 set) :=
  three_fourths_le_eventProb_successEvent_internal set hprecision

end Relative

end ApproximateCounting

end Complexity
