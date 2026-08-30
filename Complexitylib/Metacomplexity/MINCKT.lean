/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Growth
public import Complexitylib.Metacomplexity.MINCKT.Internal

/-!
# Minimum conditional time-bounded Kolmogorov complexity

This module exposes canonical `(x, y, 1^t)` instances for machine-relative
conditional time-bounded Kolmogorov complexity. Conditions use the library's
faithful random-access oracle convention. Universality and paper-specific
evaluator equivalence remain explicit future obligations. The depth-adjusted
`GapMINCKT` promise follows Hirahara's 2022 Definition 6.1.
-/


public section

namespace Complexity

namespace MINCKT

namespace Instance

variable {tapes : ℕ}

/-- The unary clock has exactly the represented length. -/
@[simp] theorem length_unaryClock (inst : Instance) :
    inst.unaryClock.length = inst.time :=
  length_unaryClock_internal inst

/-- Every canonical conditional MinKT instance decodes exactly. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Successful decoding characterizes canonical instance encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding fails exactly on noncanonical strings. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- Canonical conditional MinKT encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact code length for the right-associated tuple `(x, y, 1^t)`. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length =
      2 * inst.output.length + 2 * inst.condition.length + inst.time + 4 :=
  length_encode_internal inst

/-- A conditional complexity threshold is equivalent to a direct bounded
program witness. -/
theorem isAtMost_iff_hasProgramAtMost (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) :
    inst.IsAtMost machine threshold ↔
      inst.HasProgramAtMost machine threshold :=
  isAtMost_iff_hasProgramAtMost_internal inst machine threshold

/-- Giving the conditional evaluator more time preserves an upper threshold. -/
theorem IsAtMost.withTime_mono (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) {first second : ℕ}
    (hclock : first ≤ second)
    (hsmall : (inst.withTime first).IsAtMost machine threshold) :
    (inst.withTime second).IsAtMost machine threshold :=
  isAtMost_withTime_mono_internal inst machine threshold hclock hsmall

/-- Increasing the description threshold preserves membership. -/
theorem IsAtMost.threshold_mono (inst : Instance)
    (machine : OracleTM tapes) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hsmall : inst.IsAtMost machine first) :
    inst.IsAtMost machine second :=
  isAtMost_threshold_mono_internal inst machine hthreshold hsmall

end Instance

end MINCKT

end Complexity
