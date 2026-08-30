/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Internal

/-!
# Computational depth

Machine-relative computational depth is formalized as
`C_M^time(output) - C_M(output)`. The extended-natural difference preserves
`⊤` rather than totalizing a missing description as zero. The exact additive
decomposition, finiteness criterion, clock monotonicity, and zero-depth
characterization are proved before any symmetry-of-information hypothesis.
-/


public section

namespace Complexity

/-- Infinite upper description length gives infinite difference. -/
@[simp] theorem descriptionDifference_top_left (lower : WithTop ℕ) :
    descriptionDifference ⊤ lower = ⊤ :=
  descriptionDifference_top_left_internal lower

/-- Infinite lower description length gives infinite difference. -/
@[simp] theorem descriptionDifference_top_right (upper : WithTop ℕ) :
    descriptionDifference upper ⊤ = ⊤ :=
  descriptionDifference_top_right_internal upper

/-- On finite values, description difference is natural subtraction. -/
@[simp] theorem descriptionDifference_coe (upper lower : ℕ) :
    descriptionDifference (upper : WithTop ℕ) (lower : WithTop ℕ) =
      (upper - lower : ℕ) :=
  descriptionDifference_coe_internal upper lower

/-- If the lower description length is at most the upper one, their difference
adds back to the upper length exactly. -/
theorem descriptionDifference_add_lower
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower + lower = upper :=
  descriptionDifference_add_lower_internal horder

/-- Under the same order, description difference is infinite exactly when its
upper value is infinite. -/
theorem descriptionDifference_eq_top_iff
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower = ⊤ ↔ upper = ⊤ :=
  descriptionDifference_eq_top_iff_internal horder

/-- For a finite ordered pair, description difference vanishes exactly when
the two lengths coincide. -/
theorem descriptionDifference_eq_zero_iff
    {upper lower : WithTop ℕ} (horder : lower ≤ upper)
    (hfinite : upper ≠ ⊤) :
    descriptionDifference upper lower = 0 ↔ upper = lower :=
  descriptionDifference_eq_zero_iff_internal horder hfinite

/-- Description differences telescope through an ordered intermediate value. -/
theorem descriptionDifference_add
    {upper middle lower : WithTop ℕ}
    (hlower : lower ≤ middle) (hupper : middle ≤ upper) :
    descriptionDifference upper middle +
        descriptionDifference middle lower =
      descriptionDifference upper lower :=
  descriptionDifference_add_internal hlower hupper

namespace TM

variable {n : ℕ}

/-- Two-clock depth plus the later-clock complexity reconstructs the earlier-
clock complexity exactly. -/
theorem computationalDepthBetween_add_later
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime +
        machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.timeBoundedKolmogorovComplexity output firstTime :=
  computationalDepthBetween_add_later_internal
    machine output hclock

/-- Two-clock depth never exceeds the earlier-clock complexity. -/
theorem computationalDepthBetween_le_first
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime ≤
      machine.timeBoundedKolmogorovComplexity output firstTime :=
  computationalDepthBetween_le_first_internal machine output hclock

/-- Ordered two-clock depth is infinite exactly when the earlier-clock
complexity is infinite. -/
theorem computationalDepthBetween_eq_top_iff
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime laterTime = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output firstTime = ⊤ :=
  computationalDepthBetween_eq_top_iff_internal machine output hclock

/-- Delaying the earlier clock toward a fixed later clock cannot increase the
remaining depth. -/
theorem computationalDepthBetween_mono_first
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output secondTime laterTime ≤
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_mono_first_internal
    machine output hfirst hsecond

/-- Extending the later clock away from a fixed earlier clock cannot decrease
the accumulated depth. -/
theorem computationalDepthBetween_mono_later
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime ≤
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_mono_later_internal
    machine output hfirst hsecond

/-- On a finite earlier-clock instance, two-clock depth is zero exactly when
the extra time does not improve description length. -/
theorem computationalDepthBetween_eq_zero_iff
    (machine : TM n) (output : List Bool)
    {firstTime laterTime : ℕ} (hclock : firstTime ≤ laterTime)
    (hfinite : machine.timeBoundedKolmogorovComplexity output firstTime ≠ ⊤) :
    machine.computationalDepthBetween output firstTime laterTime = 0 ↔
      machine.timeBoundedKolmogorovComplexity output firstTime =
        machine.timeBoundedKolmogorovComplexity output laterTime :=
  computationalDepthBetween_eq_zero_iff_internal
    machine output hclock hfinite

/-- Once the later clock attains plain complexity, two-clock depth is exactly
the usual one-clock computational depth. -/
theorem computationalDepthBetween_eq_computationalDepth
    (machine : TM n) (output : List Bool) (firstTime laterTime : ℕ)
    (hlater : machine.timeBoundedKolmogorovComplexity output laterTime =
      machine.plainKolmogorovComplexity output) :
    machine.computationalDepthBetween output firstTime laterTime =
      machine.computationalDepth output firstTime :=
  computationalDepthBetween_eq_computationalDepth_internal
    machine output firstTime laterTime hlater

/-- Two-clock depths telescope exactly across three ordered clocks. -/
theorem computationalDepthBetween_add
    (machine : TM n) (output : List Bool)
    {firstTime secondTime laterTime : ℕ}
    (hfirst : firstTime ≤ secondTime) (hsecond : secondTime ≤ laterTime) :
    machine.computationalDepthBetween output firstTime secondTime +
        machine.computationalDepthBetween output secondTime laterTime =
      machine.computationalDepthBetween output firstTime laterTime :=
  computationalDepthBetween_add_internal machine output hfirst hsecond

/-- Computational depth plus plain complexity is exactly bounded complexity;
the subtraction is therefore nontruncated on every finite instance. -/
theorem computationalDepth_add_plain
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time +
        machine.plainKolmogorovComplexity output =
      machine.timeBoundedKolmogorovComplexity output time :=
  computationalDepth_add_plain_internal machine output time

/-- Computational depth never exceeds the corresponding bounded complexity. -/
theorem computationalDepth_le_timeBoundedKolmogorovComplexity
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time ≤
      machine.timeBoundedKolmogorovComplexity output time :=
  computationalDepth_le_timeBoundedKolmogorovComplexity_internal
    machine output time

/-- Depth is infinite exactly when bounded complexity is infinite. Plain
complexity cannot be the sole source of infinitude because `C_M ≤ C_M^time`. -/
theorem computationalDepth_eq_top_iff
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output time = ⊤ :=
  computationalDepth_eq_top_iff_internal machine output time

/-- More computation time cannot increase computational depth. -/
theorem computationalDepth_mono
    (machine : TM n) (output : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.computationalDepth output second ≤
      machine.computationalDepth output first :=
  computationalDepth_mono_internal machine output hclock

/-- On a finite bounded instance, depth is zero exactly when the time bound
already attains plain complexity. -/
theorem computationalDepth_eq_zero_iff
    (machine : TM n) (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.computationalDepth output time = 0 ↔
      machine.timeBoundedKolmogorovComplexity output time =
        machine.plainKolmogorovComplexity output :=
  computationalDepth_eq_zero_iff_internal machine output time hfinite

end TM

end Complexity
