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

namespace TM

variable {n : ℕ}

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
