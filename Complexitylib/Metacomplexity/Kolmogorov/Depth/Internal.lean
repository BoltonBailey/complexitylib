/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Depth.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Computational depth -- proof internals
-/


public section

namespace Complexity

theorem descriptionDifference_top_left_internal (lower : WithTop ℕ) :
    descriptionDifference ⊤ lower = ⊤ := by
  rfl

theorem descriptionDifference_top_right_internal (upper : WithTop ℕ) :
    descriptionDifference upper ⊤ = ⊤ := by
  induction upper using WithTop.recTopCoe <;> rfl

theorem descriptionDifference_coe_internal (upper lower : ℕ) :
    descriptionDifference (upper : WithTop ℕ) (lower : WithTop ℕ) =
      (upper - lower : ℕ) := by
  rfl

theorem descriptionDifference_add_lower_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower + lower = upper := by
  induction upper using WithTop.recTopCoe with
  | top => simp [descriptionDifference]
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          change ((upper - lower + lower : ℕ) : WithTop ℕ) = upper
          exact WithTop.coe_eq_coe.mpr <|
            Nat.sub_add_cancel (WithTop.coe_le_coe.mp horder)

theorem descriptionDifference_le_upper_internal
    {upper lower : WithTop ℕ} (horder : lower ≤ upper) :
    descriptionDifference upper lower ≤ upper := by
  induction upper using WithTop.recTopCoe with
  | top => exact le_top
  | coe upper =>
      induction lower using WithTop.recTopCoe with
      | top => simp at horder
      | coe lower =>
          exact WithTop.coe_le_coe.mpr (Nat.sub_le upper lower)

theorem descriptionDifference_mono_left_internal
    {lower first second : WithTop ℕ}
    (hlower : lower ≤ first) (hupper : first ≤ second) :
    descriptionDifference first lower ≤
      descriptionDifference second lower := by
  induction second using WithTop.recTopCoe with
  | top => exact le_top
  | coe second =>
      induction first using WithTop.recTopCoe with
      | top => simp at hupper
      | coe first =>
          induction lower using WithTop.recTopCoe with
          | top => simp at hlower
          | coe lower =>
              exact WithTop.coe_le_coe.mpr <|
                Nat.sub_le_sub_right (WithTop.coe_le_coe.mp hupper) lower

namespace TM

variable {n : ℕ}

theorem computationalDepth_add_plain_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time +
        machine.plainKolmogorovComplexity output =
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_add_lower_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

theorem computationalDepth_le_timeBoundedKolmogorovComplexity_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time ≤
      machine.timeBoundedKolmogorovComplexity output time := by
  exact descriptionDifference_le_upper_internal
    (plainKolmogorovComplexity_le_timeBounded_internal machine output time)

theorem computationalDepth_eq_top_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ) :
    machine.computationalDepth output time = ⊤ ↔
      machine.timeBoundedKolmogorovComplexity output time = ⊤ := by
  constructor
  · intro hdepth
    by_contra htime
    have hplain : machine.plainKolmogorovComplexity output ≠ ⊤ := by
      intro htop
      have horder :=
        plainKolmogorovComplexity_le_timeBounded_internal machine output time
      rw [htop] at horder
      exact htime (top_unique horder)
    obtain ⟨timeValue, htimeValue⟩ := WithTop.ne_top_iff_exists.mp htime
    obtain ⟨plainValue, hplainValue⟩ := WithTop.ne_top_iff_exists.mp hplain
    rw [computationalDepth, ← htimeValue, ← hplainValue] at hdepth
    change ((timeValue - plainValue : ℕ) : WithTop ℕ) = ⊤ at hdepth
    exact WithTop.coe_ne_top hdepth
  · intro htime
    simp [computationalDepth, htime, descriptionDifference_top_left_internal]

theorem computationalDepth_mono_internal
    (machine : TM n) (output : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.computationalDepth output second ≤
      machine.computationalDepth output first := by
  apply descriptionDifference_mono_left_internal
  · exact plainKolmogorovComplexity_le_timeBounded_internal
      machine output second
  · exact timeBoundedKolmogorovComplexity_mono_internal
      machine output hclock

theorem computationalDepth_eq_zero_iff_internal
    (machine : TM n) (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    machine.computationalDepth output time = 0 ↔
      machine.timeBoundedKolmogorovComplexity output time =
        machine.plainKolmogorovComplexity output := by
  have hplain : machine.plainKolmogorovComplexity output ≠ ⊤ := by
    intro htop
    have horder :=
      plainKolmogorovComplexity_le_timeBounded_internal machine output time
    rw [htop] at horder
    exact hfinite (top_unique horder)
  obtain ⟨timeValue, htimeValue⟩ := WithTop.ne_top_iff_exists.mp hfinite
  obtain ⟨plainValue, hplainValue⟩ := WithTop.ne_top_iff_exists.mp hplain
  have horder : plainValue ≤ timeValue := by
    have hbase := plainKolmogorovComplexity_le_timeBounded_internal
      machine output time
    rw [← hplainValue, ← htimeValue] at hbase
    exact WithTop.coe_le_coe.mp hbase
  rw [computationalDepth, ← htimeValue, ← hplainValue]
  change ((timeValue - plainValue : ℕ) : WithTop ℕ) = (0 : ℕ) ↔
    (timeValue : WithTop ℕ) = (plainValue : ℕ)
  constructor
  · intro hzero
    apply WithTop.coe_eq_coe.mpr
    have hsub := WithTop.coe_eq_coe.mp hzero
    exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub) horder
  · intro heq
    apply WithTop.coe_eq_coe.mpr
    have hvalues : timeValue = plainValue := by
      exact_mod_cast heq
    simp [hvalues]

end TM

end Complexity
