/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Shannon.Internal

/-!
# Shannon bounds for canonical MCSP

The classical circuit-counting frontier is exposed directly through canonical
MCSP codes. At arity at least six, some truth table is rejected at threshold
`2^n / (5n)`. At arity at least sixteen, every truth table is accepted at
threshold `18 * 2^n / n`.

These are finite statements in the library's exact fan-in-two circuit model;
they do not assert hardness of deciding MCSP.
-/


public section

namespace Complexity

namespace MCSP

/-- At every arity at least six, some canonical truth table has minimum circuit
size strictly above the Shannon lower threshold. -/
theorem exists_minimumSize_gt_shannonLower
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ inst : Instance,
      inst.arity = arity ∧
        inst.threshold = 2 ^ arity / (5 * arity) ∧
          inst.minimumSize > 2 ^ arity / (5 * arity) :=
  exists_minimumSize_gt_shannonLower_internal arity harity

/-- The Shannon lower bound gives an actual canonical MCSP no-instance at its
explicit threshold. -/
theorem exists_not_mem_at_shannonLower
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ inst : Instance,
      inst.arity = arity ∧
        inst.threshold = 2 ^ arity / (5 * arity) ∧
          inst.encode ∉ Complexity.MCSP :=
  exists_not_mem_at_shannonLower_internal arity harity

/-- Equivalently, a Boolean function packaged by the canonical truth-table
constructor is rejected at the Shannon lower threshold. -/
theorem exists_ofFunction_not_mem_at_shannonLower
    (arity : ℕ) (harity : 6 ≤ arity) :
    ∃ f : BitString arity → Bool,
      (Instance.ofFunction arity (2 ^ arity / (5 * arity)) f).encode ∉
        Complexity.MCSP :=
  exists_ofFunction_not_mem_at_shannonLower_internal arity harity

/-- Every canonical MCSP instance whose threshold reaches the explicit
Shannon upper bound is a yes-instance. -/
theorem mem_encode_of_shannonUpper_le_threshold
    (inst : Instance) (harity : 16 ≤ inst.arity)
    (hthreshold : 18 * 2 ^ inst.arity / inst.arity ≤ inst.threshold) :
    inst.encode ∈ Complexity.MCSP :=
  mem_encode_of_shannonUpper_le_threshold_internal inst harity hthreshold

/-- Packaging any Boolean function at the Shannon upper threshold produces a
canonical MCSP yes-instance. -/
theorem ofFunction_mem_at_shannonUpper
    (arity : ℕ) (harity : 16 ≤ arity) (f : BitString arity → Bool) :
    (Instance.ofFunction arity (18 * 2 ^ arity / arity) f).encode ∈
      Complexity.MCSP :=
  ofFunction_mem_at_shannonUpper_internal arity harity f

/-- The exact finite Shannon window for canonical MCSP: at the lower threshold
some truth table is rejected, while at the upper threshold every truth table is
accepted. The two constants and the truth-table arity remain explicit. -/
theorem shannon_threshold_window (arity : ℕ) (harity : 16 ≤ arity) :
    (∃ f : BitString arity → Bool,
      (Instance.ofFunction arity (2 ^ arity / (5 * arity)) f).encode ∉
        Complexity.MCSP) ∧
      ∀ f : BitString arity → Bool,
        (Instance.ofFunction arity (18 * 2 ^ arity / arity) f).encode ∈
          Complexity.MCSP := by
  exact ⟨exists_ofFunction_not_mem_at_shannonLower arity (by omega),
    fun f => ofFunction_mem_at_shannonUpper arity harity f⟩

end MCSP

end Complexity
