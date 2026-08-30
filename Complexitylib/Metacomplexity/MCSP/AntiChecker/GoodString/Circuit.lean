/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Circuit.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString.Circuit.Internal

/-!
# Good-string circuit bridge

Every canonical survivor code decodes to a typed circuit of the advertised
size. Packing a survivor tuple and composing strict majority therefore gives a
single circuit bounded by `survivorTupleMajoritySizeBound`. Target hardness
above that bound supplies the every-tuple coverage premise used by the
good-string counting argument.
-/


public section

namespace Complexity

namespace AntiChecker

/-- A canonical survivor code has a typed circuit witness of size at most the
survivor threshold, with output equal to `survivorCodeOutput`. -/
theorem exists_survivorCodeCircuit {arity : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (code : SurvivorCode target threshold inputs) :
    ∃ internalGates,
      ∃ circuit : Circuit Basis.andOr2 arity 1 internalGates,
        circuit.size ≤ threshold ∧
          ∀ input,
            (circuit.eval input) 0 =
              survivorCodeOutput target threshold inputs code input :=
  exists_survivorCodeCircuit_internal target threshold inputs code

/-- Pointwise strict majority of a survivor tuple is computed by one circuit
within the explicit packing-plus-majority size bound. -/
theorem exists_survivorTupleMajorityCircuit
    {arity : ℕ} [NeZero arity]
    (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity))
    (tuple : Fin arity → SurvivorCode target threshold inputs) :
    ∃ internalGates,
      ∃ circuit : Circuit Basis.andOr2 arity 1 internalGates,
        circuit.size ≤ survivorTupleMajoritySizeBound arity threshold ∧
          ∀ input,
            (circuit.eval input) 0 =
              majority (fun i =>
                survivorCodeOutput target threshold inputs (tuple i) input) :=
  exists_survivorTupleMajorityCircuit_internal
    target threshold inputs tuple

/-- If the target is hard above the packing-plus-majority size bound, every
survivor tuple is caught by some input. -/
theorem everySurvivorTupleCaught_of_circuitHardness
    {arity threshold hardnessThreshold : ℕ} [NeZero arity]
    (target : BitString arity → Bool)
    (inputs : List (BitString arity))
    (hfits :
      survivorTupleMajoritySizeBound arity threshold ≤ hardnessThreshold)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity hardnessThreshold target).HasCircuitAtMost) :
    EverySurvivorTupleCaught target threshold inputs :=
  everySurvivorTupleCaught_of_circuitHardness_internal
    target inputs hfits hhard

end AntiChecker

end Complexity
