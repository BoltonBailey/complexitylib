/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Internal
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Extraction
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Approximation
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.GoodString

/-!
# Finite anti-checkers

This module exposes finite anti-checkers as concrete lists of inputs. A list
anti-checks a target at threshold `s` when every circuit of size at most `s`
disagrees with the target on a listed input. The predicate is monotone under
adding inputs, antitone in the circuit threshold, and invariant under list
permutation, so the list acts semantically as a multiset.

The main bridge is exact: the canonical SuccinctMCSP instance labelled by the
target rejects if and only if its input list is an anti-checker. The extraction
layer obtains such a list from any finite covering set of circuit codes whose
members all fail somewhere, using at most one disagreement input per code. The
enumeration layer supplies a canonical covering set with an explicit exhaustive
cardinality bound. Its survivor-count layer identifies anti-checking exactly
with reducing the number of consistent canonical candidates to zero. Relative
estimates of that count use an exact cross-multiplied natural-number contract,
and minimizing those estimates preserves survivor shrinkage with explicit loss.
The good-string layer supplies exact tuple counts and finite averaging.
-/


public section

namespace Complexity

namespace AntiChecker

/-- Anti-checking is equivalent to ruling out agreement on the whole list for
every circuit within the threshold. -/
theorem isFor_iff_forall_not_agreesOn {arity : ℕ}
    [NeZero arity] (target : BitString arity → Bool) (threshold : ℕ)
    (inputs : List (BitString arity)) :
    IsFor target threshold inputs ↔
      ∀ (internalGates : ℕ)
          (circuit : Circuit Basis.andOr2 arity 1 internalGates),
        circuit.size ≤ threshold → ¬ AgreesOn circuit target inputs :=
  isFor_iff_forall_not_agreesOn_internal target threshold inputs

/-- Adding possible counterexample inputs preserves anti-checking. -/
theorem IsFor.inputs_mono {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {threshold : ℕ}
    {first second : List (BitString arity)}
    (hsub : ∀ input ∈ first, input ∈ second)
    (hanti : IsFor target threshold first) :
    IsFor target threshold second :=
  isFor_inputs_mono_internal hsub hanti

/-- An anti-checker for a larger circuit class also anti-checks every smaller
threshold. -/
theorem IsFor.threshold_anti {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {first second : ℕ}
    {inputs : List (BitString arity)} (hthreshold : first ≤ second)
    (hanti : IsFor target second inputs) :
    IsFor target first inputs :=
  isFor_threshold_anti_internal hthreshold hanti

/-- Reordering a list does not change whether it is an anti-checker. -/
theorem isFor_perm {arity : ℕ} [NeZero arity]
    {target : BitString arity → Bool} {threshold : ℕ}
    {first second : List (BitString arity)} (hperm : first.Perm second) :
    IsFor target threshold first ↔ IsFor target threshold second :=
  isFor_perm_internal hperm

/-- A circuit satisfies every canonical sample induced by an input list exactly
when it agrees with the target throughout that list. -/
theorem samplesFunction_ofInputs_iff_agreesOn {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) {internalGates : ℕ}
    (circuit : Circuit Basis.andOr2 arity 1 internalGates) :
    (SuccinctMCSP.Instance.ofInputs threshold target inputs).SamplesFunction
        (fun input => circuit.eval input 0) ↔
      AgreesOn circuit target inputs :=
  samplesFunction_ofInputs_iff_agreesOn_internal target inputs circuit

/-- A list is an anti-checker exactly when no circuit within the threshold
matches all samples in the corresponding typed SuccinctMCSP instance. -/
theorem isFor_iff_not_hasCircuitAtMost {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    IsFor target threshold inputs ↔
      ¬ (SuccinctMCSP.Instance.ofInputs threshold target inputs).HasCircuitAtMost :=
  isFor_iff_not_hasCircuitAtMost_internal target inputs

/-- Exact encoded rejection bridge between anti-checkers and SuccinctMCSP. -/
theorem encode_not_mem_iff_isFor {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (inputs : List (BitString arity)) :
    (SuccinctMCSP.Instance.ofInputs threshold target inputs).encode ∉
        Complexity.SuccinctMCSP ↔
      IsFor target threshold inputs :=
  encode_not_mem_iff_isFor_internal target inputs

end AntiChecker

end Complexity
