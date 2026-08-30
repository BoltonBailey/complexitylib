/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Defs
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Internal

/-!
# Finite circuit-code enumeration

This module supplies a canonical finite domain for anti-checker survivor
counts. It enumerates all bit strings within the circuit-code length bound and
filters them to well-formed circuits within a size threshold. The resulting set
covers every small typed circuit, has an explicit cardinality bound, and turns
worst-case circuit hardness into the pointwise-failure premise needed by finite
anti-checker extraction.

This exhaustive bound is a baseline, not the quantitative Anti-Checker Lemma:
the later approximate-counting argument must compress the extracted sample list
to the lemma's much smaller target length.
-/


public section

namespace Complexity

namespace AntiChecker

/-- Exact-length code enumeration contains precisely the lists of that
length. -/
theorem mem_codesOfLength_iff {length : ℕ} {code : List Bool} :
    code ∈ codesOfLength length ↔ code.length = length :=
  mem_codesOfLength_iff_internal

/-- There are exactly `2 ^ length` Boolean codes of a fixed length. -/
theorem card_codesOfLength (length : ℕ) :
    (codesOfLength length).card = 2 ^ length :=
  card_codesOfLength_internal length

/-- Bounded-length code enumeration contains precisely the lists within the
bound. -/
theorem mem_codesUpTo_iff {bound : ℕ} {code : List Bool} :
    code ∈ codesUpTo bound ↔ code.length ≤ bound :=
  mem_codesUpTo_iff_internal

/-- The number of Boolean codes up to a length bound is at most the next power
of two. -/
theorem card_codesUpTo_le (bound : ℕ) :
    (codesUpTo bound).card ≤ 2 ^ (bound + 1) :=
  card_codesUpTo_le_internal bound

/-- Candidate membership splits into the code-length bound and decoded
small-circuit validity. -/
theorem mem_candidateCodes_iff {arity threshold : ℕ}
    {code : List Bool} :
    code ∈ candidateCodes arity threshold ↔
      code.length ≤ codeLengthBound arity threshold ∧
        IsSmallCircuitCode arity threshold code :=
  mem_candidateCodes_iff_internal

/-- The canonical candidate circuit-code domain has an explicit exponential
cardinality bound. -/
theorem card_candidateCodes_le (arity threshold : ℕ) :
    (candidateCodes arity threshold).card ≤
      2 ^ (codeLengthBound arity threshold + 1) :=
  card_candidateCodes_le_internal arity threshold

/-- Every typed circuit within the size threshold has its canonical encoding
in the candidate domain. -/
theorem candidateCodes_coversThreshold (arity threshold : ℕ)
    [NeZero arity] :
    CoversThreshold (arity := arity) threshold
      (candidateCodes arity threshold) :=
  candidateCodes_coversThreshold_internal arity threshold

/-- If the target has no circuit within the threshold, every canonical
candidate code disagrees with it somewhere. -/
theorem candidateCodes_allFailSomewhere {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    AllFailSomewhere target (candidateCodes arity threshold) :=
  candidateCodes_allFailSomewhere_internal target hhard

/-- Exhaustive finite extraction gives an anti-checker no longer than the
canonical candidate-code domain. -/
theorem exists_isFor_length_le_candidateCard {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ (candidateCodes arity threshold).card ∧
        IsFor target threshold inputs :=
  exists_isFor_length_le_candidateCard_internal target hhard

/-- Fully numerical exhaustive bound for finite anti-checker extraction. -/
theorem exists_isFor_length_le_codeBound {arity threshold : ℕ}
    [NeZero arity] (target : BitString arity → Bool)
    (hhard :
      ¬ (MCSP.Instance.ofFunction arity threshold target).HasCircuitAtMost) :
    ∃ inputs : List (BitString arity),
      inputs.length ≤ 2 ^ (codeLengthBound arity threshold + 1) ∧
        IsFor target threshold inputs :=
  exists_isFor_length_le_codeBound_internal target hhard

end AntiChecker

end Complexity
