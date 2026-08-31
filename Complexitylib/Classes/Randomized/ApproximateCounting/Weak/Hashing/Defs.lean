/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Defs
public import Complexitylib.Classes.Randomized.Hashing.Affine
public import Complexitylib.Classes.Randomized.Hashing.Amplification.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Hashing-based weak approximate counting -- definitions

Each of the `domainWidth + 4` occupancy probes receives an independent block
of a single flat random seed. The block widths vary with the hash output width;
`finSigmaFinEquiv` gives a canonical row-major encoding without padding.
-/


@[expose] public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

/-- Random bits used by the amplified occupancy probe at one hash width. -/
def levelSeedWidth (domainWidth errorBits : ℕ) (level : Level domainWidth) : ℕ :=
  PairwiseIndependentHash.majoritySeedWidth
    (PairwiseIndependentHash.affineSeedWidth domainWidth level.val) errorBits

/-- Total random bits used by all weak-estimator occupancy probes. -/
def hashingSeedWidth (domainWidth errorBits : ℕ) : ℕ :=
  ∑ level : Level domainWidth, levelSeedWidth domainWidth errorBits level

/-- Canonical equivalence between the flat weak-estimator seed and its
variable-width per-level blocks. -/
def hashingSeedEquiv (domainWidth errorBits : ℕ) :
    BitString (hashingSeedWidth domainWidth errorBits) ≃
      ∀ level : Level domainWidth,
        BitString (levelSeedWidth domainWidth errorBits level) :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry fun _ _ => Bool)

/-- The independent seed block assigned to one hash output width. -/
def levelSeed {domainWidth errorBits : ℕ}
    (seed : BitString (hashingSeedWidth domainWidth errorBits))
    (level : Level domainWidth) :
    BitString (levelSeedWidth domainWidth errorBits level) :=
  hashingSeedEquiv domainWidth errorBits seed level

/-- Amplified affine-hash occupancy answers at every output width. Level zero
is evaluated directly, since its unique hash cell is the entire set. -/
def hashingResponses {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth))
    (seed : BitString (hashingSeedWidth domainWidth errorBits)) :
    Level domainWidth → Bool :=
  fun level =>
    if level.val = 0 then
      decide set.Nonempty
    else
      (PairwiseIndependentHash.affine domainWidth level.val).majorityNonempty
        set (fun _ => false) errorBits (levelSeed seed level)

/-- The hashing-based weak cardinality estimate. -/
def hashingEstimate {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth))
    (seed : BitString (hashingSeedWidth domainWidth errorBits)) : ℕ :=
  estimate (hashingResponses set seed)

/-- Master seeds on which one fixed occupancy level violates its promised
high- or low-mean response. -/
def badLevelEvent {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth)) (level : Level domainWidth) :
    Finset (BitString (hashingSeedWidth domainWidth errorBits)) :=
  Finset.univ.filter fun seed =>
    (8 * 2 ^ level.val ≤ set.card ∧ hashingResponses set seed level = false) ∨
      (8 * set.card ≤ 2 ^ level.val ∧ hashingResponses set seed level = true)

/-- Master seeds on which at least one occupancy level violates its response
contract. -/
def badHashingEvent {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth)) :
    Finset (BitString (hashingSeedWidth domainWidth errorBits)) :=
  Finset.univ.biUnion fun level => badLevelEvent set level

/-- Master seeds whose complete response vector satisfies the weak estimator's
simultaneous accuracy contract. -/
def goodHashingEvent {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth)) :
    Finset (BitString (hashingSeedWidth domainWidth errorBits)) :=
  Finset.univ.filter fun seed =>
    ResponsesAccurate (cardinality := set.card) (hashingResponses set seed)

/-- Master seeds on which the hashing-based estimate is within factor `16` of
the exact set cardinality. -/
def factorApproximationEvent {domainWidth errorBits : ℕ}
    (set : Finset (BitString domainWidth)) :
    Finset (BitString (hashingSeedWidth domainWidth errorBits)) :=
  Finset.univ.filter fun seed =>
    IsFactorApproximation 16 set.card (hashingEstimate set seed)

end Weak

end ApproximateCounting

end Complexity
