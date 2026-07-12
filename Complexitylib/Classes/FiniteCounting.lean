/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Finite counting toolkit

Exact cardinality lemmas for the finite sample space `Fin T → Bool` used by the
probabilistic-machine semantics (`NTM.acceptCount`, `NTM.acceptProb`). These are
the reusable combinatorial facts underlying randomized classes, amplification,
and interactive proofs (roadmap track N2).

## Main results

- `card_finArrowBool` — `|Fin T → Bool| = 2 ^ T`
- `blockEquiv` — the split of a length-`a + b` random string into its length-`a`
  prefix and length-`b` suffix, packaged as an `Equiv` (so the projection and
  concatenation maps are inverse by construction)
- `card_filter_exists_le` — the finite union bound: the number of sample points
  satisfying *some* predicate in a finite family is at most the sum of the
  per-predicate counts
- `majority`, `majority_not_of_odd` — strict majority of a Boolean vector and its
  antisymmetry under pointwise negation at odd length
-/

namespace Complexity

/-! ### Cardinality of the random-bit sample space -/

/-- The finite sample space of `T` random bits has `2 ^ T` points. This is the
    denominator in `NTM.acceptProb`. -/
theorem card_finArrowBool (T : ℕ) : Fintype.card (Fin T → Bool) = 2 ^ T := by
  simp

/-- Splitting `T = a + b` random bits multiplies the point counts. -/
theorem card_finArrowBool_add (a b : ℕ) :
    Fintype.card (Fin (a + b) → Bool) = 2 ^ a * 2 ^ b := by
  rw [card_finArrowBool, pow_add]

/-- There are exactly `2 ^ (2 ^ n)` Boolean functions on `n` bits — the number of
    distinct `2 ^ n`-entry truth tables. The base fact for property density in
    natural-proofs arguments. -/
theorem card_boolFunc (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_bool, card_finArrowBool]

/-- There are exactly `2 ^ (n * n)` directed graphs (adjacency matrices) on `n`
    vertices — the number of `n × n` Boolean matrices. The size datum behind
    adjacency-matrix encodings of graph languages such as CLIQUE. -/
theorem card_adjMatrix (n : ℕ) :
    Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
  rw [Fintype.card_fun, card_finArrowBool, Fintype.card_fin, ← pow_mul]

/-- An `n`-vertex adjacency matrix biject with `n²`-bit strings by row-major
    serialization. Packaging this as an `Equiv` gives a canonical encode
    (`adjMatrixEquivBitVec`) and decode (`.symm`) that are inverse by
    construction — the codec behind graph-language encodings. -/
def adjMatrixEquivBitVec (n : ℕ) :
    (Fin n → Fin n → Bool) ≃ (Fin (n * n) → Bool) :=
  (Equiv.curry (Fin n) (Fin n) Bool).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-! ### Block projection and concatenation -/

/-- A length-`a + b` random string is equivalently its length-`a` prefix paired
    with its length-`b` suffix. The forward map is the pair of projections; the
    inverse is concatenation. Packaging this as an `Equiv` proves the projection
    and concatenation maps are mutually inverse. -/
def blockEquiv (a b : ℕ) :
    (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

/-- The prefix projection of a length-`a + b` random string. -/
def blockFst (a b : ℕ) (w : Fin (a + b) → Bool) : Fin a → Bool := (blockEquiv a b w).1

/-- The suffix projection of a length-`a + b` random string. -/
def blockSnd (a b : ℕ) (w : Fin (a + b) → Bool) : Fin b → Bool := (blockEquiv a b w).2

/-- Concatenate a length-`a` prefix and length-`b` suffix into one random string. -/
def blockAppend (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) : Fin (a + b) → Bool :=
  (blockEquiv a b).symm (u, v)

@[simp] theorem blockFst_append (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) :
    blockFst a b (blockAppend a b u v) = u := by
  simp [blockFst, blockAppend]

@[simp] theorem blockSnd_append (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) :
    blockSnd a b (blockAppend a b u v) = v := by
  simp [blockSnd, blockAppend]

@[simp] theorem blockAppend_fst_snd (a b : ℕ) (w : Fin (a + b) → Bool) :
    blockAppend a b (blockFst a b w) (blockSnd a b w) = w := by
  simp [blockAppend, blockFst, blockSnd]

/-! ### Finite union bound -/

/-- The finite union bound: the number of sample points satisfying *some*
    predicate `p i` for `i` in a finite index set `s` is at most the sum over `s`
    of the per-predicate counts. The workhorse behind failure-probability bounds
    over many bad events. -/
theorem card_filter_exists_le {ι α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    (Finset.univ.filter (fun x => ∃ i ∈ s, p i x)).card
      ≤ ∑ i ∈ s, (Finset.univ.filter (p i)).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi, hpix⟩ := hx
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hi, hpix⟩

/-- **The probabilistic method: a perfect seed exists.** If the total number of
    "bad" seeds summed over all inputs is strictly less than the number of seeds,
    then some single seed is good for *every* input simultaneously. This is the
    machine-independent counting core of `BPP ⊆ P/poly` (hardwiring one random
    string that works for all `2ⁿ` inputs of a given length). -/
theorem exists_good_seed {S ι : Type*} [Fintype S] [DecidableEq S]
    (inputs : Finset ι) (bad : ι → Finset S)
    (h : ∑ i ∈ inputs, (bad i).card < Fintype.card S) :
    ∃ s : S, ∀ i ∈ inputs, s ∉ bad i := by
  have hcard : (inputs.biUnion bad).card < Fintype.card S :=
    lt_of_le_of_lt Finset.card_biUnion_le h
  have hne : inputs.biUnion bad ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  exact ⟨s, fun i hi hbad => hs (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)⟩

/-! ### Majority -/

/-- The number of `true` positions of a Boolean vector. -/
def popCount {k : ℕ} (f : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

/-- The strict majority vote of a Boolean vector: `true` iff more than half the
    positions are `true`. -/
def majority {k : ℕ} (f : Fin k → Bool) : Bool := decide (2 * popCount f > k)

/-- `popCount` is bounded by the length. -/
theorem popCount_le {k : ℕ} (f : Fin k → Bool) : popCount f ≤ k := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- A position is either `true` or `true`-after-negation, never both: the two
    `popCount`s sum to the length. -/
theorem popCount_add_popCount_not {k : ℕ} (f : Fin k → Bool) :
    popCount f + popCount (fun i => !f i) = k := by
  have hcongr : Finset.univ.filter (fun i : Fin k => (!f i) = true)
      = Finset.univ.filter (fun i : Fin k => ¬ (f i = true)) := by
    apply Finset.filter_congr
    intro i _
    cases f i <;> simp
  simp only [popCount]
  rw [hcongr, Finset.card_filter_add_card_filter_not]
  simp

/-- `popCount` of the pointwise negation is the complementary count. -/
theorem popCount_not {k : ℕ} (f : Fin k → Bool) :
    popCount (fun i => !f i) = k - popCount f := by
  have h := popCount_add_popCount_not f
  omega

/-- **Antisymmetry of majority under negation at odd length.** When the length
    `k` is odd there are no ties, so negating every bit flips the majority vote. -/
theorem majority_not_of_odd {k : ℕ} (hk : Odd k) (f : Fin k → Bool) :
    majority (fun i => !f i) = !(majority f) := by
  obtain ⟨m, hm⟩ := hk
  have hle := popCount_le f
  simp only [majority, popCount_not]
  by_cases h : 2 * popCount f > k
  · have h1 : ¬ (2 * (k - popCount f) > k) := by omega
    rw [decide_eq_false h1, decide_eq_true h, Bool.not_true]
  · have h1 : 2 * (k - popCount f) > k := by omega
    rw [decide_eq_true h1, decide_eq_false h, Bool.not_false]

end Complexity
