/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.FiniteCounting
import Complexitylib.Models.TuringMachine
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Finite event probability

The uniform probability of a finite event over `T` random bits, `|E| / 2^T`,
defined once as `eventProb` and related to `Finset.card` and to the existing
rational PTM acceptance probability `NTM.acceptProb` (roadmap track N2).

## Main results

- `eventProb` with `eventProb_nonneg`, `eventProb_le_one`, `eventProb_empty`,
  `eventProb_univ`, the complement identity `eventProb_compl`, and the union
  bound `eventProb_union_le`
- `eventProb_block` — independence across blocks: a prefix/suffix-separable event's
  probability is the product of the two block probabilities
- `NTM.acceptProb_eq_eventProb` — the PTM acceptance probability *is* the event
  probability of its set of accepting choice sequences
-/

namespace Complexity

/-- The uniform probability of a finite event `E ⊆ (Fin T → Bool)`: the fraction
    of the `2^T` random bit strings that lie in `E`. -/
def eventProb {T : ℕ} (E : Finset (Fin T → Bool)) : ℚ := (E.card : ℚ) / 2 ^ T

theorem eventProb_nonneg {T : ℕ} (E : Finset (Fin T → Bool)) : 0 ≤ eventProb E := by
  unfold eventProb; positivity

/-- Every finite event has cardinality at most the size of the sample space. -/
theorem card_le_pow {T : ℕ} (E : Finset (Fin T → Bool)) : E.card ≤ 2 ^ T := by
  have h := Finset.card_le_univ E
  rwa [card_finArrowBool] at h

theorem eventProb_le_one {T : ℕ} (E : Finset (Fin T → Bool)) : eventProb E ≤ 1 := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  have h : (E.card : ℚ) ≤ 2 ^ T := by exact_mod_cast card_le_pow E
  calc eventProb E = (E.card : ℚ) / 2 ^ T := rfl
    _ ≤ (2 ^ T) / 2 ^ T := by gcongr
    _ = 1 := div_self hpos

@[simp] theorem eventProb_empty {T : ℕ} : eventProb (∅ : Finset (Fin T → Bool)) = 0 := by
  simp [eventProb]

@[simp] theorem eventProb_univ {T : ℕ} :
    eventProb (Finset.univ : Finset (Fin T → Bool)) = 1 := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  simp only [eventProb, Finset.card_univ, card_finArrowBool]
  rw [show ((2 ^ T : ℕ) : ℚ) = (2 : ℚ) ^ T by norm_cast]
  exact div_self hpos

/-- The probability of the complement of an event is one minus its probability. -/
theorem eventProb_compl {T : ℕ} (E : Finset (Fin T → Bool)) :
    eventProb Eᶜ = 1 - eventProb E := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  have hcard : (Eᶜ.card : ℚ) = 2 ^ T - E.card := by
    have h1 : Eᶜ.card = 2 ^ T - E.card := by
      rw [Finset.card_compl, card_finArrowBool]
    rw [h1, Nat.cast_sub (card_le_pow E)]
    norm_cast
  unfold eventProb
  rw [hcard, sub_div, div_self hpos]

/-- The **union bound** in probability form: the probability of `E ∪ F` is at
    most the sum of their probabilities. -/
theorem eventProb_union_le {T : ℕ} (E F : Finset (Fin T → Bool)) :
    eventProb (E ∪ F) ≤ eventProb E + eventProb F := by
  unfold eventProb
  rw [← add_div]
  gcongr
  exact_mod_cast Finset.card_union_le E F

/-- **The union bound** over a finite family of events: the probability of the
    union `⋃ᵢ Eᵢ` is at most the sum of the individual probabilities. The
    amplification workhorse — bounding the failure probability across many bad
    events. -/
theorem eventProb_biUnion_le {T : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (E : ι → Finset (Fin T → Bool)) :
    eventProb (s.biUnion E) ≤ ∑ i ∈ s, eventProb (E i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    refine le_trans (eventProb_union_le _ _) ?_
    gcongr

/-- **Independence across blocks (probability form).** For an event that constrains
    the prefix and suffix of a length-`a + b` random string separately, the joint
    probability is the product of the two block probabilities. This is the
    probability-level counterpart of `card_filter_block` and the quantitative engine
    behind error amplification: `k` independent runs multiply their success
    probabilities. -/
theorem eventProb_block {a b : ℕ}
    (P : (Fin a → Bool) → Prop) (Q : (Fin b → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    eventProb (Finset.univ.filter
        (fun w : Fin (a + b) → Bool => P (blockFst a b w) ∧ Q (blockSnd a b w)))
      = eventProb (Finset.univ.filter P) * eventProb (Finset.univ.filter Q) := by
  unfold eventProb
  rw [card_filter_block, pow_add, div_mul_div_comm]
  push_cast
  rfl

/-- Event probability is invariant under any relabeling of the sample space — in
    particular under permuting the bit positions (`Equiv.arrowCongr σ`) — since a
    bijection preserves cardinality. -/
theorem eventProb_map {T : ℕ} (e : (Fin T → Bool) ≃ (Fin T → Bool))
    (E : Finset (Fin T → Bool)) :
    eventProb (E.map e.toEmbedding) = eventProb E := by
  unfold eventProb
  rw [Finset.card_map]

/-- The PTM acceptance probability is exactly the event probability of the set of
    accepting choice sequences: this ties `NTM.acceptProb` to the abstract
    `eventProb` / `Finset.card` layer. -/
theorem NTM.acceptProb_eq_eventProb {n : ℕ} (tm : NTM n) (x : List Bool) (T : ℕ) :
    tm.acceptProb x T =
      eventProb (Finset.univ.filter fun choices : Fin T → Bool =>
        let c' := tm.trace T choices (tm.initCfg x)
        c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one) := by
  rfl

end Complexity
