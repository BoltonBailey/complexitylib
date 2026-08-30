/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.EventProb

/-!
# Lautemann's covering lemma

The combinatorial core of the Sipser–Lautemann theorem, stated for an event
`E` in the seed space `Fin m → Bool` and the XOR shift action on that space.
-/

@[expose] public section

namespace Complexity

namespace Lautemann

variable {m t k : ℕ}

/-- XOR shift of a seed by a vector. -/
def shift (r u : Fin m → Bool) : Fin m → Bool := fun i => xor (r i) (u i)

@[simp] theorem shift_shift (r u : Fin m → Bool) : shift (shift r u) u = r := by
  funext i
  simp [shift]

/-- The shift action is symmetric in its two arguments. -/
theorem shift_comm (r u : Fin m → Bool) : shift r u = shift u r := by
  funext i
  simp [shift, Bool.xor_comm]

/-- Shifting by a fixed vector is an involutive equivalence of the seed space. -/
def shiftEquiv (u : Fin m → Bool) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun r := shift r u
  invFun r := shift r u
  left_inv r := shift_shift r u
  right_inv r := shift_shift r u

/-- The `t` shifts `u 0, …, u (t-1)` of the event `E` cover the whole seed
space: every seed lands in `E` after at least one of them. -/
def Covers (E : Finset (Fin m → Bool)) (u : Fin t → Fin m → Bool) : Prop :=
  ∀ r, ∃ i, shift r (u i) ∈ E

/-- Shifting is measure preserving: the seeds carried into `E` by a fixed
shift are as many as the elements of `E`. -/
theorem card_filter_shift_mem (E : Finset (Fin m → Bool)) (u : Fin m → Bool) :
    (Finset.univ.filter fun r => shift r u ∈ E).card = E.card := by
  have hset : (Finset.univ.filter fun r => shift r u ∈ E) = E.image (fun v => shift v u) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨shift r u, h, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
  have hinj : Function.Injective (fun v : Fin m → Bool => shift v u) := by
    intro a b hab
    have := congrArg (fun w => shift w u) hab
    simpa using this
  rw [hset, Finset.card_image_of_injective _ hinj]

/-- The number of seeds is `2 ^ m`. -/
theorem card_univ_seed : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  rw [Finset.card_univ, card_finArrowBool]

/-- The number of `t`-tuples of shift vectors is `(2 ^ m) ^ t`. -/
theorem card_univ_shifts :
    (Finset.univ : Finset (Fin t → Fin m → Bool)).card = (2 ^ m) ^ t := by
  rw [Finset.card_univ, Fintype.card_fun, card_finArrowBool, Fintype.card_fin]

/-- **Existence of covering shifts.** If the complement of `E` is small enough
that `2 ^ m` translates of its `m`-fold product miss the whole shift space,
some `m`-tuple of shifts covers every seed. This is the counting form of the
probabilistic argument: a uniformly random tuple fails to cover a fixed seed
with probability `(1 - eventProb E) ^ m`, and a union bound over the `2 ^ m`
seeds leaves a covering tuple. -/
theorem exists_covers_of_card (E : Finset (Fin m → Bool))
    (h : 2 ^ m * (2 ^ m - E.card) ^ t < (2 ^ m) ^ t) :
    ∃ u : Fin t → Fin m → Bool, Covers E u := by
  classical
  set bad : Finset (Fin t → Fin m → Bool) :=
    Finset.univ.filter (fun u => ¬ Covers E u) with hbad
  have hsub : bad ⊆ Finset.univ.biUnion (fun r : Fin m → Bool =>
      Fintype.piFinset (fun _ : Fin t => Finset.univ.filter fun v => shift r v ∉ E)) := by
    intro u hu
    simp only [hbad, Finset.mem_filter, Finset.mem_univ, true_and, Covers, not_forall] at hu
    obtain ⟨r, hr⟩ := hu
    simp only [not_exists] at hr
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, by
      simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i => hr i⟩
  have hfiber : ∀ r : Fin m → Bool,
      (Fintype.piFinset (fun _ : Fin t => Finset.univ.filter fun v => shift r v ∉ E)).card
        = (2 ^ m - E.card) ^ t := by
    intro r
    rw [Fintype.card_piFinset]
    have hone : (Finset.univ.filter fun v => shift r v ∉ E).card = 2 ^ m - E.card := by
      have : (Finset.univ.filter fun v => shift r v ∉ E)
          = Finset.univ.filter fun v => shift v r ∈ Eᶜ := by
        ext v
        simp [shift_comm v r]
      rw [this, card_filter_shift_mem Eᶜ r, Finset.card_compl, card_finArrowBool]
    simp [hone]
  have hcard : bad.card < (2 ^ m) ^ t := by
    calc bad.card
        ≤ (Finset.univ.biUnion (fun r : Fin m → Bool =>
            Fintype.piFinset (fun _ : Fin t => Finset.univ.filter fun v => shift r v ∉ E))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ _r : Fin m → Bool, (2 ^ m - E.card) ^ t := by
          refine le_trans (Finset.card_biUnion_le) ?_
          exact Finset.sum_le_sum fun r _ => le_of_eq (hfiber r)
      _ = 2 ^ m * (2 ^ m - E.card) ^ t := by
          rw [Finset.sum_const, card_univ_seed]
          simp
      _ < (2 ^ m) ^ t := h
  have hex : ∃ u : Fin t → Fin m → Bool, u ∉ bad := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : (Finset.univ : Finset (Fin t → Fin m → Bool)) ⊆ bad := fun u _ => hcon u
    have hle := Finset.card_le_card this
    rw [card_univ_shifts] at hle
    omega
  obtain ⟨u, hu⟩ := hex
  refine ⟨u, ?_⟩
  simpa [hbad] using hu

/-- **No covering when the event is small.** If `t` copies of `E` cannot fill
the seed space by cardinality alone, no tuple of `t` shifts covers it. -/
theorem not_covers_of_card (E : Finset (Fin m → Bool)) (h : t * E.card < 2 ^ m)
    (u : Fin t → Fin m → Bool) : ¬ Covers E u := by
  classical
  intro hcov
  have hsub : (Finset.univ : Finset (Fin m → Bool)) ⊆
      Finset.univ.biUnion (fun i : Fin t => Finset.univ.filter fun r => shift r (u i) ∈ E) := by
    intro r _
    obtain ⟨i, hi⟩ := hcov r
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hi]⟩
  have hle := Finset.card_le_card hsub
  rw [card_univ_seed] at hle
  have hbound : (Finset.univ.biUnion (fun i : Fin t =>
      Finset.univ.filter fun r => shift r (u i) ∈ E)).card ≤ t * E.card := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ i : Fin t, (Finset.univ.filter fun r => shift r (u i) ∈ E).card
        = ∑ _i : Fin t, E.card := by
          exact Finset.sum_congr rfl fun i _ => card_filter_shift_mem E (u i)
      _ = t * E.card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp
      _ ≤ t * E.card := le_rfl
  omega

/-! ## Probability form -/

/-- An event of probability at most `2 ^ (-k)` has at most `2 ^ (m - k)`
elements, in the multiplication-only form used below. -/
theorem card_mul_two_pow_le (E : Finset (Fin m → Bool)) (h : eventProb E ≤ 1 / 2 ^ k) :
    E.card * 2 ^ k ≤ 2 ^ m := by
  have h2m : (0 : ℚ) < 2 ^ m := by positivity
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hq : (E.card : ℚ) * 2 ^ k ≤ 2 ^ m := by
    rw [eventProb, div_le_div_iff₀ h2m h2k] at h
    linarith
  exact_mod_cast hq

/-- **Lautemann's covering lemma, completeness direction.** If the event `E`
fails with probability at most `2 ^ (-k)`, and the seed length `m` is below
`k * t`, then some `t` shifts of `E` cover the whole seed space. Since the
failure probability enters as its `t`-th power against a union bound over the
`2 ^ m` seeds, any `k ≥ 2` suffices at `t ≥ m`. -/
theorem exists_covers_of_eventProb_compl_le (E : Finset (Fin m → Bool))
    (hmt : m < k * t) (h : eventProb Eᶜ ≤ 1 / 2 ^ k) :
    ∃ u : Fin t → Fin m → Bool, Covers E u := by
  have hc : Eᶜ.card = 2 ^ m - E.card := by rw [Finset.card_compl, card_finArrowBool]
  have hle : Eᶜ.card * 2 ^ k ≤ 2 ^ m := card_mul_two_pow_le Eᶜ h
  refine exists_covers_of_card E ?_
  rw [← hc]
  by_contra hcon
  simp only [not_lt] at hcon
  have hpos : 0 < (2 ^ m : ℕ) ^ t := Nat.pow_pos (Nat.two_pow_pos m)
  have key : (2 ^ m : ℕ) ^ t * 2 ^ (k * t) ≤ (2 ^ m : ℕ) ^ t * 2 ^ m := by
    calc (2 ^ m : ℕ) ^ t * 2 ^ (k * t)
        ≤ (2 ^ m * Eᶜ.card ^ t) * 2 ^ (k * t) := Nat.mul_le_mul_right _ hcon
      _ = 2 ^ m * (Eᶜ.card * 2 ^ k) ^ t := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ 2 ^ m * (2 ^ m) ^ t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle t)
      _ = (2 ^ m : ℕ) ^ t * 2 ^ m := by ring
  have hexp : (2 : ℕ) ^ (k * t) ≤ 2 ^ m := Nat.le_of_mul_le_mul_left key hpos
  have hkm : k * t ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp hexp
  omega

/-- **Lautemann's covering lemma, soundness direction.** If the event `E` holds
with probability at most `2 ^ (-k)` and the number of shifts `t` is below
`2 ^ k`, then no `t` shifts of `E` cover the seed space. -/
theorem not_covers_of_eventProb_le (E : Finset (Fin m → Bool)) (hk : t < 2 ^ k)
    (h : eventProb E ≤ 1 / 2 ^ k) (u : Fin t → Fin m → Bool) : ¬ Covers E u := by
  refine not_covers_of_card E ?_ u
  have hle := card_mul_two_pow_le E h
  rcases Nat.eq_zero_or_pos E.card with h0 | h0
  · simp [h0, Nat.two_pow_pos m]
  · calc t * E.card < 2 ^ k * E.card := (Nat.mul_lt_mul_right h0).mpr hk
      _ = E.card * 2 ^ k := Nat.mul_comm _ _
      _ ≤ 2 ^ m := hle

end Lautemann

end Complexity
