/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic

/-!
# Counting permutations that keep a set inside a set

The expander existence proof needs one combinatorial estimate: of the `n!`
permutations of `Fin n`, at most `descFactorial s k · (n - k)!` map a given
`k`-element set inside a given `s`-element set.

The proof is the obvious one, made precise. Restricting a permutation to `K`
gives an injection into `S`; there are `descFactorial s k` of those. Two
permutations with the same restriction differ only outside `K`, where they are
injections from an `(n - k)`-set into the complement of the common image —
another `(n - k)`-set — so each restriction is shared by at most `(n - k)!`
permutations.

## Main results

- `Complexity.card_perm_mapsTo_le` — the estimate
- `Complexity.card_perm_escape_le` — its consequence for the escape count:
  few permutations move only a small part of `S` out of `S`
-/

@[expose] public section

namespace Complexity

open Finset

variable {n : ℕ}

/-- How many points of `S` the permutation `σ` sends outside `S`. -/
noncomputable def escape (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => σ v ∉ S).card

/-! ### Restrictions of a permutation -/

/-- The permutations mapping `K` into `S`. -/
noncomputable def permsInto (S K : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => ∀ v ∈ K, σ v ∈ S

/-- The restrictions that can occur: injective maps of `K` into `S`. -/
noncomputable def restrs (S K : Finset (Fin n)) : Finset ({x // x ∈ K} → Fin n) :=
  Finset.univ.filter fun f => Function.Injective f ∧ ∀ v, f v ∈ S

theorem mem_restrs {S K : Finset (Fin n)} {f : {x // x ∈ K} → Fin n} (hf : f ∈ restrs S K) :
    Function.Injective f ∧ ∀ v, f v ∈ S := by
  have := hf
  rw [restrs, Finset.mem_filter] at this
  exact this.2

/-- **There are few restrictions.** -/
theorem card_restrs_le (S K : Finset (Fin n)) :
    (restrs S K).card ≤ S.card.descFactorial K.card := by
  classical
  have hinj : Function.Injective (fun f : {f // f ∈ restrs S K} =>
      (⟨fun v => ⟨f.1 v, (mem_restrs f.2).2 v⟩, fun a b hab =>
        (mem_restrs f.2).1 (congrArg Subtype.val hab)⟩ :
        {x // x ∈ K} ↪ {x // x ∈ S})) := by
    intro f g h
    have h' : ∀ v, f.1 v = g.1 v := by
      intro v
      have := DFunLike.congr_fun h v
      exact congrArg Subtype.val this
    exact Subtype.ext (funext h')
  have hle := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe] at hle

/-- The values of a restriction. -/
noncomputable def restrImage {K : Finset (Fin n)} (f : {x // x ∈ K} → Fin n) : Finset (Fin n) :=
  Finset.univ.image f

theorem card_restrImage {S K : Finset (Fin n)} {f : {x // x ∈ K} → Fin n}
    (hf : f ∈ restrs S K) : (restrImage f).card = K.card := by
  rw [restrImage, Finset.card_image_of_injective _ (mem_restrs hf).1, Finset.card_univ,
    Fintype.card_coe]

/-- **Each restriction is shared by few permutations.** -/
theorem card_fiber_le (S K : Finset (Fin n)) (f : {x // x ∈ K} → Fin n)
    (hf : f ∈ restrs S K) :
    ((permsInto S K).filter fun σ => (fun v : {x // x ∈ K} => σ v) = f).card
      ≤ Nat.factorial (n - K.card) := by
  classical
  set R : Finset (Fin n) := Finset.univ \ restrImage f with hR
  have hRcard : R.card = n - K.card := by
    rw [hR, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      card_restrImage hf]
  -- a permutation in the fibre maps the complement of `K` into `R`
  have hmaps : ∀ σ ∈ (permsInto S K).filter fun σ => (fun v : {x // x ∈ K} => σ v) = f,
      ∀ v : {x // x ∉ K}, σ v.1 ∈ R := by
    intro σ hσ v
    rw [Finset.mem_filter] at hσ
    rw [hR, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [restrImage, Finset.mem_image]
    rintro ⟨w, -, hw⟩
    have hfw : f w = σ w.1 := (congrFun hσ.2 w).symm
    rw [hfw] at hw
    have : (w : Fin n) = v.1 := σ.injective hw
    exact v.2 (this ▸ w.2)
  have hinj : Function.Injective (fun σ : {σ // σ ∈ (permsInto S K).filter
      fun σ => (fun v : {x // x ∈ K} => σ v) = f} =>
      (⟨fun v => ⟨σ.1 v.1, hmaps σ.1 σ.2 v⟩, fun a b hab => by
        have : σ.1 a.1 = σ.1 b.1 := congrArg Subtype.val hab
        exact Subtype.ext (σ.1.injective this)⟩ :
        {x // x ∉ K} ↪ {x // x ∈ R})) := by
    intro σ τ h
    have hout : ∀ v : Fin n, v ∉ K → σ.1 v = τ.1 v := by
      intro v hv
      have := DFunLike.congr_fun h ⟨v, hv⟩
      exact congrArg Subtype.val this
    have hin : ∀ v : Fin n, v ∈ K → σ.1 v = τ.1 v := by
      intro v hv
      have hσ := σ.2
      have hτ := τ.2
      rw [Finset.mem_filter] at hσ hτ
      have h1 : σ.1 v = f ⟨v, hv⟩ := congrFun hσ.2 ⟨v, hv⟩
      have h2 : τ.1 v = f ⟨v, hv⟩ := congrFun hτ.2 ⟨v, hv⟩
      rw [h1, h2]
    refine Subtype.ext (Equiv.ext fun v => ?_)
    by_cases hv : v ∈ K
    · exact hin v hv
    · exact hout v hv
  have hcompl : Fintype.card {x : Fin n // x ∉ K} = n - K.card := by
    have h := Fintype.card_subtype_compl (p := fun x : Fin n => x ∈ K)
    rw [Fintype.card_fin, Fintype.card_coe] at h
    exact h
  have hle := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_coe] at hle
  rw [hRcard, hcompl, Nat.descFactorial_self] at hle
  exact hle

/-- **The estimate.** -/
theorem card_perm_mapsTo_le (S K : Finset (Fin n)) :
    (permsInto S K).card ≤ S.card.descFactorial K.card * Nat.factorial (n - K.card) := by
  classical
  have hfib : ∀ σ ∈ permsInto S K, (fun v : {x // x ∈ K} => σ v) ∈ restrs S K := by
    intro σ hσ
    rw [permsInto, Finset.mem_filter] at hσ
    rw [restrs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun a b hab => Subtype.ext (σ.injective hab),
      fun v => hσ.2 v.1 v.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  calc ∑ f ∈ restrs S K, ((permsInto S K).filter
        fun σ => (fun v : {x // x ∈ K} => σ v) = f).card
      ≤ ∑ _f ∈ restrs S K, Nat.factorial (n - K.card) :=
        Finset.sum_le_sum fun f hf => card_fiber_le S K f hf
    _ = (restrs S K).card * Nat.factorial (n - K.card) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ S.card.descFactorial K.card * Nat.factorial (n - K.card) :=
        Nat.mul_le_mul_right _ (card_restrs_le S K)

/-! ### Permutations with little escape -/

/-- **Few permutations move only a little of `S` out of `S`.** Such a
permutation keeps a `(s - t)`-element subset of `S` inside `S`, and there are
few subsets and, by `card_perm_mapsTo_le`, few permutations for each. -/
theorem card_perm_escape_le (S : Finset (Fin n)) (t : ℕ) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => escape σ S ≤ t).card
      ≤ S.card.choose (S.card - t)
        * (S.card.descFactorial (S.card - t) * Nat.factorial (n - (S.card - t))) := by
  classical
  set k := S.card - t with hk
  have hsub : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => escape σ S ≤ t)
      ⊆ (S.powersetCard k).biUnion fun K => permsInto S K := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    set A : Finset (Fin n) := S.filter fun v => σ v ∈ S with hA
    have hcompl : A.card + escape σ S = S.card := by
      rw [hA, escape]
      exact Finset.card_filter_add_card_filter_not _
    have hAk : k ≤ A.card := by omega
    obtain ⟨K, hKA, hKcard⟩ := Finset.exists_subset_card_eq hAk
    rw [Finset.mem_biUnion]
    refine ⟨K, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨fun v hv => ?_, hKcard⟩
      have := hKA hv
      rw [hA, Finset.mem_filter] at this
      exact this.1
    · rw [permsInto, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
      have := hKA hv
      rw [hA, Finset.mem_filter] at this
      exact this.2
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  have hbound : ∀ K ∈ S.powersetCard k,
      (permsInto S K).card ≤ S.card.descFactorial k * Nat.factorial (n - k) := by
    intro K hK
    rw [Finset.mem_powersetCard] at hK
    have := card_perm_mapsTo_le S K
    rw [hK.2] at this
    exact this
  calc ∑ K ∈ S.powersetCard k, (permsInto S K).card
      ≤ ∑ _K ∈ S.powersetCard k, S.card.descFactorial k * Nat.factorial (n - k) :=
        Finset.sum_le_sum hbound
    _ = (S.powersetCard k).card * (S.card.descFactorial k * Nat.factorial (n - k)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = S.card.choose k * (S.card.descFactorial k * Nat.factorial (n - k)) := by
        rw [Finset.card_powersetCard]

end Complexity
