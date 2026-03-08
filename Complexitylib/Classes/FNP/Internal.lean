import Complexitylib.Classes.FNP.Defs
import Complexitylib.Classes.P.Internal
import Mathlib.Analysis.Asymptotics.Defs

/-!
# FNP and TFNP — Internal proofs

Helper lemmas for `tagRelation` used by the surface-layer theorem
`tfnp_of_np_conp_witnesses`.
-/

open Complexity Asymptotics Filter

/-- The combined relation is polynomially balanced when both components are. -/
theorem tagRelation_polyBalanced {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : PolyBalanced R₁) (h₂ : PolyBalanced R₂) :
    PolyBalanced (tagRelation R₁ R₂) := by
  obtain ⟨p₁, hb₁⟩ := h₁
  obtain ⟨p₂, hb₂⟩ := h₂
  refine ⟨p₁ + p₂, ?_⟩
  intro x y hR
  simp only [tagRelation] at hR
  cases hR with
  | inl h => have := hb₁ x y h; simp [Polynomial.eval_add]; omega
  | inr h => have := hb₂ x y h; simp [Polynomial.eval_add]; omega

/-- If both pair languages are in P, so is the pair language of the combined
    relation. Since `tagRelation R₁ R₂ = R₁ ∨ R₂`, the pair language is
    `pairLang R₁ ∪ pairLang R₂`, and P is closed under union. -/
theorem tagRelation_pairLang_in_P {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : pairLang R₁ ∈ P) (h₂ : pairLang R₂ ∈ P) :
    pairLang (tagRelation R₁ R₂) ∈ P := by
  -- pairLang (tagRelation R₁ R₂) = pairLang R₁ ∪ pairLang R₂
  have heq : pairLang (tagRelation R₁ R₂) = pairLang R₁ ∪ pairLang R₂ := by
    ext z; simp only [pairLang, tagRelation, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨x, y, rfl, h | h⟩
      · exact Or.inl ⟨x, y, rfl, h⟩
      · exact Or.inr ⟨x, y, rfl, h⟩
    · rintro (⟨x, y, rfl, h⟩ | ⟨x, y, rfl, h⟩)
      · exact ⟨x, y, rfl, Or.inl h⟩
      · exact ⟨x, y, rfl, Or.inr h⟩
  rw [heq]
  -- Extract polynomial degrees from P = ⋃ k, DTIME(· ^ k)
  obtain ⟨d₁, hd₁⟩ := Set.mem_iUnion.mp h₁
  obtain ⟨d₂, hd₂⟩ := Set.mem_iUnion.mp h₂
  -- Apply DTIME_union and embed into P
  apply Set.mem_iUnion.mpr
  obtain ⟨k, tm, f, hdf, hfo⟩ := DTIME_union hd₁ hd₂
  refine ⟨max d₁ d₂, k, tm, f, hdf, hfo.trans ?_⟩
  -- (n^d₁ + n^d₂) =O n^(max d₁ d₂)
  show (fun n => ((n ^ d₁ + n ^ d₂ : ℕ) : ℝ)) =O[atTop]
       (fun n => ((n ^ max d₁ d₂ : ℕ) : ℝ))
  apply IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have h1 : n ^ d₁ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn (le_max_left d₁ d₂)
  have h2 : n ^ d₂ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn (le_max_right d₁ d₂)
  have : n ^ d₁ + n ^ d₂ ≤ 2 * n ^ max d₁ d₂ := by omega
  exact_mod_cast this

/-- The tagged relation is in FNP when both components are. -/
theorem tagRelation_in_FNP {R₁ R₂ : List Bool → List Bool → Prop}
    (hR₁ : R₁ ∈ FNP) (hR₂ : R₂ ∈ FNP) :
    tagRelation R₁ R₂ ∈ FNP :=
  ⟨tagRelation_polyBalanced hR₁.1 hR₂.1, tagRelation_pairLang_in_P hR₁.2 hR₂.2⟩
