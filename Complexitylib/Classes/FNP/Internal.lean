import Complexitylib.Classes.FNP.Defs

/-!
# FNP and TFNP — Internal proofs

Helper lemmas for `tagRelation` used by the surface-layer theorem
`tfnp_of_np_conp_witnesses`.
-/

/-- The tagged relation is polynomially balanced when both components are. -/
theorem tagRelation_polyBalanced {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : PolyBalanced R₁) (h₂ : PolyBalanced R₂) :
    PolyBalanced (tagRelation R₁ R₂) := by
  obtain ⟨p₁, hb₁⟩ := h₁
  obtain ⟨p₂, hb₂⟩ := h₂
  refine ⟨p₁ + p₂ + Polynomial.C 1, ?_⟩
  intro x y hR
  cases y with
  | nil => simp [tagRelation] at hR
  | cons b w =>
    cases b with
    | true =>
      have := hb₁ x w hR
      simp [Polynomial.eval_add, List.length_cons]; omega
    | false =>
      have := hb₂ x w hR
      simp [Polynomial.eval_add, List.length_cons]; omega

/-- If both pair languages are in P, so is the pair language of the tagged
    relation. Requires constructing a TM that reads the tag bit and dispatches
    to the appropriate verifier. -/
theorem tagRelation_pairLang_in_P {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : pairLang R₁ ∈ P) (h₂ : pairLang R₂ ∈ P) :
    pairLang (tagRelation R₁ R₂) ∈ P := by
  sorry

/-- The tagged relation is in FNP when both components are. -/
theorem tagRelation_in_FNP {R₁ R₂ : List Bool → List Bool → Prop}
    (hR₁ : R₁ ∈ FNP) (hR₂ : R₂ ∈ FNP) :
    tagRelation R₁ R₂ ∈ FNP :=
  ⟨tagRelation_polyBalanced hR₁.1 hR₂.1, tagRelation_pairLang_in_P hR₁.2 hR₂.2⟩
