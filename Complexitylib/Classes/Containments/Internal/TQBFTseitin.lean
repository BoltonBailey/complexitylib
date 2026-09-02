/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.CNFArith

/-!
# Tseitin encoding of a quantifier-free formula

⚠️ Unreviewed by Bolton

A quantifier-free `QBF` is turned into a CNF over its variables and fresh auxiliary variables,
one per connective, together with an output literal: every assignment satisfying the clauses
gives the output literal the formula's value (`tseitin_sound`), and every assignment of the
formula's variables extends to one satisfying the clauses (`tseitin_complete`). Existentially
closing the auxiliaries therefore reproduces the formula (`eval_exs_tseitin`) — which is how a
prenex CNF instance absorbs an arbitrary matrix.

## Main definitions

- `QBF.exs` — existential closure over a range of variables
- `QBF.tseitin` — clauses, output literal, next fresh variable

## Main results

- `QBF.eval_exs_iff`, `QBF.tseitin_sound`, `QBF.tseitin_complete`, `QBF.eval_exs_tseitin`
- `QBF.eval_disjLits`, `QBF.eval_exs_orCNF` — guarding and combining clause lists
-/

@[expose] public section

namespace Complexity

namespace QBF

/-! ## Clause semantics -/

theorem eval_litQBF (β : ℕ → Bool) (l : CLit) : eval β (litQBF l) = (β l.2 == l.1) := by
  rcases l with ⟨s, i⟩
  cases s <;> cases h : β i <;> simp [litQBF, eval, h]

theorem eval_clauseQBF_iff (β : ℕ → Bool) (c : List CLit) :
    eval β (clauseQBF c) = true ↔ ∃ l ∈ c, eval β (litQBF l) = true := by
  induction c with
  | nil => simp [clauseQBF]
  | cons l c ih =>
      rw [clauseQBF, List.foldr_cons, eval, ← clauseQBF, Bool.or_eq_true, ih]
      simp

theorem eval_cnfQBF_iff (β : ℕ → Bool) (φ : List (List CLit)) :
    eval β (cnfQBF φ) = true ↔ ∀ c ∈ φ, eval β (clauseQBF c) = true := by
  induction φ with
  | nil => simp [cnfQBF]
  | cons c φ ih =>
      rw [cnfQBF, List.foldr_cons, eval, ← cnfQBF, Bool.and_eq_true, ih]
      simp

theorem eval_cnfQBF_flatMap {A : Type} (β : ℕ → Bool) (l : List A)
    (f : A → List (List CLit)) :
    eval β (cnfQBF (l.flatMap f)) = true ↔ ∀ a ∈ l, eval β (cnfQBF (f a)) = true := by
  simp only [eval_cnfQBF_iff, List.mem_flatMap]
  constructor
  · intro h a ha c hc
    exact h c ⟨a, ha, hc⟩
  · rintro h c ⟨a, ha, hc⟩
    exact h a ha c hc

theorem eval_cnfQBF_append (β : ℕ → Bool) (φ ψ : List (List CLit)) :
    eval β (cnfQBF (φ ++ ψ)) = true ↔ eval β (cnfQBF φ) = true ∧ eval β (cnfQBF ψ) = true := by
  simp only [eval_cnfQBF_iff, List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-! ## Existential closure of a range -/

/-- `∃ x_v ∃ x_{v+1} … ∃ x_{v+n-1}. ψ`. -/
def exs (v : ℕ) : ℕ → QBF → QBF
  | 0, ψ => ψ
  | n + 1, ψ => ex v (exs (v + 1) n ψ)

theorem eval_exs_iff (α : ℕ → Bool) : ∀ (v n : ℕ) (ψ : QBF),
    eval α (exs v n ψ) = true ↔
      ∃ β : ℕ → Bool, (∀ i, (i < v ∨ v + n ≤ i) → β i = α i) ∧ eval β ψ = true
  | v, 0, ψ => by
      simp only [exs]
      constructor
      · intro h
        exact ⟨α, fun _ _ => rfl, h⟩
      · rintro ⟨β, hβ, h⟩
        rwa [eval_eq_of_agree ψ α β fun i _ => (hβ i (by omega)).symm]
  | v, n + 1, ψ => by
      rw [exs, eval_ex_iff]
      constructor
      · rintro ⟨b, hb⟩
        obtain ⟨β, hβ, h⟩ := (eval_exs_iff _ (v + 1) n ψ).mp hb
        refine ⟨β, fun i hi => ?_, h⟩
        rw [hβ i (by omega), Function.update_of_ne (by omega)]
      · rintro ⟨β, hβ, h⟩
        refine ⟨β v, (eval_exs_iff _ (v + 1) n ψ).mpr ⟨β, fun i hi => ?_, h⟩⟩
        by_cases hiv : i = v
        · subst hiv
          simp
        · rw [Function.update_of_ne hiv]
          exact hβ i (by omega)

/-! ## The encoding -/

/-- The complementary literal. -/
def negLit (l : CLit) : CLit := (!l.1, l.2)

theorem eval_litQBF_negLit (β : ℕ → Bool) (l : CLit) :
    eval β (litQBF (negLit l)) = !(eval β (litQBF l)) := by
  rw [eval_litQBF, eval_litQBF, negLit]
  cases l.1 <;> cases β l.2 <;> rfl

/-- **Tseitin.** The clauses, the output literal and the next fresh variable. Quantified
subformulas are treated as `⊥`. -/
def tseitin : QBF → ℕ → List (List CLit) × CLit × ℕ
  | var i, v => ([], (true, i), v)
  | tru, v => ([[(true, v)]], (true, v), v + 1)
  | fls, v => ([[(false, v)]], (true, v), v + 1)
  | neg φ, v =>
      let r := tseitin φ v
      (r.1, negLit r.2.1, r.2.2)
  | conj φ ψ, v =>
      let r₁ := tseitin φ v
      let r₂ := tseitin ψ r₁.2.2
      (r₁.1 ++ r₂.1 ++ [[(false, r₂.2.2), r₁.2.1], [(false, r₂.2.2), r₂.2.1],
        [(true, r₂.2.2), negLit r₁.2.1, negLit r₂.2.1]], (true, r₂.2.2), r₂.2.2 + 1)
  | disj φ ψ, v =>
      let r₁ := tseitin φ v
      let r₂ := tseitin ψ r₁.2.2
      (r₁.1 ++ r₂.1 ++ [[(false, r₂.2.2), r₁.2.1, r₂.2.1], [(true, r₂.2.2), negLit r₁.2.1],
        [(true, r₂.2.2), negLit r₂.2.1]], (true, r₂.2.2), r₂.2.2 + 1)
  | ex _ _, v => ([[(false, v)]], (true, v), v + 1)
  | all _ _, v => ([[(false, v)]], (true, v), v + 1)

theorem tseitin_next_ge : ∀ (φ : QBF) (v : ℕ), v ≤ (tseitin φ v).2.2
  | var _, _ => le_rfl
  | tru, _ => Nat.le_succ _
  | fls, _ => Nat.le_succ _
  | neg φ, v => tseitin_next_ge φ v
  | conj φ ψ, v =>
      le_trans (tseitin_next_ge φ v) (le_trans (tseitin_next_ge ψ _) (Nat.le_succ _))
  | disj φ ψ, v =>
      le_trans (tseitin_next_ge φ v) (le_trans (tseitin_next_ge ψ _) (Nat.le_succ _))
  | ex _ _, _ => Nat.le_succ _
  | all _ _, _ => Nat.le_succ _

/-- The output literal's variable is below the next fresh variable, given the formula's
variables are below `v`. -/
theorem tseitin_out_lt : ∀ (φ : QBF) (v : ℕ), (∀ i ∈ freeVars φ, i < v) →
    (tseitin φ v).2.1.2 < (tseitin φ v).2.2
  | var i, v, hv => hv i (by simp [freeVars])
  | tru, _, _ => by simp only [tseitin]; omega
  | fls, _, _ => by simp only [tseitin]; omega
  | neg φ, v, hv => tseitin_out_lt φ v hv
  | conj _ _, _, _ => by simp only [tseitin]; omega
  | disj _ _, _, _ => by simp only [tseitin]; omega
  | ex _ _, _, _ => by simp only [tseitin]; omega
  | all _ _, _, _ => by simp only [tseitin]; omega

/-- Every clause variable is below the next fresh variable. -/
theorem tseitin_clause_vars_lt : ∀ (φ : QBF) (v : ℕ), (∀ i ∈ freeVars φ, i < v) →
    ∀ c ∈ (tseitin φ v).1, ∀ l ∈ c, l.2 < (tseitin φ v).2.2
  | var _, _, _, _, hc => by simp [tseitin] at hc
  | tru, v, _, c, hc => by
      simp only [tseitin, List.mem_singleton] at hc
      subst hc
      simp [tseitin]
  | fls, v, _, c, hc => by
      simp only [tseitin, List.mem_singleton] at hc
      subst hc
      simp [tseitin]
  | neg φ, v, hv, c, hc => tseitin_clause_vars_lt φ v hv c hc
  | conj φ ψ, v, hv, c, hc => by
      have hφ : ∀ i ∈ freeVars φ, i < v := fun i hi => hv i (by simp [freeVars, hi])
      have hψ : ∀ i ∈ freeVars ψ, i < (tseitin φ v).2.2 := fun i hi =>
        lt_of_lt_of_le (hv i (by simp [freeVars, hi])) (tseitin_next_ge φ v)
      have h1 := tseitin_clause_vars_lt φ v hφ
      have h2 := tseitin_clause_vars_lt ψ _ hψ
      have ho1 := tseitin_out_lt φ v hφ
      have ho2 := tseitin_out_lt ψ _ hψ
      have hle := tseitin_next_ge ψ (tseitin φ v).2.2
      simp only [tseitin, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc ⊢
      rcases hc with (hc | hc) | rfl | rfl | rfl
      · intro l hl
        exact lt_of_lt_of_le (h1 c hc l hl) (by omega)
      · intro l hl
        exact lt_of_lt_of_le (h2 c hc l hl) (by omega)
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Nat.lt_succ_self _
        · omega
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Nat.lt_succ_self _
        · omega
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact Nat.lt_succ_self _
        · simp only [negLit]; omega
        · simp only [negLit]; omega
  | disj φ ψ, v, hv, c, hc => by
      have hφ : ∀ i ∈ freeVars φ, i < v := fun i hi => hv i (by simp [freeVars, hi])
      have hψ : ∀ i ∈ freeVars ψ, i < (tseitin φ v).2.2 := fun i hi =>
        lt_of_lt_of_le (hv i (by simp [freeVars, hi])) (tseitin_next_ge φ v)
      have h1 := tseitin_clause_vars_lt φ v hφ
      have h2 := tseitin_clause_vars_lt ψ _ hψ
      have ho1 := tseitin_out_lt φ v hφ
      have ho2 := tseitin_out_lt ψ _ hψ
      have hle := tseitin_next_ge ψ (tseitin φ v).2.2
      simp only [tseitin, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc ⊢
      rcases hc with (hc | hc) | rfl | rfl | rfl
      · intro l hl
        exact lt_of_lt_of_le (h1 c hc l hl) (by omega)
      · intro l hl
        exact lt_of_lt_of_le (h2 c hc l hl) (by omega)
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact Nat.lt_succ_self _
        · omega
        · omega
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Nat.lt_succ_self _
        · simp only [negLit]; omega
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Nat.lt_succ_self _
        · simp only [negLit]; omega
  | ex _ _, v, _, c, hc => by
      simp only [tseitin, List.mem_singleton] at hc
      subst hc
      simp [tseitin]
  | all _ _, v, _, c, hc => by
      simp only [tseitin, List.mem_singleton] at hc
      subst hc
      simp [tseitin]

/-- Clauses whose variables are below `w` evaluate the same under assignments agreeing
below `w`. -/
theorem eval_cnfQBF_of_agree (φ : List (List CLit)) (w : ℕ)
    (hw : ∀ c ∈ φ, ∀ l ∈ c, l.2 < w) (β β' : ℕ → Bool) (h : ∀ i, i < w → β' i = β i) :
    eval β' (cnfQBF φ) = eval β (cnfQBF φ) := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [eval_cnfQBF_iff, eval_clauseQBF_iff, eval_litQBF]
  constructor
  · intro hs c hc
    obtain ⟨l, hl, hv⟩ := hs c hc
    exact ⟨l, hl, by rwa [← h _ (hw c hc l hl)]⟩
  · intro hs c hc
    obtain ⟨l, hl, hv⟩ := hs c hc
    exact ⟨l, hl, by rwa [h _ (hw c hc l hl)]⟩

/-- **Soundness.** Under any assignment satisfying the clauses, the output literal has the
formula's value. -/
theorem tseitin_sound : ∀ (φ : QBF) (v : ℕ), QuantifierFree φ → ∀ β : ℕ → Bool,
    eval β (cnfQBF (tseitin φ v).1) = true →
      eval β (litQBF (tseitin φ v).2.1) = eval β φ
  | var i, v, _, β, _ => by simp [tseitin, litQBF, eval]
  | tru, v, _, β, h => by
      simp only [tseitin, eval_cnfQBF_iff, List.mem_singleton, forall_eq, eval_clauseQBF_iff,
        List.mem_singleton, exists_eq_left, eval_litQBF] at h
      simp only [tseitin, eval_litQBF, eval]
      simpa using h
  | fls, v, _, β, h => by
      simp only [tseitin, eval_cnfQBF_iff, List.mem_singleton, forall_eq, eval_clauseQBF_iff,
        List.mem_singleton, exists_eq_left, eval_litQBF] at h
      simp only [tseitin, eval_litQBF, eval]
      simpa using h
  | neg φ, v, hqf, β, h => by
      have hqf' : QuantifierFree φ := hqf
      simp only [tseitin] at h ⊢
      rw [eval_litQBF_negLit, tseitin_sound φ v hqf' β h, eval]
  | conj φ ψ, v, hqf, β, h => by
      obtain ⟨hqf₁, hqf₂⟩ : QuantifierFree φ ∧ QuantifierFree ψ := by
        simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff] at hqf
        exact hqf
      simp only [tseitin] at h ⊢
      obtain ⟨o, ho⟩ : ∃ o, o = (tseitin ψ (tseitin φ v).2.2).2.2 := ⟨_, rfl⟩
      rw [← ho] at h ⊢
      rw [eval_cnfQBF_append, eval_cnfQBF_append] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have e1 := tseitin_sound φ v hqf₁ β h1
      have e2 := tseitin_sound ψ _ hqf₂ β h2
      rw [eval, ← e1, ← e2]
      have hneg : eval β (litQBF (false, o)) = !(eval β (litQBF (true, o))) := by
        rw [eval_litQBF, eval_litQBF]
        cases β o <;> rfl
      simp only [eval_cnfQBF_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, eval_clauseQBF_iff, exists_eq_or_imp, exists_eq_left, eval_litQBF_negLit,
        hneg] at h3
      revert h3
      generalize eval β (litQBF (true, o)) = a
      generalize eval β (litQBF (tseitin φ v).2.1) = b
      generalize eval β (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) = c
      cases a <;> cases b <;> cases c <;> simp
  | disj φ ψ, v, hqf, β, h => by
      obtain ⟨hqf₁, hqf₂⟩ : QuantifierFree φ ∧ QuantifierFree ψ := by
        simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff] at hqf
        exact hqf
      simp only [tseitin] at h ⊢
      obtain ⟨o, ho⟩ : ∃ o, o = (tseitin ψ (tseitin φ v).2.2).2.2 := ⟨_, rfl⟩
      rw [← ho] at h ⊢
      rw [eval_cnfQBF_append, eval_cnfQBF_append] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have e1 := tseitin_sound φ v hqf₁ β h1
      have e2 := tseitin_sound ψ _ hqf₂ β h2
      rw [eval, ← e1, ← e2]
      have hneg : eval β (litQBF (false, o)) = !(eval β (litQBF (true, o))) := by
        rw [eval_litQBF, eval_litQBF]
        cases β o <;> rfl
      simp only [eval_cnfQBF_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, eval_clauseQBF_iff, exists_eq_or_imp, exists_eq_left, eval_litQBF_negLit,
        hneg] at h3
      revert h3
      generalize eval β (litQBF (true, o)) = a
      generalize eval β (litQBF (tseitin φ v).2.1) = b
      generalize eval β (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) = c
      cases a <;> cases b <;> cases c <;> simp
  | ex _ _, _, hqf, _, _ => by simp [QuantifierFree, quantDepth] at hqf
  | all _ _, _, hqf, _, _ => by simp [QuantifierFree, quantDepth] at hqf

/-- **Completeness.** Every assignment of the formula's variables extends, on the fresh
variables only, to one satisfying the clauses. -/
theorem tseitin_complete : ∀ (φ : QBF) (v : ℕ), QuantifierFree φ → (∀ i ∈ freeVars φ, i < v) →
    ∀ α : ℕ → Bool, ∃ β : ℕ → Bool,
      (∀ i, (i < v ∨ (tseitin φ v).2.2 ≤ i) → β i = α i) ∧
        eval β (cnfQBF (tseitin φ v).1) = true
  | var _, v, _, _, α => ⟨α, fun _ _ => rfl, by simp [tseitin, cnfQBF]⟩
  | tru, v, _, _, α =>
      ⟨Function.update α v true,
        fun i hi => Function.update_of_ne (by simp only [tseitin] at hi; omega) _ _,
        by simp [tseitin, eval_cnfQBF_iff, eval_clauseQBF_iff, eval_litQBF]⟩
  | fls, v, _, _, α =>
      ⟨Function.update α v false,
        fun i hi => Function.update_of_ne (by simp only [tseitin] at hi; omega) _ _,
        by simp [tseitin, eval_cnfQBF_iff, eval_clauseQBF_iff, eval_litQBF]⟩
  | neg φ, v, hqf, hv, α => tseitin_complete φ v hqf hv α
  | conj φ ψ, v, hqf, hv, α => by
      obtain ⟨hqf₁, hqf₂⟩ : QuantifierFree φ ∧ QuantifierFree ψ := by
        simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff] at hqf
        exact hqf
      have hφ : ∀ i ∈ freeVars φ, i < v := fun i hi => hv i (by simp [freeVars, hi])
      have hψ : ∀ i ∈ freeVars ψ, i < (tseitin φ v).2.2 := fun i hi =>
        lt_of_lt_of_le (hv i (by simp [freeVars, hi])) (tseitin_next_ge φ v)
      obtain ⟨β₁, hβ₁, h1⟩ := tseitin_complete φ v hqf₁ hφ α
      obtain ⟨β₂, hβ₂, h2⟩ := tseitin_complete ψ _ hqf₂ hψ β₁
      have hle := tseitin_next_ge ψ (tseitin φ v).2.2
      have hle' := tseitin_next_ge φ v
      have hv1 := tseitin_clause_vars_lt φ v hφ
      have hv2 := tseitin_clause_vars_lt ψ _ hψ
      have ho1 := tseitin_out_lt φ v hφ
      have ho2 := tseitin_out_lt ψ _ hψ
      obtain ⟨o, ho⟩ : ∃ o, o = (tseitin ψ (tseitin φ v).2.2).2.2 := ⟨_, rfl⟩
      rw [← ho] at hle hv2 ho2
      refine ⟨Function.update β₂ o
        (eval β₂ (litQBF (tseitin φ v).2.1) &&
          eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)),
        fun i hi => ?_, ?_⟩
      · simp only [tseitin] at hi
        rw [← ho] at hi
        rw [Function.update_of_ne (by omega), hβ₂ i (by omega), hβ₁ i (by omega)]
      · simp only [tseitin]
        rw [← ho, eval_cnfQBF_append, eval_cnfQBF_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [eval_cnfQBF_of_agree _ _ hv1 β₁ _ fun i hi => by
            rw [Function.update_of_ne (by omega), hβ₂ i (by omega)]]
          exact h1
        · rw [eval_cnfQBF_of_agree _ _ hv2 β₂ _ fun i hi => by
            rw [Function.update_of_ne (by omega)]]
          exact h2
        · have hneg : ∀ γ : ℕ → Bool,
              eval γ (litQBF (false, o)) = !(eval γ (litQBF (true, o))) := by
            intro γ
            rw [eval_litQBF, eval_litQBF]
            cases γ o <;> rfl
          have hself : eval (Function.update β₂ o (eval β₂ (litQBF (tseitin φ v).2.1) &&
              eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1))) (litQBF (true, o))
              = (eval β₂ (litQBF (tseitin φ v).2.1) &&
                eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)) := by
            rw [eval_litQBF]
            simp
          have hl1 : ∀ b, eval (Function.update β₂ o b) (litQBF (tseitin φ v).2.1)
              = eval β₂ (litQBF (tseitin φ v).2.1) := fun b => by
            rw [eval_litQBF, eval_litQBF, Function.update_of_ne (by omega)]
          have hl2 : ∀ b, eval (Function.update β₂ o b)
              (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)
              = eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) := fun b => by
            rw [eval_litQBF, eval_litQBF, Function.update_of_ne (by omega)]
          simp only [eval_cnfQBF_iff, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, eval_clauseQBF_iff, exists_eq_or_imp, exists_eq_left,
            eval_litQBF_negLit, hneg, hself, hl1, hl2]
          generalize eval β₂ (litQBF (tseitin φ v).2.1) = b
          generalize eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) = c
          cases b <;> cases c <;> simp
  | disj φ ψ, v, hqf, hv, α => by
      obtain ⟨hqf₁, hqf₂⟩ : QuantifierFree φ ∧ QuantifierFree ψ := by
        simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff] at hqf
        exact hqf
      have hφ : ∀ i ∈ freeVars φ, i < v := fun i hi => hv i (by simp [freeVars, hi])
      have hψ : ∀ i ∈ freeVars ψ, i < (tseitin φ v).2.2 := fun i hi =>
        lt_of_lt_of_le (hv i (by simp [freeVars, hi])) (tseitin_next_ge φ v)
      obtain ⟨β₁, hβ₁, h1⟩ := tseitin_complete φ v hqf₁ hφ α
      obtain ⟨β₂, hβ₂, h2⟩ := tseitin_complete ψ _ hqf₂ hψ β₁
      have hle := tseitin_next_ge ψ (tseitin φ v).2.2
      have hle' := tseitin_next_ge φ v
      have hv1 := tseitin_clause_vars_lt φ v hφ
      have hv2 := tseitin_clause_vars_lt ψ _ hψ
      have ho1 := tseitin_out_lt φ v hφ
      have ho2 := tseitin_out_lt ψ _ hψ
      obtain ⟨o, ho⟩ : ∃ o, o = (tseitin ψ (tseitin φ v).2.2).2.2 := ⟨_, rfl⟩
      rw [← ho] at hle hv2 ho2
      refine ⟨Function.update β₂ o
        (eval β₂ (litQBF (tseitin φ v).2.1) ||
          eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)),
        fun i hi => ?_, ?_⟩
      · simp only [tseitin] at hi
        rw [← ho] at hi
        rw [Function.update_of_ne (by omega), hβ₂ i (by omega), hβ₁ i (by omega)]
      · simp only [tseitin]
        rw [← ho, eval_cnfQBF_append, eval_cnfQBF_append]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [eval_cnfQBF_of_agree _ _ hv1 β₁ _ fun i hi => by
            rw [Function.update_of_ne (by omega), hβ₂ i (by omega)]]
          exact h1
        · rw [eval_cnfQBF_of_agree _ _ hv2 β₂ _ fun i hi => by
            rw [Function.update_of_ne (by omega)]]
          exact h2
        · have hneg : ∀ γ : ℕ → Bool,
              eval γ (litQBF (false, o)) = !(eval γ (litQBF (true, o))) := by
            intro γ
            rw [eval_litQBF, eval_litQBF]
            cases γ o <;> rfl
          have hself : eval (Function.update β₂ o (eval β₂ (litQBF (tseitin φ v).2.1) ||
              eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1))) (litQBF (true, o))
              = (eval β₂ (litQBF (tseitin φ v).2.1) ||
                eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)) := by
            rw [eval_litQBF]
            simp
          have hl1 : ∀ b, eval (Function.update β₂ o b) (litQBF (tseitin φ v).2.1)
              = eval β₂ (litQBF (tseitin φ v).2.1) := fun b => by
            rw [eval_litQBF, eval_litQBF, Function.update_of_ne (by omega)]
          have hl2 : ∀ b, eval (Function.update β₂ o b)
              (litQBF (tseitin ψ (tseitin φ v).2.2).2.1)
              = eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) := fun b => by
            rw [eval_litQBF, eval_litQBF, Function.update_of_ne (by omega)]
          simp only [eval_cnfQBF_iff, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, eval_clauseQBF_iff, exists_eq_or_imp, exists_eq_left,
            eval_litQBF_negLit, hneg, hself, hl1, hl2]
          generalize eval β₂ (litQBF (tseitin φ v).2.1) = b
          generalize eval β₂ (litQBF (tseitin ψ (tseitin φ v).2.2).2.1) = c
          cases b <;> cases c <;> simp
  | ex _ _, _, hqf, _, _ => by simp [QuantifierFree, quantDepth] at hqf
  | all _ _, _, hqf, _, _ => by simp [QuantifierFree, quantDepth] at hqf

/-- **Existentially closing the auxiliaries reproduces the formula.** -/
theorem eval_exs_tseitin (φ : QBF) (v : ℕ) (hqf : QuantifierFree φ)
    (hv : ∀ i ∈ freeVars φ, i < v) (α : ℕ → Bool) :
    eval α (exs v ((tseitin φ v).2.2 - v)
      (conj (cnfQBF (tseitin φ v).1) (litQBF (tseitin φ v).2.1))) = eval α φ := by
  have hle := tseitin_next_ge φ v
  refine Bool.eq_iff_iff.mpr ?_
  rw [eval_exs_iff]
  constructor
  · rintro ⟨β, hβ, h⟩
    rw [eval, Bool.and_eq_true] at h
    rw [tseitin_sound φ v hqf β h.1] at h
    rw [eval_eq_of_agree φ α β fun i hi => (hβ i (Or.inl (hv i hi))).symm]
    exact h.2
  · intro h
    obtain ⟨β, hβ, hc⟩ := tseitin_complete φ v hqf hv α
    refine ⟨β, fun i hi => hβ i (by omega), ?_⟩
    rw [eval, Bool.and_eq_true, tseitin_sound φ v hqf β hc,
      eval_eq_of_agree φ β α fun i hi => hβ i (Or.inl (hv i hi))]
    exact ⟨hc, h⟩

/-! ## Disjunction of two clause lists, with one auxiliary variable -/

/-- Add some literals to every clause: the CNF `φ` guarded by their disjunction. -/
def disjLits (ls : List CLit) (φ : List (List CLit)) : List (List CLit) := φ.map (ls ++ ·)

theorem eval_disjLits (β : ℕ → Bool) (ls : List CLit) (φ : List (List CLit)) :
    eval β (cnfQBF (disjLits ls φ)) = true ↔
      ((∃ l ∈ ls, eval β (litQBF l) = true) ∨ eval β (cnfQBF φ) = true) := by
  simp only [disjLits, eval_cnfQBF_iff, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, eval_clauseQBF_iff, List.mem_append]
  constructor
  · intro h
    by_cases hl : ∃ l ∈ ls, eval β (litQBF l) = true
    · exact Or.inl hl
    · refine Or.inr fun c hc => ?_
      obtain ⟨l', hl', hv⟩ := h c hc
      rcases hl' with hl' | hl'
      · exact absurd ⟨l', hl', hv⟩ hl
      · exact ⟨l', hl', hv⟩
  · rintro (⟨l, hl, hv⟩ | h) c hc
    · exact ⟨l, Or.inl hl, hv⟩
    · obtain ⟨l', hl', hv⟩ := h c hc
      exact ⟨l', Or.inr hl', hv⟩

/-- Add one literal to every clause. -/
def disjLit (l : CLit) (φ : List (List CLit)) : List (List CLit) := disjLits [l] φ

theorem eval_disjLit (β : ℕ → Bool) (l : CLit) (φ : List (List CLit)) :
    eval β (cnfQBF (disjLit l φ)) = true ↔
      (eval β (litQBF l) = true ∨ eval β (cnfQBF φ) = true) := by
  rw [disjLit, eval_disjLits]
  simp

/-- The disjunction of two clause lists, using one fresh variable `z`: `z` chooses which side
has to hold. -/
def orCNF (z : ℕ) (φ ψ : List (List CLit)) : List (List CLit) :=
  disjLit (false, z) φ ++ disjLit (true, z) ψ

/-- **What the selector does**: the CNF holds iff the side the selector picks holds. -/
theorem eval_orCNF (α : ℕ → Bool) (z : ℕ) (φ ψ : List (List CLit)) :
    eval α (cnfQBF (orCNF z φ ψ)) = true ↔
      (if α z = true then eval α (cnfQBF φ) = true else eval α (cnfQBF ψ) = true) := by
  rw [orCNF, eval_cnfQBF_append, eval_disjLit, eval_disjLit, eval_litQBF, eval_litQBF]
  cases hz : α z
  · simp
  · simp

/-- **The fresh variable turns a disjunction of CNFs back into a CNF.** -/
theorem eval_exs_orCNF (α : ℕ → Bool) (z : ℕ) (φ ψ : List (List CLit))
    (hφ : ∀ c ∈ φ, ∀ l ∈ c, l.2 < z) (hψ : ∀ c ∈ ψ, ∀ l ∈ c, l.2 < z) :
    eval α (exs z 1 (cnfQBF (orCNF z φ ψ))) = true ↔
      (eval α (cnfQBF φ) = true ∨ eval α (cnfQBF ψ) = true) := by
  have hagree : ∀ (χ : List (List CLit)), (∀ c ∈ χ, ∀ l ∈ c, l.2 < z) →
      ∀ β : ℕ → Bool, (∀ i, (i < z ∨ z + 1 ≤ i) → β i = α i) →
        eval β (cnfQBF χ) = eval α (cnfQBF χ) := fun χ hχ β hβ =>
    eval_cnfQBF_of_agree χ z hχ α β fun i hi => hβ i (Or.inl hi)
  rw [eval_exs_iff]
  constructor
  · rintro ⟨β, hβ, h⟩
    rw [orCNF, eval_cnfQBF_append, eval_disjLit, eval_disjLit] at h
    obtain ⟨h1, h2⟩ := h
    rw [hagree φ hφ β hβ] at h1
    rw [hagree ψ hψ β hβ] at h2
    have hlit : eval β (litQBF (false, z)) = !(eval β (litQBF (true, z))) := by
      rw [eval_litQBF, eval_litQBF]
      cases β z <;> rfl
    rcases h1 with h1 | h1
    · rw [hlit] at h1
      rcases h2 with h2 | h2
      · rw [h2] at h1
        exact absurd h1 (by simp)
      · exact Or.inr h2
    · exact Or.inl h1
  · intro h
    refine ⟨Function.update α z (decide (eval α (cnfQBF φ) = true)), fun i hi =>
      Function.update_of_ne (by omega) _ _, ?_⟩
    have hβ : ∀ i, (i < z ∨ z + 1 ≤ i) →
        Function.update α z (decide (eval α (cnfQBF φ) = true)) i = α i := fun i hi =>
      Function.update_of_ne (by omega) _ _
    rw [orCNF, eval_cnfQBF_append, eval_disjLit, eval_disjLit, hagree φ hφ _ hβ,
      hagree ψ hψ _ hβ]
    have hz : Function.update α z (decide (eval α (cnfQBF φ) = true)) z
        = decide (eval α (cnfQBF φ) = true) := Function.update_self _ _ _
    have hfalse : eval (Function.update α z (decide (eval α (cnfQBF φ) = true)))
        (litQBF (false, z)) = !(decide (eval α (cnfQBF φ) = true)) := by
      rw [eval_litQBF, hz]
      cases decide (eval α (cnfQBF φ) = true) <;> rfl
    have htrue : eval (Function.update α z (decide (eval α (cnfQBF φ) = true)))
        (litQBF (true, z)) = decide (eval α (cnfQBF φ) = true) := by
      rw [eval_litQBF, hz]
      cases decide (eval α (cnfQBF φ) = true) <;> rfl
    rw [hfalse, htrue]
    by_cases hφt : eval α (cnfQBF φ) = true
    · rw [decide_eq_true hφt]
      exact ⟨Or.inr hφt, Or.inl rfl⟩
    · rw [decide_eq_false hφt]
      refine ⟨Or.inl rfl, Or.inr ?_⟩
      rcases h with h | h
      · exact absurd h hφt
      · exact h

/-! ## Equality bits -/

/-- The four clauses forcing `e ↔ (u ↔ v)`. -/
def iffAuxCNF (e u v : ℕ) : List (List CLit) :=
  [[(false, e), (false, u), (true, v)],
   [(false, e), (true, u), (false, v)],
   [(true, e), (false, u), (false, v)],
   [(true, e), (true, u), (true, v)]]

theorem eval_iffAuxCNF (β : ℕ → Bool) (e u v : ℕ) :
    eval β (cnfQBF (iffAuxCNF e u v)) = true ↔ β e = (β u == β v) := by
  simp only [iffAuxCNF, eval_cnfQBF_iff, eval_clauseQBF_iff, eval_litQBF, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
  cases β e <;> cases β u <;> cases β v <;> simp

theorem mem_iffAuxCNF_vars (e u v : ℕ) : ∀ c ∈ iffAuxCNF e u v, ∀ l ∈ c,
    l.2 = e ∨ l.2 = u ∨ l.2 = v := by
  intro c hc l hl
  simp only [iffAuxCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl | rfl <;> simp

/-- One equality bit per position of a `W`-bit block. -/
def eqAuxCNF (W eOff u v : ℕ) : List (List CLit) :=
  (List.range W).flatMap fun i => iffAuxCNF (eOff + i) (u + i) (v + i)

theorem eval_eqAuxCNF (β : ℕ → Bool) (W eOff u v : ℕ) :
    eval β (cnfQBF (eqAuxCNF W eOff u v)) = true ↔
      ∀ i, i < W → β (eOff + i) = (β (u + i) == β (v + i)) := by
  constructor
  · intro h i hi
    rw [← eval_iffAuxCNF β (eOff + i) (u + i) (v + i), eval_cnfQBF_iff]
    intro c hc
    rw [eval_cnfQBF_iff] at h
    exact h c (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hc⟩)
  · intro h
    rw [eval_cnfQBF_iff]
    intro c hc
    rw [eqAuxCNF, List.mem_flatMap] at hc
    obtain ⟨i, hi, hc⟩ := hc
    rw [List.mem_range] at hi
    have := (eval_iffAuxCNF β (eOff + i) (u + i) (v + i)).mpr (h i hi)
    rw [eval_cnfQBF_iff] at this
    exact this c hc

theorem mem_eqAuxCNF_vars (W eOff u v : ℕ) : ∀ c ∈ eqAuxCNF W eOff u v, ∀ l ∈ c,
    (∃ i, i < W ∧ l.2 = eOff + i) ∨ (∃ i, i < W ∧ l.2 = u + i) ∨ (∃ i, i < W ∧ l.2 = v + i) := by
  intro c hc l hl
  rw [eqAuxCNF, List.mem_flatMap] at hc
  obtain ⟨i, hi, hc⟩ := hc
  rw [List.mem_range] at hi
  rcases mem_iffAuxCNF_vars (eOff + i) (u + i) (v + i) c hc l hl with h | h | h
  · exact Or.inl ⟨i, hi, h⟩
  · exact Or.inr (Or.inl ⟨i, hi, h⟩)
  · exact Or.inr (Or.inr ⟨i, hi, h⟩)

theorem iffAuxCNF_length (e u v : ℕ) : (iffAuxCNF e u v).length = 4 := rfl

theorem eqAuxCNF_length (W eOff u v : ℕ) : (eqAuxCNF W eOff u v).length = W * 4 := by
  rw [eqAuxCNF, List.length_flatMap]
  simp [iffAuxCNF]

theorem disjLit_getElem? (l : CLit) (φ : List (List CLit)) (p : ℕ) :
    (disjLit l φ)[p]? = (φ[p]?).map fun c => l :: c := by
  rw [disjLit, disjLits, List.getElem?_map]
  rfl

theorem disjLit_length (l : CLit) (φ : List (List CLit)) :
    (disjLit l φ).length = φ.length := by
  rw [disjLit, disjLits, List.length_map]

/-- **All equality bits set means the two blocks agree.** -/
theorem all_eqAux_iff (W : ℕ) (β : ℕ → Bool) (eOff u v : ℕ)
    (h : ∀ i, i < W → β (eOff + i) = (β (u + i) == β (v + i))) :
    (∀ i, i < W → β (eOff + i) = true) ↔ ∀ i, i < W → β (u + i) = β (v + i) := by
  constructor
  · intro hall i hi
    have hi' := h i hi
    rw [hall i hi] at hi'
    exact beq_iff_eq.mp hi'.symm
  · intro heq i hi
    rw [h i hi]
    exact beq_iff_eq.mpr (heq i hi)

/-! ## Clause lists are quantifier free -/

theorem quantifierFree_litQBF (l : CLit) : QuantifierFree (litQBF l) := by
  rw [litQBF]
  split <;> simp [QuantifierFree, quantDepth]

theorem quantifierFree_clauseQBF (c : List CLit) : QuantifierFree (clauseQBF c) := by
  induction c with
  | nil => simp [clauseQBF, QuantifierFree, quantDepth]
  | cons a t ih =>
      rw [clauseQBF, List.foldr_cons, ← clauseQBF]
      simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff]
      exact ⟨quantifierFree_litQBF a, ih⟩

theorem quantifierFree_cnfQBF (φ : List (List CLit)) : QuantifierFree (cnfQBF φ) := by
  induction φ with
  | nil => simp [cnfQBF, QuantifierFree, quantDepth]
  | cons c t ih =>
      rw [cnfQBF, List.foldr_cons, ← cnfQBF]
      simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff]
      exact ⟨quantifierFree_clauseQBF c, ih⟩

/-! ## The variables of a clause list -/

theorem mem_freeVars_litQBF (l : CLit) (i : ℕ) (hi : i ∈ freeVars (litQBF l)) : i = l.2 := by
  rw [litQBF] at hi
  split at hi <;> simpa [freeVars] using hi

theorem mem_freeVars_clauseQBF (c : List CLit) (i : ℕ) (hi : i ∈ freeVars (clauseQBF c)) :
    ∃ l ∈ c, i = l.2 := by
  induction c with
  | nil => simp [clauseQBF, freeVars] at hi
  | cons a t ih =>
      rw [clauseQBF, List.foldr_cons, ← clauseQBF] at hi
      simp only [freeVars, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact ⟨a, List.mem_cons_self, mem_freeVars_litQBF a i hi⟩
      · obtain ⟨l, hl, h⟩ := ih hi
        exact ⟨l, List.mem_cons_of_mem _ hl, h⟩

theorem mem_freeVars_cnfQBF (φ : List (List CLit)) (i : ℕ) (hi : i ∈ freeVars (cnfQBF φ)) :
    ∃ c ∈ φ, ∃ l ∈ c, i = l.2 := by
  induction φ with
  | nil => simp [cnfQBF, freeVars] at hi
  | cons c t ih =>
      rw [cnfQBF, List.foldr_cons, ← cnfQBF] at hi
      simp only [freeVars, Finset.mem_union] at hi
      rcases hi with hi | hi
      · obtain ⟨l, hl, h⟩ := mem_freeVars_clauseQBF c i hi
        exact ⟨c, List.mem_cons_self, l, hl, h⟩
      · obtain ⟨c', hc', h⟩ := ih hi
        exact ⟨c', List.mem_cons_of_mem _ hc', h⟩

theorem mem_disjLits_vars (ls : List CLit) (φ : List (List CLit)) :
    ∀ c ∈ disjLits ls φ, ∀ l ∈ c, l ∈ ls ∨ ∃ c' ∈ φ, l ∈ c' := by
  intro c hc l hl
  rw [disjLits, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  rcases List.mem_append.mp hl with h | h
  · exact Or.inl h
  · exact Or.inr ⟨c', hc', h⟩

end QBF

end Complexity
