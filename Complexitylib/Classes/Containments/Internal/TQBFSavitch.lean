/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFTseitin
public import Complexitylib.Classes.Interactive.TQBFProtocol
public import Complexitylib.Circuits.Formula

/-!
# Blocks of variables and the formulas that compare them

⚠️ Unreviewed by Bolton

Savitch's recursion quantifies over configurations, each a block of `W` consecutive variables.
This file has the block-level vocabulary: reading a block off an assignment, a quantifier block
of a prefix, equality and constancy formulas for blocks, and the lemma that lets quantifiers over
later blocks move past a context that does not mention them (`eval_toQBF_conj_impl`).

## Main definitions

- `QBF.blockOf`, `QBF.blockQ`, `QBF.andList`, `QBF.orList`, `QBF.eqF`, `QBF.constF`,
  `QBF.oneHotL`, `QBF.ofBoolFormula`

## Main results

- `QBF.toQBF_append`, `QBF.toQBF_blockQ_false`, `QBF.eval_toQBF_blockQ_true_iff`
- `QBF.eval_toQBF_conj_impl`
- `QBF.eval_eqF_iff`, `QBF.eval_constF_iff`
-/

@[expose] public section

namespace Complexity

namespace QBF

open Shen

/-! ## Blocks -/

/-- The `W`-bit block at `off`. -/
def blockOf (W : ℕ) (α : ℕ → Bool) (off : ℕ) : Fin W → Bool := fun i => α (off + i)

theorem blockOf_eq_of_agree (W : ℕ) (α β : ℕ → Bool) (off : ℕ)
    (h : ∀ i, off ≤ i → i < off + W → β i = α i) : blockOf W β off = blockOf W α off :=
  funext fun i => h _ (by omega) (by omega)

/-- A quantifier block: `n` quantifiers of kind `q` over `off, …, off + n - 1`. -/
def blockQ (q : Bool) (off n : ℕ) : Prefix := (List.range n).map fun i => (q, off + i)

theorem blockQ_length (q : Bool) (off n : ℕ) : (blockQ q off n).length = n := by
  simp [blockQ]

theorem blockQ_succ (q : Bool) (off n : ℕ) :
    blockQ q off (n + 1) = (q, off) :: blockQ q (off + 1) n := by
  rw [blockQ, blockQ, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, List.cons.injEq, true_and]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp]
  congr 1
  omega

theorem toQBF_append (qs₁ qs₂ : Prefix) (ψ : QBF) :
    toQBF (qs₁ ++ qs₂) ψ = toQBF qs₁ (toQBF qs₂ ψ) := by
  induction qs₁ with
  | nil => rfl
  | cons q qs ih =>
      rcases q with ⟨b, i⟩
      cases b <;> simp [toQBF, ih]

theorem toQBF_blockQ_false : ∀ (off n : ℕ) (ψ : QBF),
    toQBF (blockQ false off n) ψ = exs off n ψ
  | _, 0, _ => rfl
  | off, n + 1, ψ => by
      rw [blockQ_succ, exs, toQBF, toQBF_blockQ_false (off + 1) n]

theorem eval_toQBF_blockQ_true_iff (α : ℕ → Bool) : ∀ (off n : ℕ) (ψ : QBF),
    eval α (toQBF (blockQ true off n) ψ) = true ↔
      ∀ β : ℕ → Bool, (∀ i, (i < off ∨ off + n ≤ i) → β i = α i) → eval β ψ = true
  | off, 0, ψ => by
      simp only [blockQ, List.range_zero, List.map_nil, toQBF]
      constructor
      · intro h β hβ
        rwa [eval_eq_of_agree ψ β α fun i _ => hβ i (by omega)]
      · intro h
        exact h α fun _ _ => rfl
  | off, n + 1, ψ => by
      rw [blockQ_succ, toQBF, eval_all_iff]
      constructor
      · intro h β hβ
        have := (eval_toQBF_blockQ_true_iff _ (off + 1) n ψ).mp (h (β off)) β fun i hi => by
          by_cases hio : i = off
          · subst hio
            simp
          · rw [Function.update_of_ne hio]
            exact hβ i (by omega)
        exact this
      · intro h b
        refine (eval_toQBF_blockQ_true_iff _ (off + 1) n ψ).mpr fun β hβ => h β fun i hi => ?_
        rw [hβ i (by omega), Function.update_of_ne (by omega)]

/-! ## Quantifiers past a context -/

/-- Quantifiers over variables that a conjunct and an antecedent do not mention move inside:
`Q. (X ∧ (C → Y)) ≡ X ∧ (C → Q. Y)`. -/
theorem eval_toQBF_conj_impl (X C : QBF) : ∀ (qs : Prefix) (Y : QBF) (α : ℕ → Bool),
    (∀ q ∈ qs, q.2 ∉ freeVars X) → (∀ q ∈ qs, q.2 ∉ freeVars C) →
    (eval α (toQBF qs (conj X (disj (neg C) Y))) = true ↔
      (eval α X = true ∧ (eval α C = true → eval α (toQBF qs Y) = true)))
  | [], Y, α, _, _ => by
      simp only [toQBF, eval_conj, eval_disj, eval_neg, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true]
      constructor
      · rintro ⟨hx, h⟩
        refine ⟨hx, fun hc => ?_⟩
        rcases h with h | h
        · rw [hc] at h
          exact absurd h (by decide)
        · exact h
      · rintro ⟨hx, h⟩
        refine ⟨hx, ?_⟩
        by_cases hc : eval α C = true
        · exact Or.inr (h hc)
        · exact Or.inl (by simpa using hc)
  | (b, i) :: qs, Y, α, hX, hC => by
      have hX' : ∀ q ∈ qs, q.2 ∉ freeVars X := fun q hq => hX q (List.mem_cons_of_mem _ hq)
      have hC' : ∀ q ∈ qs, q.2 ∉ freeVars C := fun q hq => hC q (List.mem_cons_of_mem _ hq)
      have hXi : i ∉ freeVars X := hX (b, i) List.mem_cons_self
      have hCi : i ∉ freeVars C := hC (b, i) List.mem_cons_self
      cases b
      · rw [toQBF, toQBF, eval_ex_iff, eval_ex_iff]
        constructor
        · rintro ⟨b, hb⟩
          obtain ⟨hx, h⟩ := (eval_toQBF_conj_impl X C qs Y _ hX' hC').mp hb
          rw [eval_update_not_mem _ _ _ _ hXi] at hx
          rw [eval_update_not_mem _ _ _ _ hCi] at h
          exact ⟨hx, fun hc => ⟨b, h hc⟩⟩
        · rintro ⟨hx, h⟩
          by_cases hc : eval α C = true
          · obtain ⟨b, hb⟩ := h hc
            refine ⟨b, (eval_toQBF_conj_impl X C qs Y _ hX' hC').mpr ⟨?_, fun _ => hb⟩⟩
            rwa [eval_update_not_mem _ _ _ _ hXi]
          · refine ⟨false, (eval_toQBF_conj_impl X C qs Y _ hX' hC').mpr ⟨?_, fun hc' => ?_⟩⟩
            · rwa [eval_update_not_mem _ _ _ _ hXi]
            · rw [eval_update_not_mem _ _ _ _ hCi] at hc'
              exact absurd hc' hc
      · rw [toQBF, toQBF, eval_all_iff, eval_all_iff]
        constructor
        · intro h
          have h0 := (eval_toQBF_conj_impl X C qs Y _ hX' hC').mp (h false)
          rw [eval_update_not_mem _ _ _ _ hXi] at h0
          refine ⟨h0.1, fun hc b => ?_⟩
          have hb := (eval_toQBF_conj_impl X C qs Y _ hX' hC').mp (h b)
          rw [eval_update_not_mem _ _ _ _ hCi] at hb
          exact hb.2 hc
        · rintro ⟨hx, h⟩ b
          refine (eval_toQBF_conj_impl X C qs Y _ hX' hC').mpr ⟨?_, fun hc => ?_⟩
          · rwa [eval_update_not_mem _ _ _ _ hXi]
          · rw [eval_update_not_mem _ _ _ _ hCi] at hc
            exact h hc b

/-! ## Conjunctions of lists -/

/-- The conjunction of a list of formulas. -/
def andList (l : List QBF) : QBF := l.foldr conj tru

theorem eval_andList_iff (α : ℕ → Bool) (l : List QBF) :
    eval α (andList l) = true ↔ ∀ φ ∈ l, eval α φ = true := by
  induction l with
  | nil => simp [andList]
  | cons φ l ih =>
      rw [andList, List.foldr_cons, eval_conj, Bool.and_eq_true, ← andList, ih]
      simp

theorem mem_freeVars_andList (l : List QBF) (i : ℕ) (hi : i ∈ freeVars (andList l)) :
    ∃ φ ∈ l, i ∈ freeVars φ := by
  induction l with
  | nil => simp [andList, freeVars] at hi
  | cons φ l ih =>
      rw [andList, List.foldr_cons, freeVars, ← andList, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact ⟨φ, List.mem_cons_self, hi⟩
      · obtain ⟨ψ, hψ, hi⟩ := ih hi
        exact ⟨ψ, List.mem_cons_of_mem _ hψ, hi⟩

theorem quantifierFree_andList (l : List QBF) (h : ∀ φ ∈ l, QuantifierFree φ) :
    QuantifierFree (andList l) := by
  induction l with
  | nil => simp [andList, QuantifierFree, quantDepth]
  | cons φ l ih =>
      rw [andList, List.foldr_cons, ← andList, quantifierFree_conj]
      exact ⟨h φ List.mem_cons_self, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

/-! ## Equality of blocks -/

/-- `x ↔ y`. -/
def iffF (x y : ℕ) : QBF := disj (conj (var x) (var y)) (conj (neg (var x)) (neg (var y)))

theorem eval_iffF (α : ℕ → Bool) (x y : ℕ) : eval α (iffF x y) = (α x == α y) := by
  simp only [iffF, eval_disj, eval_conj, eval_neg, eval_var]
  cases α x <;> cases α y <;> rfl

theorem quantifierFree_iffF (x y : ℕ) : QuantifierFree (iffF x y) := by
  simp [iffF, QuantifierFree, quantDepth]

theorem mem_freeVars_iffF (x y i : ℕ) (hi : i ∈ freeVars (iffF x y)) : i = x ∨ i = y := by
  simp [iffF, freeVars] at hi
  omega

/-- The blocks at `u` and `a` are equal. -/
def eqF (W u a : ℕ) : QBF := andList ((List.range W).map fun i => iffF (u + i) (a + i))

theorem eval_eqF_iff (W : ℕ) (α : ℕ → Bool) (u a : ℕ) :
    eval α (eqF W u a) = true ↔ blockOf W α u = blockOf W α a := by
  rw [eqF, eval_andList_iff]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, eval_iffF, beq_iff_eq]
  constructor
  · intro h
    funext i
    exact h i i.2
  · intro h i hi
    exact congrFun h ⟨i, hi⟩

theorem quantifierFree_eqF (W u a : ℕ) : QuantifierFree (eqF W u a) :=
  quantifierFree_andList _ fun φ hφ => by
    rw [List.mem_map] at hφ
    obtain ⟨i, _, rfl⟩ := hφ
    exact quantifierFree_iffF _ _

theorem mem_freeVars_eqF (W u a i : ℕ) (hi : i ∈ freeVars (eqF W u a)) :
    (u ≤ i ∧ i < u + W) ∨ (a ≤ i ∧ i < a + W) := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  rw [List.mem_map] at hφ
  obtain ⟨j, hj, rfl⟩ := hφ
  rw [List.mem_range] at hj
  rcases mem_freeVars_iffF _ _ _ hi with rfl | rfl
  · left; omega
  · right; omega

/-! ## A block with fixed contents -/

/-- The block at `off` is `c`. -/
def constF (W off : ℕ) (c : Fin W → Bool) : QBF :=
  andList ((List.finRange W).map fun i => if c i then var (off + i) else neg (var (off + i)))

theorem eval_constF_iff (W : ℕ) (α : ℕ → Bool) (off : ℕ) (c : Fin W → Bool) :
    eval α (constF W off c) = true ↔ blockOf W α off = c := by
  rw [constF, eval_andList_iff]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  constructor
  · intro h
    funext i
    have := h i
    split_ifs at this with hc
    · rw [hc]
      simpa using this
    · rw [Bool.eq_false_iff.mpr hc]
      simpa using this
  · intro h i
    have := congrFun h i
    simp only [blockOf] at this
    split_ifs with hc
    · rw [eval_var, this, hc]
    · rw [eval_neg, eval_var, this]
      simpa using hc

theorem quantifierFree_constF (W off : ℕ) (c : Fin W → Bool) : QuantifierFree (constF W off c) :=
  quantifierFree_andList _ fun φ hφ => by
    rw [List.mem_map] at hφ
    obtain ⟨i, _, rfl⟩ := hφ
    split_ifs <;> simp [QuantifierFree, quantDepth]

theorem mem_freeVars_constF (W off : ℕ) (c : Fin W → Bool) (i : ℕ)
    (hi : i ∈ freeVars (constF W off c)) : off ≤ i ∧ i < off + W := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  rw [List.mem_map] at hφ
  obtain ⟨j, _, rfl⟩ := hφ
  split_ifs at hi <;> simp [freeVars] at hi <;> omega

/-! ## Disjunctions and one-hot groups -/

/-- The disjunction of a list of formulas. -/
def orList (l : List QBF) : QBF := l.foldr disj fls

theorem eval_orList_iff (α : ℕ → Bool) (l : List QBF) :
    eval α (orList l) = true ↔ ∃ φ ∈ l, eval α φ = true := by
  induction l with
  | nil => simp [orList]
  | cons φ l ih =>
      rw [orList, List.foldr_cons, eval_disj, Bool.or_eq_true, ← orList, ih]
      simp

theorem mem_freeVars_orList (l : List QBF) (i : ℕ) (hi : i ∈ freeVars (orList l)) :
    ∃ φ ∈ l, i ∈ freeVars φ := by
  induction l with
  | nil => simp [orList, freeVars] at hi
  | cons φ l ih =>
      rw [orList, List.foldr_cons, freeVars, ← orList, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact ⟨φ, List.mem_cons_self, hi⟩
      · obtain ⟨ψ, hψ, hi⟩ := ih hi
        exact ⟨ψ, List.mem_cons_of_mem _ hψ, hi⟩

theorem quantifierFree_orList (l : List QBF) (h : ∀ φ ∈ l, QuantifierFree φ) :
    QuantifierFree (orList l) := by
  induction l with
  | nil => simp [orList, QuantifierFree, quantDepth]
  | cons φ l ih =>
      rw [orList, List.foldr_cons, ← orList]
      have h1 := h φ List.mem_cons_self
      have h2 := ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)
      simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff] at *
      exact ⟨h1, h2⟩

variable {A : Type}

/-- Exactly the wire of `a` is set among the wires of `l`. -/
def hotAt (w : A → ℕ) (l : List A) (a : A) : QBF :=
  andList (l.map fun b => if w b = w a then var (w b) else neg (var (w b)))

theorem eval_hotAt_iff (w : A → ℕ) (l : List A) (a : A) (α : ℕ → Bool) :
    eval α (hotAt w l a) = true ↔ ∀ b ∈ l, α (w b) = decide (w b = w a) := by
  rw [hotAt, eval_andList_iff]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h b hb
    have := h b hb
    split_ifs at this with hc
    · rw [eval_var] at this
      rw [this, decide_eq_true hc]
    · rw [eval_neg, eval_var, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      rw [this, decide_eq_false hc]
  · intro h b hb
    have := h b hb
    split_ifs with hc
    · rw [eval_var, this, decide_eq_true hc]
    · rw [eval_neg, eval_var, this, decide_eq_false hc]
      rfl

/-- Exactly one wire of the group is set. -/
def oneHotL (w : A → ℕ) (l : List A) : QBF := orList (l.map (hotAt w l))

theorem eval_oneHotL_iff (w : A → ℕ) (l : List A) (α : ℕ → Bool) :
    eval α (oneHotL w l) = true ↔
      ∃ a ∈ l, ∀ b ∈ l, α (w b) = decide (w b = w a) := by
  rw [oneHotL, eval_orList_iff]
  simp only [List.mem_map, exists_exists_and_eq_and, eval_hotAt_iff]

theorem quantifierFree_hotAt (w : A → ℕ) (l : List A) (a : A) :
    QuantifierFree (hotAt w l a) :=
  quantifierFree_andList _ fun φ hφ => by
    rw [List.mem_map] at hφ
    obtain ⟨b, _, rfl⟩ := hφ
    split_ifs <;> simp [QuantifierFree, quantDepth]

theorem quantifierFree_oneHotL (w : A → ℕ) (l : List A) : QuantifierFree (oneHotL w l) :=
  quantifierFree_orList _ fun φ hφ => by
    rw [List.mem_map] at hφ
    obtain ⟨b, _, rfl⟩ := hφ
    exact quantifierFree_hotAt _ _ _

theorem mem_freeVars_hotAt (w : A → ℕ) (l : List A) (a : A) (i : ℕ)
    (hi : i ∈ freeVars (hotAt w l a)) : ∃ b ∈ l, i = w b := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  rw [List.mem_map] at hφ
  obtain ⟨b, hb, rfl⟩ := hφ
  refine ⟨b, hb, ?_⟩
  split_ifs at hi <;> simp [freeVars] at hi <;> omega

theorem mem_freeVars_oneHotL (w : A → ℕ) (l : List A) (i : ℕ)
    (hi : i ∈ freeVars (oneHotL w l)) : ∃ b ∈ l, i = w b := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_orList _ i hi
  rw [List.mem_map] at hφ
  obtain ⟨a, _, rfl⟩ := hφ
  exact mem_freeVars_hotAt w l a i hi

theorem eval_oneHotL_inj_iff [DecidableEq A] (w : A → ℕ) (l : List A)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, w a = w b → a = b) (α : ℕ → Bool) :
    eval α (oneHotL w l) = true ↔ ∃ a ∈ l, ∀ b ∈ l, α (w b) = decide (b = a) := by
  rw [eval_oneHotL_iff]
  have key : ∀ a ∈ l, ∀ b ∈ l, decide (w b = w a) = decide (b = a) := fun a ha b hb =>
    decide_eq_decide.mpr ⟨fun hc => hinj b hb a ha hc, fun hc => by rw [hc]⟩
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, fun b hb => by rw [h b hb, key a ha b hb]⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, fun b hb => by rw [h b hb, (key a ha b hb).symm]⟩

/-! ## Boolean formulas -/

/-- A Boolean formula as a quantifier-free `QBF`. -/
def ofBoolFormula : BoolFormula → QBF
  | .var i => var i
  | .tru => tru
  | .fls => fls
  | .neg φ => neg (ofBoolFormula φ)
  | .conj φ ψ => conj (ofBoolFormula φ) (ofBoolFormula ψ)
  | .disj φ ψ => disj (ofBoolFormula φ) (ofBoolFormula ψ)

@[simp] theorem eval_ofBoolFormula (α : ℕ → Bool) :
    ∀ φ : BoolFormula, eval α (ofBoolFormula φ) = BoolFormula.eval α φ
  | .var _ => rfl
  | .tru => rfl
  | .fls => rfl
  | .neg φ => by rw [ofBoolFormula, eval, BoolFormula.eval, eval_ofBoolFormula α φ]
  | .conj φ ψ => by
      rw [ofBoolFormula, eval, BoolFormula.eval, eval_ofBoolFormula α φ, eval_ofBoolFormula α ψ]
  | .disj φ ψ => by
      rw [ofBoolFormula, eval, BoolFormula.eval, eval_ofBoolFormula α φ, eval_ofBoolFormula α ψ]

theorem quantifierFree_ofBoolFormula : ∀ φ : BoolFormula, QuantifierFree (ofBoolFormula φ)
  | .var _ => rfl
  | .tru => rfl
  | .fls => rfl
  | .neg φ => quantifierFree_ofBoolFormula φ
  | .conj φ ψ => by
      have h1 := quantifierFree_ofBoolFormula φ
      have h2 := quantifierFree_ofBoolFormula ψ
      simp only [QuantifierFree, ofBoolFormula, quantDepth, Nat.max_eq_zero_iff] at *
      exact ⟨h1, h2⟩
  | .disj φ ψ => by
      have h1 := quantifierFree_ofBoolFormula φ
      have h2 := quantifierFree_ofBoolFormula ψ
      simp only [QuantifierFree, ofBoolFormula, quantDepth, Nat.max_eq_zero_iff] at *
      exact ⟨h1, h2⟩

@[simp] theorem freeVars_ofBoolFormula : ∀ φ : BoolFormula, freeVars (ofBoolFormula φ) = φ.vars
  | .var _ => rfl
  | .tru => rfl
  | .fls => rfl
  | .neg φ => by rw [ofBoolFormula, freeVars, BoolFormula.vars, freeVars_ofBoolFormula φ]
  | .conj φ ψ => by
      rw [ofBoolFormula, freeVars, BoolFormula.vars, freeVars_ofBoolFormula φ,
        freeVars_ofBoolFormula ψ]
  | .disj φ ψ => by
      rw [ofBoolFormula, freeVars, BoolFormula.vars, freeVars_ofBoolFormula φ,
        freeVars_ofBoolFormula ψ]

end QBF

end Complexity
