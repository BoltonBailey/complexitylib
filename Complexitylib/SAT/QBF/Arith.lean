/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.SAT.QBF
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Arithmetization of quantified Boolean formulas

⚠️ Unreviewed by Bolton

The first step of Shamir's theorem: a quantified Boolean formula becomes a polynomial expression
over a commutative ring, with `∧` as multiplication, `¬ φ` as `1 - φ`, `∨` by De Morgan,
`∀ x_i` as the product and `∃ x_i` as the De Morgan dual of the product over `x_i ∈ {0, 1}`. This
arithmetization is *Boolean-preserving*: on a `0`/`1` assignment its value is the truth value of
the formula (`QBF.arith_ofBool`), in any ring, so no size condition on the field is needed to
read the answer off.

With every other variable fixed, the arithmetization is a polynomial in `x_i` of degree at most
`QBF.varDeg i φ` (`QBF.arith_isPoly`): one for a variable, additive over connectives, and
*doubling* at every quantifier not binding `x_i` — the degree blow-up that Shamir's protocol
controls with the linearization operator `QBF.linearize`, which replaces a function by the unique
multilinear-in-`x_i` interpolant of its values at `x_i ∈ {0, 1}`. Linearization keeps Boolean
values (`QBF.linearize_ofBool`), has degree at most one in `x_i` (`QBF.linearize_isPoly_self`),
and does not raise the degree in any other variable (`QBF.linearize_isPoly_other`).

## Main definitions

- `QBF.arith` — the arithmetization
- `QBF.ofBool` — a Boolean assignment as a ring assignment
- `QBF.IsPolyIn` — "a polynomial of degree at most `d` in variable `i`"
- `QBF.varDeg` — the degree bound of the arithmetization in a variable
- `QBF.linearize` — the degree-reduction operator

## Main results

- `QBF.arith_ofBool` — the arithmetization is Boolean-preserving
- `QBF.arith_isPoly` — and of degree at most `varDeg i φ` in `x_i`
- `QBF.linearize_ofBool`, `QBF.linearize_isPoly_self`, `QBF.linearize_isPoly_other`
-/

@[expose] public section

namespace Complexity

namespace QBF

variable {R : Type} [CommRing R]

/-! ## The arithmetization -/

/-- The Boolean-preserving arithmetization of a QBF under a ring assignment. -/
def arith : QBF → (ℕ → R) → R
  | .var i, a => a i
  | .tru, _ => 1
  | .fls, _ => 0
  | .neg φ, a => 1 - arith φ a
  | .conj φ ψ, a => arith φ a * arith ψ a
  | .disj φ ψ, a => 1 - (1 - arith φ a) * (1 - arith ψ a)
  | .ex i φ, a =>
      1 - (1 - arith φ (Function.update a i 0)) * (1 - arith φ (Function.update a i 1))
  | .all i φ, a => arith φ (Function.update a i 0) * arith φ (Function.update a i 1)

/-- A Boolean assignment, as a ring assignment. -/
def ofBool (α : ℕ → Bool) : ℕ → R := fun i => if α i then 1 else 0

theorem ofBool_update (α : ℕ → Bool) (i : ℕ) (b : Bool) :
    (ofBool (Function.update α i b) : ℕ → R)
      = Function.update (ofBool α) i (if b then 1 else 0) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ofBool]
  · simp [ofBool, Function.update_of_ne h]

/-- **The arithmetization is Boolean-preserving**: on a Boolean assignment it is the truth
value. -/
theorem arith_ofBool (φ : QBF) : ∀ α : ℕ → Bool,
    arith φ (ofBool α : ℕ → R) = if eval α φ then 1 else 0 := by
  induction φ with
  | var i => intro α; rfl
  | tru => intro α; rfl
  | fls => intro α; rfl
  | neg φ ih =>
      intro α
      rw [arith, ih, eval_neg]
      cases eval α φ <;> simp
  | conj φ ψ ihφ ihψ =>
      intro α
      rw [arith, ihφ, ihψ, eval_conj]
      cases eval α φ <;> cases eval α ψ <;> simp
  | disj φ ψ ihφ ihψ =>
      intro α
      rw [arith, ihφ, ihψ, eval_disj]
      cases eval α φ <;> cases eval α ψ <;> simp
  | ex i φ ih =>
      intro α
      have h0 := ih (Function.update α i false)
      have h1 := ih (Function.update α i true)
      rw [ofBool_update] at h0 h1
      simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
      rw [arith, h0, h1, eval]
      cases eval (Function.update α i false) φ <;> cases eval (Function.update α i true) φ <;>
        simp
  | all i φ ih =>
      intro α
      have h0 := ih (Function.update α i false)
      have h1 := ih (Function.update α i true)
      rw [ofBool_update] at h0 h1
      simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
      rw [arith, h0, h1, eval]
      cases eval (Function.update α i false) φ <;> cases eval (Function.update α i true) φ <;>
        simp

/-! ## Degree in a variable -/

/-- `f` is a polynomial of degree at most `d` in variable `i`, whatever the other variables. -/
def IsPolyIn (d i : ℕ) (f : (ℕ → R) → R) : Prop :=
  ∀ a : ℕ → R, ∃ p : Polynomial R, p.natDegree ≤ d ∧
    ∀ t, p.eval t = f (Function.update a i t)

theorem IsPolyIn.mono {d d' i : ℕ} {f : (ℕ → R) → R} (h : IsPolyIn d i f) (hd : d ≤ d') :
    IsPolyIn d' i f :=
  fun a => let ⟨p, hp, hpe⟩ := h a; ⟨p, le_trans hp hd, hpe⟩

theorem isPolyIn_const (i : ℕ) (c : R) : IsPolyIn 0 i (fun _ => c) :=
  fun _ => ⟨Polynomial.C c, by simp, fun t => by simp⟩

theorem isPolyIn_one_sub {d i : ℕ} {f : (ℕ → R) → R} (h : IsPolyIn d i f) :
    IsPolyIn d i (fun a => 1 - f a) := by
  intro a
  obtain ⟨p, hp, hpe⟩ := h a
  refine ⟨1 - p, ?_, fun t => by simp [hpe]⟩
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) hp)

theorem isPolyIn_mul {d₁ d₂ i : ℕ} {f g : (ℕ → R) → R} (hf : IsPolyIn d₁ i f)
    (hg : IsPolyIn d₂ i g) : IsPolyIn (d₁ + d₂) i (fun a => f a * g a) := by
  intro a
  obtain ⟨p, hp, hpe⟩ := hf a
  obtain ⟨q, hq, hqe⟩ := hg a
  refine ⟨p * q, le_trans (Polynomial.natDegree_mul_le) (add_le_add hp hq), fun t => by
    simp [hpe, hqe]⟩

/-- Substituting a constant for `x_i` leaves a function that no longer depends on `x_i`. -/
theorem isPolyIn_update_self {i : ℕ} (f : (ℕ → R) → R) (c : R) :
    IsPolyIn 0 i (fun a => f (Function.update a i c)) := by
  intro a
  refine ⟨Polynomial.C (f (Function.update a i c)), by simp, fun t => ?_⟩
  simp [Function.update_idem]

/-- Substituting a constant for another variable `x_j` preserves the degree in `x_i`. -/
theorem isPolyIn_update_other {d i j : ℕ} (hij : j ≠ i) {f : (ℕ → R) → R}
    (hf : IsPolyIn d i f) (c : R) : IsPolyIn d i (fun a => f (Function.update a j c)) := by
  intro a
  obtain ⟨p, hp, hpe⟩ := hf (Function.update a j c)
  refine ⟨p, hp, fun t => ?_⟩
  rw [hpe, Function.update_comm hij]

/-- The degree bound of the arithmetization in variable `i`. -/
def varDeg (i : ℕ) : QBF → ℕ
  | .var j => if j = i then 1 else 0
  | .tru => 0
  | .fls => 0
  | .neg φ => varDeg i φ
  | .conj φ ψ => varDeg i φ + varDeg i ψ
  | .disj φ ψ => varDeg i φ + varDeg i ψ
  | .ex j φ => if j = i then 0 else 2 * varDeg i φ
  | .all j φ => if j = i then 0 else 2 * varDeg i φ

/-- **The arithmetization is a polynomial of degree at most `varDeg i φ` in `x_i`.** -/
theorem arith_isPoly (i : ℕ) :
    ∀ φ : QBF, IsPolyIn (varDeg i φ) i (arith φ : (ℕ → R) → R)
  | .var j => by
      intro a
      by_cases h : j = i
      · subst h
        refine ⟨Polynomial.X, by rw [varDeg, if_pos rfl]; exact Polynomial.natDegree_X_le,
          fun t => by simp [arith]⟩
      · refine ⟨Polynomial.C (a j), by simp [varDeg, h], fun t => ?_⟩
        simp [arith, Function.update_of_ne h]
  | .tru => isPolyIn_const i 1
  | .fls => isPolyIn_const i 0
  | .neg φ => isPolyIn_one_sub (arith_isPoly i φ)
  | .conj φ ψ => isPolyIn_mul (arith_isPoly i φ) (arith_isPoly i ψ)
  | .disj φ ψ =>
      isPolyIn_one_sub (isPolyIn_mul (isPolyIn_one_sub (arith_isPoly i φ))
        (isPolyIn_one_sub (arith_isPoly i ψ)))
  | .ex j φ => by
      have ih := arith_isPoly i φ
      by_cases h : j = i
      · subst h
        show IsPolyIn (if j = j then 0 else 2 * varDeg j φ) j _
        rw [if_pos rfl]
        exact isPolyIn_one_sub (isPolyIn_mul (isPolyIn_one_sub (isPolyIn_update_self _ 0))
          (isPolyIn_one_sub (isPolyIn_update_self _ 1)))
      · show IsPolyIn (if j = i then 0 else 2 * varDeg i φ) i _
        rw [if_neg h, two_mul]
        exact isPolyIn_one_sub (isPolyIn_mul (isPolyIn_one_sub (isPolyIn_update_other h ih 0))
          (isPolyIn_one_sub (isPolyIn_update_other h ih 1)))
  | .all j φ => by
      have ih := arith_isPoly i φ
      by_cases h : j = i
      · subst h
        show IsPolyIn (if j = j then 0 else 2 * varDeg j φ) j _
        rw [if_pos rfl]
        exact isPolyIn_mul (isPolyIn_update_self _ 0) (isPolyIn_update_self _ 1)
      · show IsPolyIn (if j = i then 0 else 2 * varDeg i φ) i _
        rw [if_neg h, two_mul]
        exact isPolyIn_mul (isPolyIn_update_other h ih 0) (isPolyIn_update_other h ih 1)

/-! ## Degree reduction -/

/-- **Linearization in `x_i`**: the interpolant, of degree one in `x_i`, of the values at
`x_i ∈ {0, 1}`. -/
def linearize (i : ℕ) (f : (ℕ → R) → R) (a : ℕ → R) : R :=
  (1 - a i) * f (Function.update a i 0) + a i * f (Function.update a i 1)

/-- Linearization keeps Boolean values. -/
theorem linearize_ofBool (i : ℕ) (f : (ℕ → R) → R) (α : ℕ → Bool) :
    linearize i f (ofBool α) = f (ofBool α) := by
  rw [linearize]
  have h0 : Function.update (ofBool α : ℕ → R) i 0 = ofBool (Function.update α i false) := by
    rw [ofBool_update]; simp
  have h1 : Function.update (ofBool α : ℕ → R) i 1 = ofBool (Function.update α i true) := by
    rw [ofBool_update]; simp
  rw [h0, h1]
  by_cases hi : α i
  · have : Function.update α i true = α := by
      funext j; by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [Function.update_of_ne hj]
    simp [ofBool, hi, this]
  · have : Function.update α i false = α := by
      funext j; by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [Function.update_of_ne hj]
    simp [ofBool, hi, this]

/-- Linearization has degree at most one in the linearized variable. -/
theorem linearize_isPoly_self (i : ℕ) (f : (ℕ → R) → R) : IsPolyIn 1 i (linearize i f) := by
  intro a
  refine ⟨Polynomial.C (f (Function.update a i 0)) * (1 - Polynomial.X)
    + Polynomial.C (f (Function.update a i 1)) * Polynomial.X, ?_, fun t => ?_⟩
  · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, zero_add]
      exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) Polynomial.natDegree_X_le)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, zero_add]
      exact Polynomial.natDegree_X_le
  · simp only [linearize, Function.update_self, Function.update_idem, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X]
    ring

/-- Linearization in `x_i` does not raise the degree in any other variable. -/
theorem linearize_isPoly_other {d i j : ℕ} (hij : j ≠ i) {f : (ℕ → R) → R}
    (hf : IsPolyIn d j f) : IsPolyIn d j (linearize i f) := by
  intro a
  obtain ⟨p₀, hp₀, hp₀e⟩ := hf (Function.update a i 0)
  obtain ⟨p₁, hp₁, hp₁e⟩ := hf (Function.update a i 1)
  refine ⟨Polynomial.C (1 - a i) * p₀ + Polynomial.C (a i) * p₁, ?_, fun t => ?_⟩
  · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans Polynomial.natDegree_mul_le
        (by rw [Polynomial.natDegree_C, zero_add]; exact hp₀)
    · exact le_trans Polynomial.natDegree_mul_le
        (by rw [Polynomial.natDegree_C, zero_add]; exact hp₁)
  · simp only [linearize, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hp₀e,
      hp₁e, Function.update_of_ne hij.symm, Function.update_comm hij]

end QBF

end Complexity
