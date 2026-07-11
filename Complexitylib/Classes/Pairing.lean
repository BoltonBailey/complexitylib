import Complexitylib.Models.TuringMachine
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Complexity

/-!
# Pairing and relation predicates

This file defines a simple injective pairing `pair : List Bool → List Bool → List Bool`
used to encode `(x, y)` as a single binary string for verification by a TM, along with
the shared predicates `PolyBalanced` and `pairLang` used by FNP, FNL, and other
search-problem classes.
-/

/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    This encoding is injective and computable in linear time. -/
def pair (x y : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ y

/-- Partial inverse to `pair`. It scans doubled bits until the first
    separator `[false, true]`, returning the decoded left component together
    with the remaining suffix. Invalid doubled prefixes return `none`. -/
def unpair? : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: true :: y => some ([], y)
  | false :: false :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (false :: xy.1, xy.2)) (unpair? z)
  | true :: true :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (true :: xy.1, xy.2)) (unpair? z)
  | _ => none

private theorem pair_nil_eq (y : List Bool) :
    pair [] y = false :: true :: y := by
  simp [pair]

private theorem pair_cons_eq (b : Bool) (x y : List Bool) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair, List.append_assoc]

/-- `|pair x y| = 2·|x| + 2 + |y|`. The `2·|x|` comes from doubling every
    bit of `x`; the `+2` is the separator `[false, true]`. -/
@[simp] theorem pair_length (x y : List Bool) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  induction x with
  | nil => simp [pair]; omega
  | cons b xs ih =>
    rw [pair_cons_eq, List.length_cons, List.length_cons, List.length_cons, ih]
    omega

/-- `pair` is injective: if `pair x₁ y₁ = pair x₂ y₂` then `x₁ = x₂` and `y₁ = y₂`. -/
theorem pair_injective {x₁ x₂ : List Bool} {y₁ y₂ : List Bool}
    (h : pair x₁ y₁ = pair x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  induction x₁ generalizing x₂ with
  | nil =>
    rw [pair_nil_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
    | cons b x₂' =>
      rw [pair_cons_eq] at h
      have h1 := (List.cons.inj h).1           -- false = b
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- true = b
      exact absurd (h1.trans h2.symm) Bool.false_ne_true
  | cons b₁ x₁' ih =>
    rw [pair_cons_eq] at h
    cases x₂ with
    | nil =>
      rw [pair_nil_eq] at h
      have h1 := (List.cons.inj h).1           -- b₁ = false
      have h2 := (List.cons.inj (List.cons.inj h).2).1  -- b₁ = true
      exact absurd (h1.symm.trans h2) Bool.false_ne_true
    | cons b₂ x₂' =>
      rw [pair_cons_eq] at h
      have hb := (List.cons.inj h).1           -- b₁ = b₂
      have htail := (List.cons.inj (List.cons.inj h).2).2  -- pair x₁' y₁ = pair x₂' y₂
      have ⟨hx, hy⟩ := ih htail
      subst hb; subst hx
      exact ⟨rfl, hy⟩

@[simp] theorem unpair?_pair (x y : List Bool) :
    unpair? (pair x y) = some (x, y) := by
  induction x with
  | nil =>
    simp [unpair?, pair_nil_eq]
  | cons b xs ih =>
    rw [pair_cons_eq]
    cases b <;> simp [unpair?, ih]

theorem unpair?_sound {z x y : List Bool} (h : unpair? z = some (x, y)) :
    z = pair x y := by
  have hsound :
      ∀ z x y, unpair? z = some (x, y) → z = pair x y := by
    intro z x y h
    induction hlen : z.length using Nat.strong_induction_on generalizing z x y with
    | h n ih =>
        cases z with
        | nil =>
            simp [unpair?] at h
        | cons a z1 =>
            cases z1 with
            | nil =>
                cases a <;> simp [unpair?] at h
            | cons b z2 =>
                cases a
                · cases b
                  · simp [unpair?] at h
                    rcases h with ⟨x', htail, rfl⟩
                    have hz2lt : z2.length < n := by
                      rw [← hlen]
                      have : z2.length < z2.length + 1 + 1 := by omega
                      exact this
                    have hz2 : z2 = pair x' y := ih z2.length hz2lt z2 x' y htail rfl
                    simpa [pair_cons_eq] using congrArg (fun t => false :: false :: t) hz2
                  · simp [unpair?] at h
                    rcases h with ⟨rfl, rfl⟩
                    simp [pair_nil_eq]
                · cases b
                  · simp [unpair?] at h
                  · simp [unpair?] at h
                    rcases h with ⟨x', htail, rfl⟩
                    have hz2lt : z2.length < n := by
                      rw [← hlen]
                      have : z2.length < z2.length + 1 + 1 := by omega
                      exact this
                    have hz2 : z2 = pair x' y := ih z2.length hz2lt z2 x' y htail rfl
                    simpa [pair_cons_eq] using congrArg (fun t => true :: true :: t) hz2
  exact hsound z x y h

theorem unpair?_eq_some_iff {z x y : List Bool} :
    unpair? z = some (x, y) ↔ z = pair x y := by
  constructor
  · exact unpair?_sound
  · intro hz
    subst hz
    exact unpair?_pair x y

/-- A binary relation is **polynomially balanced** if witness length is bounded
    by a polynomial in the input length. This is the standard "short witness"
    condition used in the definitions of NP, FNP, FNL, etc. -/
def PolyBalanced (R : List Bool → List Bool → Prop) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x y, R x y → y.length ≤ p.eval x.length

/-- The **pair language** (verification language) of a binary relation `R`:
    the set of encoded pairs `pair(x, y)` such that `R x y` holds. -/
def pairLang (R : List Bool → List Bool → Prop) : Language :=
  {z | ∃ x y, z = pair x y ∧ R x y}

end Complexity
