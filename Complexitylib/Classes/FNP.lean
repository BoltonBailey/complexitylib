import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial
import Complexitylib.Classes.P
import Complexitylib.Classes.NP

/-!
# FNP, coFNP, and TFNP

This file defines the function/search complexity classes **FNP**, **coFNP**, and
**TFNP**.

An FNP search problem is specified by a binary relation `R` that is polynomially
balanced and decidable in polynomial time. The search task is: given `x`, find `y`
with `R x y`, or report that none exists.

## Pairing

We define a simple injective pairing `pair : List Bool → List Bool → List Bool`
used to encode `(x, y)` as a single binary string for verification by a TM.
-/

/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    This encoding is injective and computable in linear time. -/
def pair (x y : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ y

private theorem pair_nil_eq (y : List Bool) :
    pair [] y = false :: true :: y := by
  simp [pair]

private theorem pair_cons_eq (b : Bool) (x y : List Bool) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair, List.append_assoc]

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

/-- **FNP** is the class of search problems defined by NP relations: binary
    relations that are polynomially balanced and decidable in polynomial time.
    A relation `R` is in FNP if witnesses have poly-bounded length and the
    language `{pair(x, y) | R x y}` is in P. -/
def FNP : Set (List Bool → List Bool → Prop) :=
  {R | (∃ p, IsPolyBounded p ∧ ∀ x y, R x y → y.length ≤ p x.length) ∧
       {z | ∃ x y, z = pair x y ∧ R x y} ∈ P}

/-- **coFNP** is the class of FNP search problems whose associated decision
    language `{x | ∃ y, R x y}` is in coNP. Since any FNP relation has its
    decision language in NP (by constructing an NTM that guesses and verifies a
    witness), membership in coFNP places the decision language in NP ∩ coNP. -/
def CoFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | {x | ∃ y, R x y} ∈ CoNP}

/-- **TFNP** is the class of total FNP search problems: every instance has at
    least one witness. -/
def TFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | ∀ x, ∃ y, R x y}
