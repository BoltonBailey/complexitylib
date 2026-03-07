import Complexitylib.Classes.Pairing
import Complexitylib.Classes.P

/-!
# FNP and TFNP

This file defines the function/search complexity classes **FNP** and **TFNP**.

An FNP search problem is specified by a binary relation `R` that is polynomially
balanced and decidable in polynomial time. The search task is: given `x`, find `y`
with `R x y`, or report that none exists.
-/

/-- **FNP** is the class of search problems defined by NP relations: binary
    relations that are polynomially balanced and decidable in polynomial time.
    A relation `R` is in FNP if witnesses have poly-bounded length and the
    pair language `{pair(x, y) | R x y}` is in P. -/
def FNP : Set (List Bool → List Bool → Prop) :=
  {R | PolyBalanced R ∧ pairLang R ∈ P}

/-- **TFNP** is the class of total FNP search problems: every instance has at
    least one witness. -/
def TFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | ∀ x, ∃ y, R x y}
