import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial
import Complexitylib.Classes.P
import Complexitylib.Classes.NP

/-!
# FNP, coFNP, and TFNP

This file defines the function/search complexity classes **FNP**, **coFNP**, and
**TFNP** (Arora-Barak Section 2.2).

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

/-- **FNP** is the class of search problems defined by NP relations: binary
    relations that are polynomially balanced and decidable in polynomial time.
    A relation `R` is in FNP if witnesses have poly-bounded length and the
    language `{pair(x, y) | R x y}` is in P (Arora-Barak Section 2.2). -/
def FNP : Set (List Bool → List Bool → Prop) :=
  {R | (∃ p, IsPolyBounded p ∧ ∀ x y, R x y → y.length ≤ p x.length) ∧
       {z | ∃ x y, z = pair x y ∧ R x y} ∈ P}

/-- **coFNP** is the class of search problems whose associated decision language
    `{x | ∃ y, R x y}` is in coNP (Arora-Barak Section 2.2). -/
def CoFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | {x | ∃ y, R x y} ∈ CoNP}

/-- **TFNP** is the class of total FNP search problems: every instance has at
    least one witness (Arora-Barak Section 2.2). -/
def TFNP : Set (List Bool → List Bool → Prop) :=
  {R ∈ FNP | ∀ x, ∃ y, R x y}
