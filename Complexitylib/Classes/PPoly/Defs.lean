import Complexitylib.Circuits.Family.Defs
import Complexitylib.Circuits.AON.Defs
import Complexitylib.Models.TuringMachine

namespace Complexity

/-!
# Nonuniform circuit classes — definitions

This module defines language semantics for circuit families, pointwise circuit
size classes, and `PPoly`, the class conventionally written `P/poly`.

`PPoly` is initially specialized to the library's fan-in-two AND/OR basis with
free per-gate-input negation flags. Primary input vertices are also excluded
from `Circuit.size`. These choices preserve the usual polynomial-size class
after elementary overhead simulations, but exact `SIZE` bounds are
convention-dependent. Basis/size invariance must be proved rather than treated
as definitional.
-/

namespace BoolFunFamily

/-- The language whose characteristic function is `f`, using the canonical
    list-to-fixed-length representation. -/
def toLanguage (f : BoolFunFamily) : Language :=
  {x | f x.length x.get = true}

end BoolFunFamily

namespace CircuitFamily

variable {B : Basis}

/-- The language recognized by a circuit family. -/
def language (F : CircuitFamily B) : Language :=
  F.function.toLanguage

/-- `F` decides `L` when its recognized language is exactly `L`. -/
def Decides (F : CircuitFamily B) (L : Language) : Prop :=
  F.language = L

end CircuitFamily

/-- Languages decided by `B`-circuit families with the pointwise size bound
    `s`, using this library's non-input-gate count. -/
def SIZEWithBasis (B : Basis) (s : ℕ → ℕ) : Set Language :=
  {L | ∃ F : CircuitFamily B, F.Decides L ∧ F.SizeBoundedBy s}

/-- The fan-in-two AND/OR circuit-size class under the library's free-negation,
    non-input-gate convention. -/
def SIZE (s : ℕ → ℕ) : Set Language :=
  SIZEWithBasis Basis.andOr2 s

/-- **P/poly**: languages decided by polynomial-size nonuniform fan-in-two
    AND/OR circuit families under the library's size convention. -/
def PPoly : Set Language :=
  {L | ∃ F : CircuitFamily Basis.andOr2, F.Decides L ∧ F.PolynomialSize}

end Complexity
