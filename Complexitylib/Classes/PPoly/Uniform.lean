/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly
import Complexitylib.Classes.P
import Complexitylib.Circuits.Encoding.Family

/-!
# Uniform P/poly

The **P-uniform** polynomial-size circuit class. A circuit family is P-uniform when
its tagged code map `1ⁿ ↦ (code of the length-n member)` is computable by a
deterministic polynomial-time machine (`FP`). `UniformPPoly` restricts `PPoly` to
such families.

Uniformity is what makes a nonuniform circuit class comparable to a uniform machine
class: the headline `UniformPPoly = P` (roadmap M1) rests on this definition — the
easy containment `UniformPPoly ⊆ P` evaluates the generated code with a
polynomial-time DTM, and `P ⊆ UniformPPoly` unrolls a time-bounded DTM into a
P-uniform tableau family.

## Main definitions and results

- `unaryList` — the unary input `1ⁿ`.
- `CircuitFamily.Uniform` — P-uniformity of a family (its `encodeAt` code map is
  in `FP`).
- `UniformPPoly` — the P-uniform polynomial-size class.
- `UniformPPoly_subset_PPoly` — uniform P/poly is contained in nonuniform P/poly.
-/

namespace Complexity

/-- The unary encoding of `n` as `1ⁿ` (n `true` bits): the standard generator input
    that keeps generator time polynomial in `n` rather than in `log n`. -/
def unaryList (n : ℕ) : List Bool := List.replicate n true

/-- A circuit family is **P-uniform** when its tagged code map `1ⁿ ↦ (code of the
    length-n member)` is computable by a deterministic polynomial-time machine. The
    tagged `encodeAt` codec already carries the length-zero answer explicitly, so a
    single generator function produces the whole family. -/
def CircuitFamily.Uniform (F : CircuitFamily Basis.andOr2) : Prop :=
  ∃ gen ∈ FP, ∀ n, gen (unaryList n) = F.encodeAt n

/-- **Uniform P/poly**: languages decided by a P-uniform polynomial-size fan-in-two
    AND/OR circuit family. The uniform companion of `PPoly`; the M1 headline is
    `UniformPPoly = P`. -/
def UniformPPoly : Set Language :=
  { L | ∃ (F : CircuitFamily Basis.andOr2) (p : Polynomial ℕ),
      F.Decides L ∧ F.SizeBoundedBy (fun n => p.eval n) ∧ F.Uniform }

/-- **Uniform P/poly is contained in nonuniform P/poly.** Forgetting the uniformity
    generator leaves exactly a polynomial-size family deciding the language. -/
theorem UniformPPoly_subset_PPoly : UniformPPoly ⊆ PPoly := by
  rintro L ⟨F, p, hdec, hsize, -⟩
  exact Set.mem_iUnion.mpr ⟨p, F, hdec, hsize⟩

end Complexity
