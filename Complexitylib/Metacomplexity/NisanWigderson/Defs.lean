/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Defs

/-!
# Nisan--Wigderson set systems and generators -- definitions

An `NWDesign m ell d` is an ordered family of `m` injectively enumerated
`ell`-coordinate subsets of a `d`-bit seed. Injective enumerations avoid
cardinality casts when restricting a seed and retain the coordinate order used
by the hard Boolean function.

The exact weak-design resource is recorded as a natural-number overlap cost.
At output coordinate `i`, it is the sum of `2^|S_i ∩ S_j|` over predecessors
`j < i`, plus one unit for every later output coordinate. A separate predicate
bounds this cost uniformly, allowing later analytic estimates to choose their
own integer upper bound.
-/


@[expose] public section

namespace Complexity

/-- An ordered family of injectively enumerated coordinate subsets for the
Nisan--Wigderson generator. -/
structure NWDesign (outputLength inputLength seedLength : ℕ) where
  /-- The `inputLength` distinct seed coordinates used by each output bit. -/
  coordinates : Fin outputLength → Fin inputLength ↪ Fin seedLength

namespace NWDesign

/-- The underlying coordinate set of one design block. -/
def support {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) : Finset (Fin seedLength) :=
  Finset.univ.map (design.coordinates output)

/-- Cardinality of the intersection of two design blocks. -/
def overlap {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (first second : Fin outputLength) : ℕ :=
  ((design.support first) ∩ (design.support second)).card

/-- Exact predecessor-overlap resource at one output coordinate, including
one unit for each later output coordinate as in Hirahara's weak-design bound. -/
def overlapCostAt {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) : ℕ :=
  (∑ previous ∈ Finset.Iio output,
      2 ^ design.overlap output previous) +
    (outputLength - (output.val + 1))

/-- Every coordinate's exact overlap cost is at most `budget`. -/
def HasOverlapBudget {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (budget : ℕ) : Prop :=
  ∀ output, design.overlapCostAt output ≤ budget

/-- Restrict a seed to the ordered coordinates of one design block. -/
def restrictSeed {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (seed : Fin seedLength → Bool) :
    Fin inputLength → Bool :=
  fun input => seed (design.coordinates output input)

/-- The Nisan--Wigderson generator associated to a design and a Boolean
function on one design block. -/
def generator {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool) :
    BitGenerator seedLength outputLength :=
  fun seed output => hardFunction (design.restrictSeed output seed)

end NWDesign

end Complexity
