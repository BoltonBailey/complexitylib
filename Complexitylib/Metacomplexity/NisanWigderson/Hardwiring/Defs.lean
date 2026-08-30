/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.BooleanDependency.Defs
public import Complexitylib.Metacomplexity.NisanWigderson.Defs
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Nisan--Wigderson overlap hardwiring -- definitions

Fixing an NW output coordinate turns its block input into a challenge and leaves
all seed coordinates outside that block fixed. A predecessor block can then vary
only through the challenge coordinates lying in the two blocks' intersection.
This module defines that challenge experiment and its canonical hardwiring table.
-/


@[expose] public section

namespace Complexity

namespace NWDesign

/-- Challenge coordinates of `current` whose seed positions also occur in
`previous`. -/
def challengeOverlap {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength) : Finset (Fin inputLength) :=
  Finset.univ.filter fun input =>
    design.coordinates current input ∈ design.support previous

/-- Replace the seed coordinates in one design block by a challenge, retaining
an outside assignment on every other coordinate. The finite inverse of the
block embedding makes this operation executable. -/
def seedWithChallenge {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) (outside : Fin seedLength → Bool)
    (challenge : Fin inputLength → Bool) : Fin seedLength → Bool :=
  fun coordinate =>
    if hcoordinate : coordinate ∈ Set.range (design.coordinates current) then
      challenge ((design.coordinates current).toEquivRange.symm
        ⟨coordinate, hcoordinate⟩)
    else
      outside coordinate

/-- The input seen by a block when `current` carries the challenge and all
coordinates outside `current` are fixed. -/
def challengedBlock {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool) :
    (Fin inputLength → Bool) → (Fin inputLength → Bool) :=
  fun challenge =>
    design.restrictSeed previous
      (design.seedWithChallenge current outside challenge)

/-- The canonical advice table for an observed predecessor-block value. Its
indices are assignments to precisely the overlap coordinates. -/
def predecessorTable {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current previous : Fin outputLength)
    (outside : Fin seedLength → Bool)
    (observe : (Fin inputLength → Bool) → Bool) :
    (design.challengeOverlap current previous → Bool) → Bool :=
  BooleanDependency.table (design.challengeOverlap current previous)
    (fun challenge => observe (design.challengedBlock current previous outside challenge))

/-- Total number of Boolean entries in all predecessor tables at one output
coordinate. -/
def predecessorTableEntriesAt {outputLength inputLength seedLength : ℕ}
  (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) : ℕ :=
  ∑ previous ∈ Finset.Iio current,
    Fintype.card (design.challengeOverlap current previous → Bool)

end NWDesign

end Complexity
