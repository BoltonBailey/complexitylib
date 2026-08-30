/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Defs
public import Complexitylib.Classes.EventProb

/-!
# Finite incompressibility -- definitions

This layer packages all binary programs of length at most a bound and the
finite sets of fixed-length strings whose machine-relative time-bounded
Kolmogorov complexity is below or above that bound.
-/


@[expose] public section

namespace Complexity

/-- A binary program of length strictly below `bound`. -/
abbrev StrictShortProgram (bound : ℕ) :=
  Σ length : Fin bound, Fin length.val → Bool

namespace StrictShortProgram

/-- Forget the strict length certificate and recover the variable-length program. -/
def toList {bound : ℕ} (program : StrictShortProgram bound) : List Bool :=
  List.ofFn program.2

/-- Package a variable-length program with a strict length certificate. -/
def ofList (bound : ℕ) (program : List Bool) (hlength : program.length < bound) :
    StrictShortProgram bound :=
  ⟨⟨program.length, hlength⟩, program.get⟩

end StrictShortProgram

/-- A binary program of length at most `bound`, represented by its length and
fixed-length contents. -/
abbrev ShortProgram (bound : ℕ) :=
  Σ length : Fin (bound + 1), Fin length.val → Bool

namespace ShortProgram

/-- Forget the length certificate and recover the variable-length program. -/
def toList {bound : ℕ} (program : ShortProgram bound) : List Bool :=
  List.ofFn program.2

/-- Package a variable-length program with a proof that it meets the bound. -/
def ofList (bound : ℕ) (program : List Bool) (hlength : program.length ≤ bound) :
    ShortProgram bound :=
  ⟨⟨program.length, Nat.lt_succ_iff.mpr hlength⟩, program.get⟩

end ShortProgram

namespace TM

variable {tapes : ℕ}

/-- Fixed-length strings having a description strictly shorter than
`threshold` within the specified clock. This is the exact low-complexity event
used by strict-threshold MINKT. -/
noncomputable def timeBoundedStrictlyCompressibleStrings (machine : TM tapes)
    (outputLength time threshold : ℕ) : Finset (Fin outputLength → Bool) := by
  classical
  exact Finset.univ.filter fun output =>
    machine.timeBoundedKolmogorovComplexity (List.ofFn output) time <
      (threshold : WithTop ℕ)

/-- Fixed-length `threshold`-random strings, namely those whose time-bounded
complexity is at least `threshold`. -/
noncomputable def timeBoundedRandomStrings (machine : TM tapes)
    (outputLength time threshold : ℕ) : Finset (Fin outputLength → Bool) := by
  classical
  exact (machine.timeBoundedStrictlyCompressibleStrings
    outputLength time threshold)ᶜ

/-- Fixed-length strings having a description of length at most `bound` within
the specified clock. -/
noncomputable def timeBoundedCompressibleStrings (machine : TM tapes)
    (outputLength time bound : ℕ) : Finset (Fin outputLength → Bool) := by
  classical
  exact Finset.univ.filter fun output =>
    machine.timeBoundedKolmogorovComplexity (List.ofFn output) time ≤
      (bound : WithTop ℕ)

/-- Fixed-length strings whose time-bounded complexity exceeds `bound`. -/
noncomputable def timeBoundedIncompressibleStrings (machine : TM tapes)
    (outputLength time bound : ℕ) : Finset (Fin outputLength → Bool) := by
  classical
  exact (machine.timeBoundedCompressibleStrings outputLength time bound)ᶜ

end TM

end Complexity
