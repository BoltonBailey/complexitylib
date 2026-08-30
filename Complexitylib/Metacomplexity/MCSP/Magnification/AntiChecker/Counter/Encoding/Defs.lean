/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.Defs

/-!
# Anti-checker counter encodings -- definitions

Approximate counter circuits receive a fixed number of labeled samples. Each
sample occupies one row of `arity + 1` bits: its input coordinates in the
library's usual order, followed by the required output bit. Counter outputs
are interpreted as little-endian natural numbers, matching MCSP truth-table
indices.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Pack fixed-width labeled samples in row-major order. -/
def packLabeledSamples {count arity : ℕ}
    (samples : Fin count → SuccinctMCSP.Sample arity) :
    BitString (count * (arity + 1)) :=
  fun coordinate =>
    let position := finProdFinEquiv.symm coordinate
    Fin.lastCases (samples position.1).output
      (fun inputCoordinate => (samples position.1).input inputCoordinate)
      position.2

/-- Read one labeled sample from a row-major packed bit string. -/
def unpackLabeledSample {count arity : ℕ}
    (input : BitString (count * (arity + 1)))
    (sample : Fin count) : SuccinctMCSP.Sample arity where
  input := fun coordinate =>
    input (finProdFinEquiv (sample, coordinate.castSucc))
  output := input (finProdFinEquiv (sample, Fin.last arity))

/-- Split a packed bit string into its fixed-width labeled samples. -/
def unpackLabeledSamples {count arity : ℕ}
    (input : BitString (count * (arity + 1))) :
    Fin count → SuccinctMCSP.Sample arity :=
  fun sample => unpackLabeledSample input sample

/-- Pack inputs labeled by a target Boolean function. -/
def packTargetSamples {count arity : ℕ}
    (target : BitString arity → Bool)
    (inputs : Fin count → BitString arity) :
    BitString (count * (arity + 1)) :=
  packLabeledSamples (fun sample =>
    SuccinctMCSP.Sample.ofFunction target (inputs sample))

/-- Interpret a counter circuit's output as a little-endian natural number. -/
def counterValue {width : ℕ} (output : BitString width) : ℕ :=
  (MCSP.Instance.inputIndex output).val

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
