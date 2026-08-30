/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputSources.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Iteration.Defs

/-!
# Anti-checker generator output padding -- definitions

The selection circuit prints the inputs chosen during the shrinking rounds.
This module prepends all-zero sample rows until the packed output has the
published sample count, matching `AntiChecker.padInputsTo` exactly.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Prepend all-zero rows to a row-major packed sample vector. -/
def padPackedSamples {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (input : BitString (sourceCount * arity)) :
    BitString (targetCount * arity) :=
  fun output =>
    let position := finProdFinEquiv.symm output
    Fin.append
      (fun _ : Fin (targetCount - sourceCount) => false)
      (fun sourceSample => unpackSample input sourceSample position.2)
      (Fin.cast (Nat.sub_add_cancel hbudget).symm position.1)

/-- One source of a packed-sample padding circuit. Padding rows are constant
false; remaining rows copy the corresponding source coordinate. -/
def packedSamplePaddingSource {sourceCount targetCount arity : ℕ}
    (hbudget : sourceCount ≤ targetCount)
    (output : Fin (targetCount * arity)) :
    Circuit.InputSource (sourceCount * arity) :=
  let position := finProdFinEquiv.symm output
  Fin.addCases
    (fun _ => .constant false)
    (fun sourceSample =>
      .input (finProdFinEquiv (sourceSample, position.2)))
    (Fin.cast (Nat.sub_add_cancel hbudget).symm position.1)

/-- Zero-internal-gate circuit that prepends all-zero rows to a packed sample
vector. -/
def packedSamplePaddingCircuit
    {sourceCount targetCount arity : ℕ}
    [NeZero (sourceCount * arity)] [NeZero (targetCount * arity)]
    (hbudget : sourceCount ≤ targetCount) :
    Circuit Basis.andOr2 (sourceCount * arity) (targetCount * arity) 0 :=
  Circuit.inputSources (packedSamplePaddingSource hbudget)

/-- Full required-round selection followed by zero padding to the published
number of sample rows. -/
noncomputable def paddedSelectionCircuit
    {overhead arity : ℕ} {beta : PositiveRationalScale} [NeZero arity]
    (family : ApproximateCounterFamily overhead beta arity)
    (hbudget : requiredRoundCount beta arity ≤ sampleCount beta arity) :
    Σ internalGates,
      Circuit Basis.andOr2 (2 ^ arity)
        (outputBitCount beta arity) internalGates :=
  let selected := fullSelectionSamplesCircuit family
  let padding := packedSamplePaddingCircuit (arity := arity) hbudget
  ⟨_, padding.compose selected.2⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
