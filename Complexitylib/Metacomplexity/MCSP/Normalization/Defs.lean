/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Asymptotics.PolyBound
public import Complexitylib.Classes.Pairing
public import Complexitylib.Metacomplexity.MCSP.Witness.Defs

/-!
# Threshold normalization for MCSP -- definitions

Binary thresholds can denote values exponentially larger than their encoded
width. MCSP nevertheless has an unconditional circuit-size upper bound that is
polynomial in truth-table length. This layer caps thresholds at a concrete
bound without changing yes/no semantics and defines the resulting polynomial
raw-witness envelope.
-/


@[expose] public section

namespace Complexity

namespace MCSP

namespace Instance

/-- Coarse unconditional circuit-size bound for the represented function.

For positive arity this is the square of truth-table length plus two. Arity
zero retains the separate size-zero convention. -/
def trivialCircuitSizeBound (inst : Instance) : ℕ :=
  if inst.arity = 0 then 0 else (2 ^ inst.arity + 2) ^ 2

/-- Threshold capped at the unconditional circuit-size upper bound. -/
def effectiveThreshold (inst : Instance) : ℕ :=
  min inst.threshold inst.trivialCircuitSizeBound

/-- Replace an instance's possibly oversized threshold by its effective cap. -/
def normalizeThreshold (inst : Instance) : Instance :=
  inst.withThreshold inst.effectiveThreshold

/-- Polynomial envelope for a normalized raw-circuit witness, expressed only
in the encoded instance length. -/
def rawWitnessLengthPolynomial (inputLength : ℕ) : ℕ :=
  let sizeBound := (inputLength + 2) ^ 2
  1 + sizeBound * (2 * (inputLength + sizeBound) + 6)

end Instance

/-- Polynomially balanced raw-circuit relation used by the MCSP verifier.

The input must decode canonically, and the witness is checked against the
semantics-preserving normalized threshold rather than an arbitrarily large
binary threshold from the input. -/
def RawWitnessRelation (bits witness : List Bool) : Prop :=
  match Instance.decode? bits with
  | none => False
  | some inst => inst.normalizeThreshold.IsRawCircuitWitness witness

end MCSP

end Complexity
