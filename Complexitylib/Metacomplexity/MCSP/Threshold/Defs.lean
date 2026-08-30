/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Defs

/-!
# Threshold slices of MCSP -- definitions

Hardness-magnification statements normally fix a circuit-size threshold as a
function of the represented arity. This module retains the canonical full MCSP
codec, but restricts its threshold field to the chosen function. It also gives
a total re-encoding map that changes only that field.
-/


@[expose] public section

namespace Complexity

namespace MCSP

/-- Replace the threshold of every decodable MCSP instance by an arity-indexed
threshold. Malformed strings are fixed. -/
def rethreshold (threshold : ℕ → ℕ) (bits : List Bool) : List Bool :=
  match Instance.decode? bits with
  | some inst => (inst.withThreshold (threshold inst.arity)).encode
  | none => bits

/-- The canonical MCSP language restricted to instances whose encoded threshold
is the prescribed function of arity. -/
def atThreshold (threshold : ℕ → ℕ) : Set (List Bool) :=
  {bits | match Instance.decode? bits with
    | some inst =>
        inst.threshold = threshold inst.arity ∧ inst.HasCircuitAtMost
    | none => False}

end MCSP

end Complexity
