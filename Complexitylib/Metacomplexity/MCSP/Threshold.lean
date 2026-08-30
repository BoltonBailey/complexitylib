/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Threshold.Defs
public import Complexitylib.Metacomplexity.MCSP.Threshold.Internal

/-!
# Threshold slices of MCSP

This module exposes the arity-indexed language `MCSP.atThreshold s` and its
canonical total re-encoding map. The exact length theorem retains the binary
width of both the old and new threshold rather than hiding it in asymptotic
notation.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

/-- Changing an instance threshold preserves its minimum circuit size. -/
@[simp] theorem minimumSize_withThreshold (inst : Instance) (threshold : ℕ) :
    (inst.withThreshold threshold).minimumSize = inst.minimumSize :=
  minimumSize_withThreshold_internal inst threshold

end Instance

/-- Rethresholding a decodable code produces the corresponding canonical code. -/
theorem decode?_rethreshold_of_decode?_eq_some
    (threshold : ℕ → ℕ) {bits : List Bool} {inst : Instance}
    (hdecode : Instance.decode? bits = some inst) :
    Instance.decode? (rethreshold threshold bits) =
      some (inst.withThreshold (threshold inst.arity)) :=
  decode?_rethreshold_of_decode?_eq_some_internal threshold hdecode

/-- Rethresholding a canonical code changes only its threshold field. -/
@[simp] theorem rethreshold_encode (threshold : ℕ → ℕ) (inst : Instance) :
    rethreshold threshold inst.encode =
      (inst.withThreshold (threshold inst.arity)).encode :=
  rethreshold_encode_internal threshold inst

/-- Only the final requested threshold matters after repeated re-encoding. -/
theorem rethreshold_comp (first second : ℕ → ℕ) (bits : List Bool) :
    rethreshold second (rethreshold first bits) = rethreshold second bits :=
  rethreshold_comp_internal first second bits

/-- Exact output-length accounting for rethresholding a decodable instance. -/
theorem length_rethreshold_of_decode?_eq_some
    (threshold : ℕ → ℕ) {bits : List Bool} {inst : Instance}
    (hdecode : Instance.decode? bits = some inst) :
    (rethreshold threshold bits).length + 2 * inst.threshold.size =
      bits.length + 2 * (threshold inst.arity).size :=
  length_rethreshold_of_decode?_eq_some_internal threshold hdecode

/-- Canonical membership in a threshold slice exposes both the forced threshold
field and the ordinary MCSP predicate. -/
@[simp] theorem mem_atThreshold_encode_iff
    (threshold : ℕ → ℕ) (inst : Instance) :
    inst.encode ∈ atThreshold threshold ↔
      inst.threshold = threshold inst.arity ∧ inst.HasCircuitAtMost :=
  mem_atThreshold_encode_iff_internal threshold inst

/-- Rethresholding always installs the requested threshold, leaving exactly the
corresponding circuit-size question. -/
theorem rethreshold_encode_mem_atThreshold_iff
    (threshold : ℕ → ℕ) (inst : Instance) :
    rethreshold threshold inst.encode ∈ atThreshold threshold ↔
      (inst.withThreshold (threshold inst.arity)).HasCircuitAtMost :=
  rethreshold_encode_mem_atThreshold_iff_internal threshold inst

end MCSP

end Complexity
