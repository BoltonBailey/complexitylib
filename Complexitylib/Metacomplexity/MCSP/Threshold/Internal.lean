/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Threshold.Defs
import Complexitylib.Metacomplexity.MCSP.Internal

/-!
# Threshold slices of MCSP -- proof internals
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

theorem minimumSize_withThreshold_internal (inst : Instance) (threshold : ℕ) :
    (inst.withThreshold threshold).minimumSize = inst.minimumSize := by
  rfl

end Instance

theorem decode?_rethreshold_of_decode?_eq_some_internal
    (threshold : ℕ → ℕ) {bits : List Bool} {inst : Instance}
    (hdecode : Instance.decode? bits = some inst) :
    Instance.decode? (rethreshold threshold bits) =
      some (inst.withThreshold (threshold inst.arity)) := by
  simp [rethreshold, hdecode, Instance.decode?_encode_internal]

theorem rethreshold_encode_internal (threshold : ℕ → ℕ) (inst : Instance) :
    rethreshold threshold inst.encode =
      (inst.withThreshold (threshold inst.arity)).encode := by
  simp [rethreshold, Instance.decode?_encode_internal]

theorem rethreshold_comp_internal
    (first second : ℕ → ℕ) (bits : List Bool) :
    rethreshold second (rethreshold first bits) =
      rethreshold second bits := by
  cases hdecode : Instance.decode? bits with
  | none => simp [rethreshold, hdecode]
  | some inst =>
      simp [rethreshold, hdecode, Instance.decode?_encode_internal,
        Instance.withThreshold]

theorem length_rethreshold_of_decode?_eq_some_internal
    (threshold : ℕ → ℕ) {bits : List Bool} {inst : Instance}
    (hdecode : Instance.decode? bits = some inst) :
    (rethreshold threshold bits).length + 2 * inst.threshold.size =
      bits.length + 2 * (threshold inst.arity).size := by
  have hbits :=
    (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
  subst bits
  rw [rethreshold_encode_internal, Instance.length_encode_internal,
    Instance.length_encode_internal]
  simp [Instance.withThreshold]
  omega

theorem mem_atThreshold_encode_iff_internal
    (threshold : ℕ → ℕ) (inst : Instance) :
    inst.encode ∈ atThreshold threshold ↔
      inst.threshold = threshold inst.arity ∧ inst.HasCircuitAtMost := by
  simp [atThreshold, Instance.decode?_encode_internal]

theorem rethreshold_encode_mem_atThreshold_iff_internal
    (threshold : ℕ → ℕ) (inst : Instance) :
    rethreshold threshold inst.encode ∈ atThreshold threshold ↔
      (inst.withThreshold (threshold inst.arity)).HasCircuitAtMost := by
  rw [rethreshold_encode_internal, mem_atThreshold_encode_iff_internal]
  simp [Instance.withThreshold]

end MCSP

end Complexity
