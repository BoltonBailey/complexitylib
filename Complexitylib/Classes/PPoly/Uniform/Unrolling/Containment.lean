/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Containment.Internal

/-!
# Conditional deterministic unrolling into uniform P/poly

This module exposes the final packaging seam for the machines-to-circuits
direction of uniform P/poly. It deliberately assumes that an exact direct or
regularly padded unrolling code map belongs to `FL`; the streaming serializer
must discharge that hypothesis separately.

## Main results

- `TM.DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL` packages
  one polynomial-time decider and direct-code generator.
- `P_subset_UniformPPoly_of_directUnrollingCode_mem_FL` packages the resulting
  conditional class containment.
- The corresponding `paddedDirectUnrollingCode` theorems target the regular
  family whose gate-count header is known before gate emission begins.
-/

namespace Complexity

namespace TM

/-- A polynomial-time decider belongs to uniform P/poly whenever its direct
unrolling code map is computable in logarithmic space. -/
theorem DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.directUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly :=
  hdec.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal q hgen

/-- A polynomial-time decider belongs to uniform P/poly whenever its regularly
padded exact code map is computable in logarithmic space. -/
theorem DecidesInTime.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly :=
  hdec.mem_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal q hgen

end TM

/-- If every polynomial-horizon direct unrolling code map belongs to `FL`,
then every language in `P` has a logspace-uniform polynomial-size circuit
family. -/
theorem P_subset_UniformPPoly_of_directUnrollingCode_mem_FL
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool => tm.directUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly :=
  P_subset_UniformPPoly_of_directUnrollingCode_mem_FL_internal hgen

/-- If every polynomial-horizon padded unrolling code map belongs to `FL`,
then every language in `P` has a logspace-uniform polynomial-size family. -/
theorem P_subset_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool =>
        tm.paddedDirectUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly :=
  P_subset_UniformPPoly_of_paddedDirectUnrollingCode_mem_FL_internal hgen

end Complexity
