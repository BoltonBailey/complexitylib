/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.PPoly.Uniform
import Complexitylib.Classes.PPoly.Uniform.Unrolling

/-!
# Deterministic unrolling into uniform P/poly -- proof internals

This module packages the direct deterministic unrolling family once its exact
code map is known to belong to `FL`. The actual streaming-generator
construction remains separate.
-/

namespace Complexity

namespace TM

/-- Internal packaging of one polynomial-time decider and its direct-code
generator as a logspace-uniform polynomial-size circuit family. -/
theorem DecidesInTime.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    {tm : TM k} {L : Language} (q : Polynomial ℕ)
    (hdec : tm.DecidesInTime L q.eval)
    (hgen : (fun x : List Bool =>
      tm.directUnrollingCode q.eval x.length) ∈ FL) :
    L ∈ UniformPPoly := by
  let F := tm.directUnrollingCircuitFamily q.eval
  have hq : q.eval =O ((· ^ q.natDegree) : ℕ → ℕ) :=
    BigO.of_polynomial_bound q (fun _ => le_rfl)
  have hsizeO : F.size =O ((· ^ (3 * q.natDegree)) : ℕ → ℕ) := by
    dsimp only [F]
    exact tm.directUnrollingCircuitFamily_size_bigO hq
  obtain ⟨sizePoly, hsize⟩ := BigO.pow_polynomial_bound hsizeO
  refine ⟨F, sizePoly, ?_, hsize, ?_⟩
  · dsimp only [F]
    exact hdec.directUnrollingCircuitFamily_decides
  · refine ⟨(fun x => tm.directUnrollingCode q.eval x.length), hgen, ?_⟩
    intro n
    simpa only [F, unaryList, List.length_replicate] using
      (tm.directUnrollingCircuitFamily_encodeAt q.eval n).symm

end TM

/-- Internal conditional containment: if every polynomial-horizon direct
unrolling code map belongs to `FL`, then `P` is contained in uniform P/poly. -/
theorem P_subset_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    (hgen : ∀ {k : ℕ} (tm : TM k) (q : Polynomial ℕ),
      (fun x : List Bool => tm.directUnrollingCode q.eval x.length) ∈ FL) :
    P ⊆ UniformPPoly := by
  intro L hL
  obtain ⟨k, tm, q, hdec⟩ :=
    mem_P_iff_decidesInTime_polynomial.mp hL
  exact hdec.mem_UniformPPoly_of_directUnrollingCode_mem_FL_internal
    q (hgen tm q)

end Complexity
