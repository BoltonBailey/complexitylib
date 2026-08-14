/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Nondeterministic
public import Complexitylib.Models.TuringMachine.Composition.Internal.NondetPrefix

/-!
# Trace factorization through the deterministic prefix

Every trace of `NTM.compositionNTM tmF N` — along *any* choice sequence —
first runs the deterministic pipeline (first computation, output rewind,
copy, virtual-input rewind) without consulting a single choice bit. The
trace therefore factors through the `DetPrefixBoundary` configuration in
which the virtual input holds `f x`, after which only the placed
retargeted copy of `N` runs.

The choice-independence is packaged by `NTM.compositionNTM_trace_prefix`:
the length-`(s + t)` trace equals the length-`s` trace restarted from the
boundary with the first `t` choices discarded.
-/


public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- **Trace factorization through the deterministic prefix.** There is a
    boundary configuration `E` (holding `f x` on the virtual-input tape)
    and a prefix length `t ≤ 4 * TF |x| + 10` such that every trace of the
    composite factors through `E`, with the first `t` choice bits ignored. -/
theorem compositionNTM_trace_prefix (tmF : TM nf) (N : NTM ng)
    {f : List Bool → List Bool} {TF : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF) (x : List Bool) :
    ∃ (E : Cfg (TM.compositionTapeCount nf ng) (compositionNTM tmF N).Q) (t : ℕ),
      t ≤ 4 * TF x.length + 10 ∧
      DetPrefixBoundary tmF N (f x) E ∧
      ∀ (s : ℕ) (choices : Fin (s + t) → Bool),
        (compositionNTM tmF N).trace (s + t) choices
            ((compositionNTM tmF N).initCfg x) =
          (compositionNTM tmF N).trace s
            (fun i => choices ⟨i.val + t, by omega⟩) E := by
  obtain ⟨E, t, ht, hvia, hboundary⟩ :=
    compositionNTM_detPrefix_internal tmF N hF x
  exact ⟨E, t, ht, hboundary, fun s choices => trace_of_det_prefix hvia s choices⟩

end NTM

end Complexity
