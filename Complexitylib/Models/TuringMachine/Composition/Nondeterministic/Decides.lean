/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Composition.Nondeterministic.Trace

/-!
# Deterministic preprocessing before a nondeterministic decider

`NTM.compositionNTM_decidesInTime`: if `tmF` computes `f` in time `TF` and
`N` decides `L` within a monotone bound `TG`, then the composite decides the
preimage `f ⁻¹' L` within `4·TF(n) + 11 + TG(TF(n))` — the same coarse
pipeline bound as the deterministic composition, with the decider's budget
evaluated at the output-length bound `TF(n)`.

The hypothesis `N.qstart ≠ N.qhalt` excludes the degenerate machine that
starts halted; such a machine accepts nothing, so a client can decide the
preimage of its (empty) language without running the composite at all.
-/


public section

namespace Complexity

namespace NTM

variable {nf ng : ℕ}

/-- **Preprocessing before a nondeterministic decider.** The composite
    decides the preimage language within the composed budget. -/
theorem compositionNTM_decidesInTime {tmF : TM nf} {N : NTM ng}
    {f : List Bool → List Bool} {L : Language} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime f TF) (hN : N.DecidesInTime L TG)
    (hmono : Monotone TG) (hne : N.qstart ≠ N.qhalt) :
    (compositionNTM tmF N).DecidesInTime (f ⁻¹' L)
      (fun n => 4 * TF n + 11 + TG (TF n)) := by
  have hread_ns : ∀ tp : Tape, tp.StartInvariant → 1 ≤ tp.head →
      tp.read ≠ Γ.start := fun tp hinv hh => hinv.2 tp.head hh
  -- Halting of `N` at any budget past `TG` on a fixed input.
  have hNhaltAt : ∀ (z : List Bool) (m : ℕ), TG z.length ≤ m →
      ∀ ch : Fin m → Bool, N.halted (N.trace m ch (N.initCfg z)) := by
    intro z m hm ch
    have heq := N.trace_mono hm (choices := fun i => ch ⟨i.val, by omega⟩)
      (choices' := ch) (c := N.initCfg z) (fun i => rfl)
      (hN.1 z (fun i => ch ⟨i.val, by omega⟩))
    rw [heq]
    exact hN.1 z _
  constructor
  · -- All paths halt within the composed budget.
    intro x
    dsimp only
    obtain ⟨E, t, ht, hB, hrun⟩ := compositionNTM_trace_run tmF N hF x hne
    have hylen : (f x).length ≤ TF x.length := hF.output_length_le x
    have harith : ((4 * TF x.length + 11 + TG (TF x.length)) - t - 1 + 1) + t =
        4 * TF x.length + 11 + TG (TF x.length) := by omega
    rw [← harith]
    intro choices
    rw [hrun _ choices]
    refine (placedCfg_halted_iff tmF N E.work E.input _).mpr ?_
    exact hNhaltAt (f x) _ (by
      have := hmono hylen
      omega) _
  · -- Acceptance is exactly membership in the preimage.
    intro x
    dsimp only
    obtain ⟨E, t, ht, hB, hrun⟩ := compositionNTM_trace_run tmF N hF x hne
    have hylen : (f x).length ≤ TF x.length := hF.output_length_le x
    have harith : ((4 * TF x.length + 11 + TG (TF x.length)) - t - 1 + 1) + t =
        4 * TF x.length + 11 + TG (TF x.length) := by omega
    have hsle : TG (f x).length ≤
        (4 * TF x.length + 11 + TG (TF x.length)) - t - 1 + 1 := by
      have := hmono hylen
      omega
    constructor
    · intro hx
      have hacc := ((hN.2 (f x)).mp hx).mono hsle
      obtain ⟨ch', hhalt', hout'⟩ := hacc
      rw [← harith]
      refine ⟨fun j => ch' ⟨j.val - t, by omega⟩, ?_, ?_⟩ <;>
        rw [hrun _ _] <;>
        simp only [Nat.add_sub_cancel, Fin.eta]
      · exact (placedCfg_halted_iff tmF N E.work E.input _).mpr hhalt'
      · exact hout'
    · intro hacc
      rw [← harith] at hacc
      obtain ⟨ch, hhalt, hout⟩ := hacc
      rw [hrun _ ch] at hhalt hout
      have hNacc : N.AcceptsInTime (f x)
          ((4 * TF x.length + 11 + TG (TF x.length)) - t - 1 + 1) :=
        ⟨_, (placedCfg_halted_iff tmF N E.work E.input _).mp hhalt, hout⟩
      refine (hN.2 (f x)).mpr ?_
      exact acceptsInTime_of_le_of_allPathsHaltIn (tm := N)
        (T := TG)
        (T' := fun m => max (TG m)
          ((4 * TF x.length + 11 + TG (TF x.length)) - t - 1 + 1))
        (fun m => le_max_left _ _) hN.1
        (hNacc.mono (le_max_right _ _))

end NTM

end Complexity
