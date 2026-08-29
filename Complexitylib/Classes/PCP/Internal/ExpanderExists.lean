/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ExpanderRandom
public import Complexitylib.Classes.PCP.Internal.PermGraph
public import Complexitylib.Classes.PCP.Internal.Cheeger
public import Complexitylib.Classes.PCP.Internal.Expander

/-!
# An expander family exists

The three strands meet here. `ExpanderRandom` produces, for every `n`, thirty
permutations of `Fin n` no vertex set of at most half the vertices survives;
`PermGraph` turns those into a `60`-regular graph with edge expansion `1/600`;
and `Cheeger` converts edge expansion into a spectral gap once enough self-loops
are added to make the walk lazy. Relabelling the resulting `120` darts as
`Fin 120` puts the graph in the rotation-map form `ExpanderFamily` asks for.

The construction is not explicit — the permutations come from
`Classical.choose` on a counting argument — which is all the mathematics of
Dinur's proof needs. An explicit family would be needed only to make the
reduction itself polynomial-time computable.

## Main definitions

- `Complexity.goodPerms` — the chosen permutations
- `Complexity.randExpander` — the resulting `ExpanderFamily`
-/

@[expose] public section

namespace Complexity

/-- Thirty permutations of `Fin n` that expand every small set. -/
noncomputable def goodPerms (n : ℕ) : Fin 30 → Equiv.Perm (Fin n) :=
  Classical.choose (exists_good_perms n)

theorem goodPerms_spec (n : ℕ) (S : Finset (Fin n)) (hS : 2 * S.card ≤ n) :
    ∃ i, S.card ≤ 10 * escape (goodPerms n i) S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⟨0, by norm_num⟩, by simp⟩
  · exact Classical.choose_spec (exists_good_perms n) S hS hne

/-- The `60`-regular graph of those permutations. -/
noncomputable def baseGraph (n : ℕ) : RegGraph :=
  RegGraph.permsGraph (by norm_num : (0 : ℕ) < 30) (goodPerms n)

theorem edgeExpansion_baseGraph (n : ℕ) :
    (baseGraph n).EdgeExpansion (1 / (2 * (10 : ℝ) * 30)) :=
  RegGraph.edgeExpansion_permsGraph _ _ 10 (by norm_num) (goodPerms_spec n)

theorem deg_baseGraph (n : ℕ) : (baseGraph n).deg = 60 := by
  rw [baseGraph, RegGraph.deg_permsGraph]

/-- The lazy walk on it: a self-loop for every dart. -/
noncomputable def lazyGraph (n : ℕ) : RegGraph := (baseGraph n).padLoops (baseGraph n).deg

/-- The spectral bound the construction achieves. -/
noncomputable def randLam : ℝ := 1 - (1 / (2 * (10 : ℝ) * 30)) ^ 2 / 4

theorem randLam_nonneg : 0 ≤ randLam := by
  rw [randLam]
  norm_num

theorem randLam_lt_one : randLam < 1 := by
  rw [randLam]
  norm_num

theorem spectral_lazyGraph (n : ℕ) : (lazyGraph n).SpectralBound randLam :=
  RegGraph.spectralBound_padLoops_of_edgeExpansion _ (edgeExpansion_baseGraph n) (by norm_num)

theorem deg_lazyGraph (n : ℕ) : (lazyGraph n).deg = 120 := by
  rw [lazyGraph, RegGraph.deg_padLoops, deg_baseGraph]

theorem card_lazyDarts (n : ℕ) : Fintype.card (lazyGraph n).D = 120 := deg_lazyGraph n

/-- The darts of the lazy graph, named by `Fin 120`. -/
noncomputable def dartEquiv (n : ℕ) : (lazyGraph n).D ≃ Fin 120 :=
  Fintype.equivFinOfCardEq (card_lazyDarts n)

/-- The graph on `n` vertices with `Fin 120` darts. -/
noncomputable def randGraph (n : ℕ) : RegGraph := (lazyGraph n).relabel (dartEquiv n)

theorem spectral_randGraph (n : ℕ) : (randGraph n).SpectralBound randLam :=
  RegGraph.spectralBound_relabel _ _ (spectral_lazyGraph n)

/-- Its rotation map, as data on `Fin n × Fin 120`. -/
noncomputable def randRot (n : ℕ) : Fin n × Fin 120 → Fin n × Fin 120 := (randGraph n).rot

theorem randRot_involutive (n : ℕ) : Function.Involutive (randRot n) :=
  (randGraph n).rot_involutive

theorem ofRot_randRot (n : ℕ) :
    RegGraph.ofRot 120 (by norm_num) n (randRot n) (randRot_involutive n) = randGraph n := rfl

/-- **An expander family.** -/
noncomputable def randExpander : ExpanderFamily where
  degree := 120
  degree_pos := by norm_num
  rot := randRot
  rot_involutive := randRot_involutive
  lam := randLam
  lam_nonneg := randLam_nonneg
  lam_lt_one := randLam_lt_one
  spectral := fun n => by
    rw [ofRot_randRot]
    exact spectral_randGraph n

end Complexity
