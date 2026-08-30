/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.EdgeExpansion

/-!
# Disagreement across an expander

The counting fact that makes Dinur's clouds work. A cloud is wired by an
expander and carries equality constraints, so an assignment that is not constant
on the cloud must break many of them. Quantitatively: if `f` labels the vertices
of an expander and `S` is the set of vertices whose label differs from some
fixed value `c`, then at least `(1 - lam) · deg · |S| · |Sᶜ| / n` darts join two
vertices with *different* labels — because every dart from `S` to `Sᶜ` does, and
`EdgeExpansion` counts those.

Taking `c` to be a plurality value of `f` — which by pigeonhole is held by at
least a `1 / |α|` fraction of the vertices — turns this into

`(1 - lam) · deg · |S| / |α| ≤ #disagreeing darts`,

a bound linear in the number of deviant vertices, with a constant depending only
on the expander and the alphabet. That is exactly the exchange rate degree
reduction needs: each vertex that lies about its cloud's value pays for itself
in broken equality constraints.

## Main definitions

- `RegGraph.disagreeDarts` — the darts whose two ends carry different labels

## Main results

- `exists_plurality_value` — pigeonhole: some value is held `n / |α|` often
- `RegGraph.card_disagreeDarts_ge` — disagreement is at least the edge boundary
- `RegGraph.card_disagreeDarts_ge_of_plurality` — the form used by clouds
-/

@[expose] public section

namespace Complexity

/-- **Pigeonhole.** Some value is taken by at least a `1 / |α|` fraction. -/
theorem exists_plurality_value {V α : Type} [Fintype V] [Fintype α] [Nonempty α]
    [DecidableEq α] (f : V → α) :
    ∃ c : α, Fintype.card V
      ≤ Fintype.card α * (Finset.univ.filter fun v => f v = c).card := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun a => (Finset.univ.filter fun v => f v = a).card)
    ⟨Classical.arbitrary α, Finset.mem_univ _⟩
  refine ⟨c, ?_⟩
  have hsum : ∑ a : α, (Finset.univ.filter fun v => f v = a).card = Fintype.card V := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (fun v _ => Finset.mem_univ (f v)),
      Finset.card_univ]
  calc Fintype.card V = ∑ a : α, (Finset.univ.filter fun v => f v = a).card := hsum.symm
    _ ≤ ∑ _a : α, (Finset.univ.filter fun v => f v = c).card :=
        Finset.sum_le_sum fun a _ => hc a (Finset.mem_univ a)
    _ = Fintype.card α * (Finset.univ.filter fun v => f v = c).card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

namespace RegGraph

variable {α : Type} [DecidableEq α] (G : RegGraph)

/-- The darts whose two endpoints carry different labels. -/
def disagreeDarts (f : G.V → α) : Finset (G.V × G.D) :=
  Finset.univ.filter fun p => f p.1 ≠ f (G.nbr p.1 p.2)

/-- **Disagreement is at least the edge boundary.** Every dart leaving the set
of vertices that differ from `c` joins two differently-labelled vertices. -/
theorem card_disagreeDarts_ge {lam : ℝ} (hlam : 0 ≤ lam) (h : G.SpectralBound lam)
    (hn : 0 < G.order) (f : G.V → α) (c : α) :
    (1 - lam) * (G.deg : ℝ)
        * (((Finset.univ.filter fun v => f v ≠ c).card : ℝ)
          * ((Finset.univ.filter fun v => f v ≠ c)ᶜ.card : ℝ) / (G.order : ℝ))
      ≤ ((G.disagreeDarts f).card : ℝ) := by
  classical
  set S : Finset G.V := Finset.univ.filter fun v => f v ≠ c with hS
  have hsub : G.dartsBetween S Sᶜ ⊆ G.disagreeDarts f := by
    intro p hp
    rw [dartsBetween, Finset.mem_filter] at hp
    obtain ⟨-, h1, h2⟩ := hp
    rw [hS, Finset.mem_filter] at h1
    have h2' : f (G.nbr p.1 p.2) = c := by
      by_contra hcon
      refine (Finset.mem_compl.mp h2) ?_
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcon⟩
    rw [disagreeDarts, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [h2']; exact h1.2⟩
  have hcard : ((G.dartsBetween S Sᶜ).card : ℝ) ≤ ((G.disagreeDarts f).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans (G.card_dartsBetween_compl_ge hlam h hn S) hcard

/-- The form the cloud argument uses: with `c` a plurality value, the number of
disagreeing darts is proportional to the number of deviant vertices. -/
theorem card_disagreeDarts_ge_of_plurality [Fintype α] {lam : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (h : G.SpectralBound lam) (hn : 0 < G.order) (f : G.V → α) (c : α)
    (hc : G.order ≤ Fintype.card α * (Finset.univ.filter fun v => f v = c).card) :
    (1 - lam) * (G.deg : ℝ)
        * (((Finset.univ.filter fun v => f v ≠ c).card : ℝ) / (Fintype.card α : ℝ))
      ≤ ((G.disagreeDarts f).card : ℝ) := by
  classical
  set S : Finset G.V := Finset.univ.filter fun v => f v ≠ c with hS
  have hcompl : Sᶜ = Finset.univ.filter fun v => f v = c := by
    rw [hS]
    ext v
    simp
  have hnq : (0 : ℝ) < (G.order : ℝ) := by exact_mod_cast hn
  have hαq : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨c⟩
    exact_mod_cast this
  have hcq : (G.order : ℝ) ≤ (Fintype.card α : ℝ) * (Sᶜ.card : ℝ) := by
    rw [hcompl]
    exact_mod_cast hc
  -- `|Sᶜ| / n ≥ 1 / |α|`
  have hfrac : (S.card : ℝ) / (Fintype.card α : ℝ)
      ≤ (S.card : ℝ) * (Sᶜ.card : ℝ) / (G.order : ℝ) := by
    rw [div_le_div_iff₀ hαq hnq]
    have hS0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    nlinarith [hcq, hS0]
  refine le_trans ?_ (G.card_disagreeDarts_ge hlam h hn f c)
  have hfac : (0 : ℝ) ≤ (1 - lam) * (G.deg : ℝ) := by
    have : (0 : ℝ) ≤ (G.deg : ℝ) := by positivity
    nlinarith [hlam1]
  exact mul_le_mul_of_nonneg_left hfrac hfac

end RegGraph

end Complexity
