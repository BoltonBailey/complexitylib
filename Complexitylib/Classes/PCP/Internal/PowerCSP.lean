/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Power
public import Complexitylib.Classes.PCP.Internal.RegCSP
public import Complexitylib.Classes.PCP.Internal.WalkDart

/-!
# Powering a constraint system

Dinur's gap amplification step. The `t`-th power of a constraint system `R` has
the same vertices; its constraints are indexed by the **walks of length `t`** in
`R`'s graph, and its alphabet consists of *opinions*.

## Opinions

A label of the powered system at `v` is a function
`(Fin h → G.D) → α`: for every length-`h` walk out of `v`, a claim about the
label of that walk's endpoint. Since `G` has self-loops, `Loops.padWalk` names
every vertex within distance `h` of `v` by such a walk, so a label is exactly an
opinion about the ball of radius `h` around `v` — while remaining a *constant*
sized alphabet, `|α| ^ (deg ^ h)`, independent of the number of vertices. That
is what makes the alphabet-reduction step afterwards possible.

## The powered constraint

The constraint on the walk `(v, s)` compares the opinions held at its two ends.
For each step `k` of the walk that lies in the **middle window** — close enough
to the start (`k ≤ h`) that the start has an opinion about `v k`, and close
enough to the end (`t - (k+1) ≤ h`) that the end has an opinion about `v (k+1)`
— it demands that those two opinions satisfy `R`'s own constraint on the `k`-th
dart. The end's opinion is addressed through the *reversed* walk, which is why
`Power`'s reversal machinery is needed here.

Steps outside the middle window are not checked: neither endpoint is required to
have an opinion about them.

## What is proved here

Perfect completeness: a satisfying assignment `σ` of `R` induces the *truthful*
opinion assignment `v ↦ (w ↦ σ (walkEnd h v w))`, which satisfies every walk
constraint, because on the middle window the two opinions are literally `σ`'s
values at the two ends of a dart of `R`.

The converse — that the value *doubles*, the analytic heart of Dinur's proof —
is the soundness direction and is not proved here.

## ⚠️ Soundness needs a different walk law

Soundness decodes `A` by plurality (`Plurality`) and needs, for each checked
step `k`, that the two opinions the constraint reads are truthful with
probability at least `1 / |α|` each. That fails for the construction above, and
not for want of effort:

* the plurality at `x` is taken over **all** `deg ^ h` walk indices out of `x`,
  whereas the index the constraint reads at step `k` is
  `revWalk (padWalk … k h)`, whose last `h - k` labels are the *fixed* loop
  label. Those indices form a sub-cube of relative size `deg ^ (k - h)`, so a
  popular-overall opinion may be wrong on every index the constraint ever
  reads.

Defining the plurality over the mixture of padded distributions instead fixes
each step in isolation but not the first moment, which needs
`∑_{k ∈ W} a_k · b_{t-1-k} > 0` for the prefix- and suffix-truthfulness
profiles `a, b`. Fixed-length walks force `i + j = t - 1` on the prefix and
suffix lengths, so `a` and `b` can be supported on mirror-disjoint halves of the
window and the sum vanishes; an adversarial `A` whose opinions depend only on
the walk length realises this.

The construction that works is Dinur's: stop the walk with probability `1/q` at
each step. Memorylessness makes the prefix and suffix lengths **independent**,
so the double sum factorises into a product of two mixture bounds and each
factor is at least `1 / |α|`. Concretely: label darts by
`Fin T → G.D × Fin q`, let the effective length be the first index whose second
component is `0`, reverse only that prefix (keeping the tail, which preserves
involutivity), and index opinions by *variable-length* walks so that no padding
is needed. Every step of the effective walk is then checkable, and no window is
required.

What the present construction does support is the single matching position:
with `t = 2 * h + 1` and `k = h`, the prefix and suffix are unpadded walks of
length exactly `h`, so both distributions are uniform and independent, giving
soundness with no amplification. That is a fine sanity check, but it is not
enough for the PCP theorem, which needs the gain to grow with `t`.

## Main definitions

- `Opinion` — the alphabet of the powered system
- `RegCSP.power` — the powered constraint system
- `RegCSP.truthful` — the opinion assignment induced by an assignment of `R`

## Main results

- `RegCSP.graph_power`, `RegCSP.rel_power_iff`
- `RegCSP.satisfies_power_truthful` — the truthful assignment satisfies every
  walk constraint
- `RegCSP.satisfiable_power_of_satisfiable` — perfect completeness
- `RegCSP.not_satisfies_power_of_faulty` — a faulty dart in the middle window
  with truthful opinions at both ends breaks the walk's constraint
- `RegCSP.card_dart_power`, `RegCSP.unsatFrac_power` — the powered value is a
  fraction of walks
- `RegCSP.card_walks_faulty` — the first moment: `deg ^ (t-1)` walks per faulty
  dart per step index
-/

@[expose] public section

namespace Complexity

/-- A label of the powered system: for each length-`h` walk out of the vertex, a
claim about the label of that walk's endpoint. -/
abbrev Opinion (G : RegGraph) (h : ℕ) (α : Type) : Type := (Fin h → G.D) → α

namespace RegCSP

variable {α : Type} (R : RegCSP α) (L : R.graph.Loops) (t h : ℕ)

/-- The `t`-th power of `R`, with opinions of radius `h` as its alphabet: one
constraint per length-`t` walk, checking `R`'s constraints on the steps of the
walk that both endpoints have an opinion about. -/
def power (R : RegCSP α) (L : R.graph.Loops) (t h : ℕ) :
    RegCSP (Opinion R.graph h α) where
  graph := R.graph.power t
  rel v s a b := decide (∀ k : Fin t, k.val ≤ h → t - (k.val + 1) ≤ h →
    R.rel (R.graph.walkAt t v s k.val) (s k)
        (a (L.padWalk v s k.val h))
        (b (L.padWalk (R.graph.walkEnd t v s) (R.graph.revWalk v s)
          (t - (k.val + 1)) h)) = true)

@[simp] theorem graph_power : (R.power L t h).graph = R.graph.power t := rfl

theorem rel_power_iff (v : R.graph.V) (s : Fin t → R.graph.D)
    (a b : Opinion R.graph h α) :
    (R.power L t h).rel v s a b = true ↔
      ∀ k : Fin t, k.val ≤ h → t - (k.val + 1) ≤ h →
        R.rel (R.graph.walkAt t v s k.val) (s k)
            (a (L.padWalk v s k.val h))
            (b (L.padWalk (R.graph.walkEnd t v s) (R.graph.revWalk v s)
              (t - (k.val + 1)) h)) = true := by
  simp [power]

/-- The truthful opinion assignment induced by an assignment of `R`: every
vertex reports the true labels of the endpoints of the walks out of it. -/
def truthful (σ : R.Assignment) : (R.power L t h).Assignment :=
  fun v w => σ (R.graph.walkEnd h v w)

/-- On the middle window the truthful opinions are exactly `σ`'s values at the
two ends of the corresponding dart of `R`, so a satisfying `σ` satisfies every
walk constraint. -/
theorem satisfies_power_truthful {σ : R.Assignment} (hσ : ∀ p, R.Satisfies σ p)
    (p : (R.power L t h).Dart) : (R.power L t h).Satisfies (R.truthful L t h σ) p := by
  obtain ⟨v, s⟩ := p
  have hnbr : (R.power L t h).graph.nbr v s = R.graph.walkEnd t v s := R.graph.nbr_power t v s
  rw [Satisfies, satisfies]
  dsimp only
  rw [hnbr, rel_power_iff]
  intro k hk1 hk2
  have hkt : k.val < t := k.isLt
  -- the start's opinion about the `k`-th vertex
  have hstart : R.truthful L t h σ v (L.padWalk v s k.val h)
      = σ (R.graph.walkAt t v s k.val) := by
    rw [truthful, L.walkEnd_padWalk v s hk1 (le_of_lt hkt)]
  -- the end's opinion about the `(k+1)`-st vertex, addressed along the reversal
  have harith : t - (t - (k.val + 1)) = k.val + 1 := by omega
  have hend : R.truthful L t h σ (R.graph.walkEnd t v s)
        (L.padWalk (R.graph.walkEnd t v s) (R.graph.revWalk v s) (t - (k.val + 1)) h)
      = σ (R.graph.walkAt t v s (k.val + 1)) := by
    rw [truthful, L.walkEnd_padWalk (R.graph.walkEnd t v s) (R.graph.revWalk v s) hk2 (by omega),
      R.graph.walkAt_revWalk v s (t - (k.val + 1)) (by omega), harith]
  rw [hstart, hend]
  have hdart := hσ (R.graph.walkAt t v s k.val, s k)
  rw [Satisfies, satisfies] at hdart
  rwa [R.graph.walkAt_succ_of_lt v s hkt]

/-- **Perfect completeness of powering.** -/
theorem satisfiable_power_of_satisfiable (hR : R.Satisfiable) :
    (R.power L t h).Satisfiable := by
  obtain ⟨σ, hσ⟩ := hR
  exact ⟨R.truthful L t h σ, fun p => R.satisfies_power_truthful L t h hσ p⟩

/-- **The soundness-side counterpart.** If some step of the walk lies in the
middle window, carries a dart that `σ` fails, and both endpoints happen to
report `σ`'s values for that dart's two vertices, then the walk's constraint
fails.

This is the bridge from counting *faulty darts along walks* to the value of the
powered system: it is what makes a walk that meets a faulty dart an unsatisfied
constraint, provided the two opinions involved are truthful. Bounding how often
they are not is the remaining analytic work. -/
theorem not_satisfies_power_of_faulty {σ : R.Assignment}
    (A : (R.power L t h).Assignment) (v : R.graph.V) (s : Fin t → R.graph.D)
    (k : Fin t) (hk1 : k.val ≤ h) (hk2 : t - (k.val + 1) ≤ h)
    (hfault : ¬ R.Satisfies σ (R.graph.walkAt t v s k.val, s k))
    (htruth₁ : A v (L.padWalk v s k.val h) = σ (R.graph.walkAt t v s k.val))
    (htruth₂ : A (R.graph.walkEnd t v s)
        (L.padWalk (R.graph.walkEnd t v s) (R.graph.revWalk v s) (t - (k.val + 1)) h)
      = σ (R.graph.walkAt t v s (k.val + 1))) :
    ¬ (R.power L t h).Satisfies A (v, s) := by
  intro hsat
  have hnbr : (R.power L t h).graph.nbr v s = R.graph.walkEnd t v s := R.graph.nbr_power t v s
  rw [Satisfies, satisfies] at hsat
  dsimp only at hsat
  rw [hnbr, rel_power_iff] at hsat
  have hk := hsat k hk1 hk2
  rw [htruth₁, htruth₂] at hk
  rw [Satisfies, satisfies] at hfault
  dsimp only at hfault
  rw [← R.graph.walkAt_succ_of_lt v s k.isLt] at hfault
  exact hfault hk

/-! ### Counting -/

/-- The powered system has one constraint per walk. -/
theorem card_dart_power :
    Fintype.card (R.power L t h).Dart = R.graph.order * R.graph.deg ^ t := by
  rw [card_dart]
  simp [graph_power]

/-- The value of an assignment of the powered system is the fraction of *walks*
whose constraint it fails. -/
theorem unsatFrac_power (A : (R.power L t h).Assignment) :
    (R.power L t h).unsatFrac A
      = (((R.power L t h).unsatDarts A).card : ℚ)
        / ((R.graph.order * R.graph.deg ^ t : ℕ) : ℚ) := by
  rw [unsatFrac]
  congr 2
  simp [graph_power]

/-- **The first moment.** For each step index `k`, the walks whose `k`-th dart
is one that `σ` fails number exactly `deg ^ (t-1)` times the faulty darts — one
`deg ^ (t-1)`-sized fibre per faulty dart, by `sum_stepDart`. This is what makes
the expected number of faulty steps along a walk proportional to `unsatFrac σ`. -/
theorem card_walks_faulty (σ : R.Assignment) {k : ℕ} (hk : k < t) :
    (∑ v : R.graph.V, (Finset.univ.filter fun s : Fin t → R.graph.D =>
        (R.graph.walkAt t v s k, s ⟨k, hk⟩) ∈ R.unsatDarts σ).card)
      = R.graph.deg ^ (t - 1) * (R.unsatDarts σ).card :=
  R.graph.card_walks_stepDart_mem hk (R.unsatDarts σ)

end RegCSP

end Complexity
