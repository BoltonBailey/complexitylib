/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.PowerCSP
public import Mathlib.Data.Finset.Max

/-!
# The plurality assignment

Soundness of Dinur's powering step is proved by *decoding*: an arbitrary
assignment of the powered system, whose labels are opinions that need not be
consistent with each other, is turned into a single assignment of the original
system, and the walks whose constraints fail are counted against it.

The decoding is by plurality. The endpoint `u` of a length-`h` walk `w` out of
`v` holds an opinion about `v` — read off at the index `revWalk v w`, the
reversal of `w`, which is the walk from `u` back to `v`. Letting `w` range over
all `deg ^ h` walks out of `v` gives a multiset of opinions about `v`, and
`plurality` picks a most frequent one.

Two consequences are recorded: the plurality value is at least as popular as any
other value, and it is held by at least a `1 / |α|` fraction of the walks. The
second is the pigeonhole that keeps the decoded assignment from being vacuous.

## Main definitions

- `RegCSP.opinionAbout` — what the far end of a walk says about its start
- `RegCSP.opinionCount` — how many walks out of `v` ascribe a given value to it
- `RegCSP.plurality` — the decoded assignment

## Main results

- `RegCSP.opinionAbout_walkEnd_revWalk`, `RegCSP.opinionAbout_padWalk` — the
  opinions the powered constraint reads are entries of the plurality's multiset
- `RegCSP.opinionCount_le_plurality` — no value beats the plurality
- `RegCSP.card_le_card_mul_opinionCount_plurality` — the plurality is held by at
  least a `1 / |α|` fraction of walks
-/

@[expose] public section

namespace Complexity

namespace RegCSP

variable {α : Type} (R : RegCSP α) (L : R.graph.Loops) (t h : ℕ)

/-- The value that the far end of the length-`h` walk `w` out of `v` ascribes to
`v`, read at the index `revWalk v w` — the walk back from that end to `v`. -/
def opinionAbout (A : (R.power L t h).Assignment) (v : R.graph.V)
    (w : Fin h → R.graph.D) : α :=
  A (R.graph.walkEnd h v w) (R.graph.revWalk v w)

/-- **Reversal duality.** The value `v` reads at the walk `w` *is* the opinion
that `w`'s far end holds about `v`. Both reversal lemmas of `Power` are used:
reversing `w` lands back at `v`, and reversing it twice returns `w`. -/
theorem opinionAbout_walkEnd_revWalk (A : (R.power L t h).Assignment) (v : R.graph.V)
    (w : Fin h → R.graph.D) :
    R.opinionAbout L t h A (R.graph.walkEnd h v w) (R.graph.revWalk v w) = A v w := by
  rw [opinionAbout, R.graph.walkEnd_revWalk v w, R.graph.revWalk_revWalk v w]

/-- **The bridge to decoding.** The opinion that the *start* of a walk holds
about its `k`-th vertex — exactly what the powered constraint reads — is one of
the opinions about that vertex whose mode is `plurality`. So bounding how often
the powered constraint reads an untruthful opinion is a statement about the
plurality's own multiset. -/
theorem opinionAbout_padWalk (A : (R.power L t h).Assignment) (v : R.graph.V)
    (s : Fin t → R.graph.D) {k : ℕ} (hkh : k ≤ h) (hkt : k ≤ t) :
    R.opinionAbout L t h A (R.graph.walkAt t v s k)
        (R.graph.revWalk v (L.padWalk v s k h))
      = A v (L.padWalk v s k h) := by
  rw [← L.walkEnd_padWalk v s hkh hkt, R.opinionAbout_walkEnd_revWalk]

section Decode

variable [DecidableEq α] [Fintype α] [Nonempty α]

/-- The number of length-`h` walks out of `v` whose far end ascribes the value
`a` to `v`. -/
def opinionCount (A : (R.power L t h).Assignment) (v : R.graph.V) (a : α) : ℕ :=
  (Finset.univ.filter fun w : Fin h → R.graph.D => R.opinionAbout L t h A v w = a).card

/-- The plurality decoding: each vertex is given a value that the ends of the
walks out of it ascribe to it most often. -/
noncomputable def plurality (A : (R.power L t h).Assignment) (v : R.graph.V) : α :=
  (Finset.exists_max_image (Finset.univ : Finset α) (R.opinionCount L t h A v)
    ⟨Classical.arbitrary α, Finset.mem_univ _⟩).choose

/-- No value is ascribed to `v` more often than its plurality value. -/
theorem opinionCount_le_plurality (A : (R.power L t h).Assignment) (v : R.graph.V) (a : α) :
    R.opinionCount L t h A v a ≤ R.opinionCount L t h A v (R.plurality L t h A v) :=
  (Finset.exists_max_image (Finset.univ : Finset α) (R.opinionCount L t h A v)
    ⟨Classical.arbitrary α, Finset.mem_univ _⟩).choose_spec.2 a (Finset.mem_univ a)

omit [Nonempty α] in
/-- The counts over all values partition the walks. -/
theorem sum_opinionCount (A : (R.power L t h).Assignment) (v : R.graph.V) :
    ∑ a : α, R.opinionCount L t h A v a = R.graph.deg ^ h := by
  classical
  have hcard : Fintype.card (Fin h → R.graph.D) = R.graph.deg ^ h := R.graph.card_walks h
  calc ∑ a : α, R.opinionCount L t h A v a
      = ∑ a : α, (Finset.univ.filter fun w : Fin h → R.graph.D =>
          R.opinionAbout L t h A v w = a).card := rfl
    _ = (Finset.univ : Finset (Fin h → R.graph.D)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise]
        intro w _
        exact Finset.mem_univ _
    _ = R.graph.deg ^ h := by rw [Finset.card_univ, hcard]

/-- **Pigeonhole.** The plurality value is ascribed to `v` by at least a
`1 / |α|` fraction of the walks out of `v`. -/
theorem card_le_card_mul_opinionCount_plurality (A : (R.power L t h).Assignment)
    (v : R.graph.V) :
    R.graph.deg ^ h
      ≤ Fintype.card α * R.opinionCount L t h A v (R.plurality L t h A v) := by
  calc R.graph.deg ^ h = ∑ a : α, R.opinionCount L t h A v a := (R.sum_opinionCount L t h A v).symm
    _ ≤ ∑ _a : α, R.opinionCount L t h A v (R.plurality L t h A v) :=
        Finset.sum_le_sum fun a _ => R.opinionCount_le_plurality L t h A v a
    _ = Fintype.card α * R.opinionCount L t h A v (R.plurality L t h A v) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Decode

end RegCSP

end Complexity
