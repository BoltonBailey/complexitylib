/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.EventProb

/-!
# Exact dyadic distribution ensembles -- definitions

A `DyadicEnsemble α` represents each parameter slice by a uniformly random
finite Boolean seed and a deterministic sample map. Repeated samples may map to
the same output, so this representation captures arbitrary finite dyadic
distributions without quotienting away sampler multiplicity.

This is the representation-independent finite layer needed by average-case
complexity. Polynomial-time samplability is a separate machine-level property.
-/


@[expose] public section

universe u v

namespace Complexity

/-- A parameterized family of finite dyadic distributions on `α`.

At parameter `n`, a uniformly random Boolean string of length `seedLength n` is
mapped to an output by `sample n`. Distinct seeds may produce the same output. -/
structure DyadicEnsemble (α : Type u) where
  /-- Number of uniformly random bits used by the `n`th slice. -/
  seedLength : ℕ → ℕ
  /-- Deterministic sample produced from the parameter and random seed. -/
  sample : ∀ n, (Fin (seedLength n) → Bool) → α

namespace DyadicEnsemble

variable {α : Type u} {β : Type v}

/-- The seed event whose samples satisfy `P`. -/
def event (D : DyadicEnsemble α) (n : ℕ) (P : α → Prop)
    [DecidablePred P] : Finset (Fin (D.seedLength n) → Bool) :=
  Finset.univ.filter fun seed => P (D.sample n seed)

/-- Exact probability of `P` in the `n`th ensemble slice. -/
def probability (D : DyadicEnsemble α) (n : ℕ) (P : α → Prop)
    [DecidablePred P] : ℚ :=
  eventProb (D.event n P)

/-- Probability mass of one output in the `n`th slice. -/
def mass [DecidableEq α] (D : DyadicEnsemble α) (n : ℕ) (x : α) : ℚ :=
  D.probability n fun y => y = x

/-- Finite support of the `n`th slice. -/
def support [DecidableEq α] (D : DyadicEnsemble α) (n : ℕ) : Finset α :=
  (Finset.univ : Finset (Fin (D.seedLength n) → Bool)).image (D.sample n)

/-- Push an ensemble forward through a deterministic map. -/
def map (D : DyadicEnsemble α) (f : α → β) : DyadicEnsemble β where
  seedLength := D.seedLength
  sample n seed := f (D.sample n seed)

/-- Independently sample two ensembles using disjoint blocks of one seed. -/
def product (D : DyadicEnsemble α) (E : DyadicEnsemble β) :
    DyadicEnsemble (α × β) where
  seedLength n := D.seedLength n + E.seedLength n
  sample n seed :=
    (D.sample n (blockFst (D.seedLength n) (E.seedLength n) seed),
      E.sample n (blockSnd (D.seedLength n) (E.seedLength n) seed))

/-- Point-mass ensemble. Its slices use no random bits. -/
def dirac (x : ℕ → α) : DyadicEnsemble α where
  seedLength _ := 0
  sample n _ := x n

/-- Uniform distribution on all Boolean strings of length `n`, represented as
lists in increasing index order. -/
def uniformBits : DyadicEnsemble (List Bool) where
  seedLength n := n
  sample _ seed := List.ofFn seed

end DyadicEnsemble

end Complexity
