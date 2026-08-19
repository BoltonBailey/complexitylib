/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH
public import Complexitylib.Classes.Randomized

/-!
# The Sipser–Lautemann theorem

The Sipser–Lautemann theorem (Arora–Barak Theorem 7.15) places bounded-error
probabilistic polynomial time inside the second level of the polynomial
hierarchy: `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`. This file states that containment against the
library's concrete `BPP` (`Complexitylib.Classes.Randomized`) and the
certificate-quantifier levels `SigmaP` / `PiP`
(`Complexitylib.Classes.PH`), and proves the set-theoretic consequences that
follow from it without any machine engineering.

The containment itself is not proved here. Following the interface-isolation
pattern used elsewhere in the library, the statement is packaged as the
`Prop`-valued definition `SipserLautemann`, so that downstream results can be
stated and proved against it now and discharged once the probabilistic
argument lands. Every theorem in this file is unconditional: each takes the
statement (or its `Σ₂` half) as an explicit hypothesis rather than assuming it
globally.

## Main definitions

- `SipserLautemann` — the statement `BPP ⊆ SigmaP 2 ∩ PiP 2`

## Main results

- `sipserLautemann_iff` — the statement splits into its `Σ₂` and `Π₂` halves
- `sipserLautemann_of_subset_SigmaP` — the `Σ₂` half suffices, given that
  `BPP` is closed under complement (`BPP` is a two-sided-error class, so the
  `Π₂` half is the `Σ₂` half applied to complements)
- `BPP_subset_SigmaP_two_of_sipserLautemann`,
  `BPP_subset_PiP_two_of_sipserLautemann` — the two halves
- `BPP_subset_PH_of_sipserLautemann` — `BPP ⊆ PH`

## TODO

- Prove `BPP` is closed under complement (swap the accept/reject outputs of a
  `BPTIME` machine), reducing `SipserLautemann` to its `Σ₂` half via
  `sipserLautemann_of_subset_SigmaP`.
- Prove that half. The standard route: amplify a `BPP` machine so that the
  bad-seed set has density below `2^(-m)` for `m` the number of random bits
  used (the amplification machinery of
  `Complexitylib.Classes.Randomized.GoodSeed` and
  `Complexitylib.Classes.Randomized.CircuitAmplification` is the starting
  point), then express membership by Lautemann's shift trick: `x ∈ L` iff
  there exist `m` shift vectors `u₁, …, u_m` whose translates of the accepting
  seed set cover `{0,1}^m`, a `∃∀` predicate with a polynomial-time matrix.
-/

@[expose] public section

namespace Complexity

/-- **Sipser–Lautemann**: bounded-error probabilistic polynomial time lies in
the second level of the polynomial hierarchy, `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`.

Stated as a `Prop` rather than proved: the probabilistic argument behind it is
still to be formalized (see the module docstring). Results depending on it take
it as an explicit hypothesis. -/
def SipserLautemann : Prop :=
  BPP ⊆ SigmaP 2 ∩ PiP 2

/-- The statement splits into its two halves: containment in `Σ₂ᵖ` and
containment in `Π₂ᵖ`. -/
theorem sipserLautemann_iff : SipserLautemann ↔ BPP ⊆ SigmaP 2 ∧ BPP ⊆ PiP 2 :=
  Set.subset_inter_iff

/-- The `Σ₂ᵖ` half of the statement. -/
theorem BPP_subset_SigmaP_two_of_sipserLautemann (h : SipserLautemann) :
    BPP ⊆ SigmaP 2 :=
  fun _ hL => (h hL).1

/-- The `Π₂ᵖ` half of the statement. -/
theorem BPP_subset_PiP_two_of_sipserLautemann (h : SipserLautemann) :
    BPP ⊆ PiP 2 :=
  fun _ hL => (h hL).2

/-- The `Σ₂ᵖ` half implies the full statement, given that `BPP` is closed under
complement: a language of `BPP` lies in `Π₂ᵖ` exactly when its complement lies
in `Σ₂ᵖ`, and the complement is again a `BPP` language. -/
theorem sipserLautemann_of_subset_SigmaP (hcompl : ∀ L ∈ BPP, Lᶜ ∈ BPP)
    (h : BPP ⊆ SigmaP 2) : SipserLautemann :=
  fun L hL => ⟨h hL, h (hcompl L hL)⟩

/-- Sipser–Lautemann puts `BPP` inside the polynomial hierarchy. -/
theorem BPP_subset_PH_of_sipserLautemann (h : SipserLautemann) : BPP ⊆ PH :=
  fun _ hL => SigmaP_subset_PH 2 (h hL).1

end Complexity
