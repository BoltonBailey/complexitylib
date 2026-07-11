/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.EssentialInput
import Complexitylib.Circuits.Internal.LowerBound

/-! # Gate Elimination Lower Bound

For any circuit over a bounded fan-in `k` AND/OR basis (`Basis.boundedAndOr k`),
the number of essential input variables is at most `k` times the circuit size.

The key insight: if no gate directly reads a primary input wire, then that
input cannot influence the circuit's output. By contrapositive, every
essential variable must be "covered" by at least one gate. Since each gate
reads at most `k` inputs, the circuit needs at least `⌈n'/k⌉` gates.

## Definitions (from `Complexitylib.Circuits.EssentialInput`)

* `IsEssentialInput f i` — function `f` depends on input variable `i`
  (flipping bit `i` can change some output)
* `essentialInputs f` — the `Finset` of all essential input variables

## Main results

The main theorem is `Circuit.card_essentialInputs_le_mul_size`:

    theorem Circuit.card_essentialInputs_le_mul_size {k : Nat}
        (c : Circuit (Basis.boundedAndOr k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f) :
        (essentialInputs f).card ≤ k * c.size

And its corollary for functions that depend on all inputs:

    theorem Circuit.le_mul_size_of_forall_isEssentialInput {k : Nat}
        (c : Circuit (Basis.boundedAndOr k) N M G)
        (f : BitString N → BitString M)
        (hf : c.eval = f)
        (hall : ∀ i : Fin N, IsEssentialInput f i) :
        N ≤ k * c.size
-/
