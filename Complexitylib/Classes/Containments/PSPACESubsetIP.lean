/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.IPSubsetPSPACE
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.P.Defs

/-!
# `PSPACE ⊆ IP`

⚠️ Unreviewed by Bolton

Shamir's theorem, the hard half of `IP = PSPACE`.

Take a `PSPACE`-complete problem — validity of a quantified Boolean formula — and arithmetize
it:
replace the Boolean connectives by polynomial operations over a finite field, so that the formula's
truth value becomes the value of an iterated sum and product. The prover then convinces the
verifier of that value by the sum-check protocol, one variable at a time, with a degree-reduction
step interleaved to keep the intermediate polynomials small.

## What the proof needs

- **The interactive protocol — done.** `Complexitylib.SAT.QBF.Arith`,
  `Complexitylib.Classes.Interactive.SumCheck`, `OperatorChain` and `TQBFProtocol` are the
  abstract protocol with completeness and the `Σ d / |F|` soundness bound;
  `Complexitylib.Classes.Interactive.Internal.Shen*` build Shen's verifier in Cobham's algebra
  (field elements as fixed-width strings, a prime found by trial division, the operator chain as
  data) and prove `Complexity.mem_IP_of_shen_reduction` (`Internal.ShenIP`): **any language that
  reduces in polynomial time to well-formed prenex-CNF quantified formulas is in `IP`.**
  So all that is left is the hardness reduction.
- **The reduction — Savitch's recursion as a formula, done abstractly.**
  `Complexitylib.Classes.Containments.Internal.TQBFSavitchRec` takes a `SavitchData`: an abstract
  configuration space of `W`-bit blocks with formulas for validity, one step (with scratch bits)
  and acceptance, and builds the prenex formula
  `∃A ∃B ∃M_k ∀U_k ∀V_k … ∃scratch ∃aux. CNF` whose matrix is the Tseitin encoding
  (`Internal.TQBFTseitin`) of Savitch's recursion. `SavitchData.savitch_spec` proves the instance
  is `WellFormed` — its prefix names the variables `0, …, n - 1` in order — and that it is true
  exactly when a valid accepting block is reachable from the start in `2 ^ k` steps.
- **What is missing.** Two things, both about a concrete machine:
  1. *An instance of `SavitchData` for a polynomial-space machine.* The block layout of
     `Complexitylib.Circuits.Unrolling` fits: `configWire tm T base atom` is contiguous of width
     `configWidth tm T`, and `nextFormula`/`nextFormula_eval` give one step as a `BoolFormula`
     (`QBF.ofBoolFormula` carries it over). What has to be written is `validF` — the one-hot
     constraints, with the decoding lemma that a one-hot block *is* a configuration — and the
     acceptance formula, which is two literals.
  2. *A polynomial-time emitter.* `mem_IP_of_shen_reduction` needs the instance's encoding as a
     function in `FP`. This is the analogue of Cook–Levin's `reductionFn_mem_FP` for the Savitch
     formula, and is the larger of the two.

## TODO

- Instantiate `SavitchData` for a polynomial-space machine and emit the instance in `FP`; the
  protocol side is finished. This is the deepest single theorem on the roadmap's long-term
  track.
-/

@[expose] public section

namespace Complexity

/-- **`PSPACE ⊆ IP`** (Shamir): arithmetize a quantified Boolean formula and run sum-check. -/
def PSPACESubsetIP : Prop := PSPACE ⊆ IP

/-- The two halves together are Shamir's theorem; the first is `IP_subset_PSPACE`. -/
theorem IP_eq_PSPACE_of (h' : PSPACESubsetIP) : IP = PSPACE :=
  subset_antisymm IP_subset_PSPACE (h' : PSPACE ⊆ IP)

end Complexity
