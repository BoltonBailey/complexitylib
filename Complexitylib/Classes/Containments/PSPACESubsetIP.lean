/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.IPSubsetPSPACE
public import Complexitylib.Classes.Containments.Internal.TQBFFlatHard
public import Complexitylib.Classes.Interactive.Internal.ShenIP
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
- **The reduction is now proved, as mathematics.**
  `Complexitylib.Classes.Containments.Internal.TQBFConfig` reads the one-hot configuration layout
  of `Complexitylib.Circuits.Unrolling` as a block of a quantified formula and packages a
  machine's configuration space as a `SavitchData` (`cfgSavitchData`); `blockInj` says a block
  determines a windowed, space-bounded configuration. `Internal.TQBFReach` identifies block
  reachability with `NTM.ReachesCfgLe` (`reachPow_iff`), and `Internal.TQBFHard` concludes
  `Complexity.exists_savitch_instance`: **every `PSPACE` language has, for each input, a
  `WellFormed` prenex-CNF quantified Boolean formula that is true exactly when the input is in
  the language.**
- **The emitter — done.** `Internal.TQBFFlat` rebuilds the matrix as a fixed number of *indexed
  clause families* over a `FlatLayout` — one-hot clauses in at-least-one/at-most-one form,
  Cook–Levin style transition clauses indexed by transition case and atom, and level-indexed
  Tseitin auxiliaries for the recursion's chain — and `Internal.TQBFFlatHard` proves
  `Complexity.exists_flat_instance`, the same reduction in that shape. The families are then
  written down in Cobham's algebra by `Internal.TQBFEmitArith`, `TQBFEmitValid`,
  `TQBFEmitPrefix`, `TQBFEmitWire` and `TQBFEmitMatrix` (`Complexity.flatInstance_mem_FP`):
  every wire index is an arithmetic function of the clause index, so each family is a single
  `Complexity.emitListAt`.
-/

@[expose] public section

namespace Complexity

/-- **`PSPACE ⊆ IP`** (Shamir): every `PSPACE` language reduces in polynomial time to a
well-formed prenex-CNF quantified Boolean formula, and every such language is in `IP` by the
sum-check protocol. -/
theorem PSPACE_subset_IP : PSPACE ⊆ IP := fun L hL => by
  obtain ⟨inst, hwf, hfp, heq⟩ := exists_flat_instance hL
  exact mem_IP_of_shen_reduction L _ hfp inst (fun _ => rfl) hwf heq

/-- **`IP = PSPACE`** (Shamir's theorem): the two containments together. -/
theorem IP_eq_PSPACE : IP = PSPACE :=
  subset_antisymm IP_subset_PSPACE PSPACE_subset_IP

end Complexity
