/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.AndOrNot.Defs
import Complexitylib.Circuits.Internal.AndOrNot
import Complexitylib.Circuits.Internal.Simulation

/-! # AND/OR/NOT Basis

This module provides the AND/OR basis definitions and completeness results.

## Definitions (from `Complexitylib.Circuits.AndOrNot.Defs`)

* `AndOrOp` — AND/OR operations
* `Basis.unboundedAndOr` — unbounded fan-in AND/OR basis
* `Basis.boundedAndOr k` — fan-in ≤ `k` AND/OR basis
* `Basis.andOr2` — fan-in exactly 2 AND/OR basis

## Main results

* `CompleteBasis Basis.unboundedAndOr` — proved via DNF construction
* `CompleteBasis Basis.andOr2` — proved via gate-chain simulation
  from `unboundedAndOr`, using `CompleteBasis.of_simulation`
-/
