/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Basic
import Complexitylib.Circuits.BitString
import Complexitylib.Circuits.NF
import Complexitylib.Circuits.AON
import Complexitylib.Circuits.Encoding
import Complexitylib.Circuits.Family
import Complexitylib.Circuits.Encoding.Family
import Complexitylib.Circuits.XOR
import Complexitylib.Circuits.EssentialInput
import Complexitylib.Circuits.Shannon
import Complexitylib.Circuits.LowerBound
import Complexitylib.Circuits.Schnorr
import Complexitylib.Circuits.AC0.Defs
import Complexitylib.Circuits.Nondeterminism
import Complexitylib.Circuits.Valiant

/-! # Circuit Complexity Library

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib.

## The circuit model

A `Circuit B N M G` is an acyclic Boolean circuit over basis `B` with `N`
primary inputs, `M` outputs, and `G` internal gates. The circuit's `size`
is `G + M`: internal and output gates are counted, while primary-input
vertices and per-edge negation flags are not. The `size_complexity` of a
Boolean function is the minimum size of any circuit computing it under this
convention.

## Main results

* **Functional completeness** (`CompleteBasis Basis.unboundedAON`):
  Unbounded fan-in AND/OR (with free negation) can compute every Boolean
  function, via DNF construction.

* **Shannon counting lower bound** (`shannon_lower_bound_circuit`):
  For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot
  be computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)`
  gates.

* **Gate elimination lower bound** (`Circuit.gate_elimination_lower_bound`):
  Any circuit over bounded fan-in `k` AND/OR computing a function with `n'`
  essential inputs has size at least `n' / k`.

* **Schnorr's XOR lower bound** (`schnorr_lower_bound_circuit`):
  Any fan-in-2 AND/OR circuit computing N-input XOR (or its complement)
  requires at least `2(N − 1)` internal gates.

* **CNF/DNF lower bound for XOR** (`DNF.xorBool_complexity_lb`,
  `CNF.xorBool_complexity_lb`): Any DNF (resp. CNF) computing N-input XOR
  requires at least `2^{N-1}` terms (resp. clauses).

* **Nondeterministic quantification** (`existQuantify_complexity_le`):
  If `f` has circuit complexity `s`, then `∃ x ∈ {0,1}^k, f(x,y)` has
  circuit complexity at most `2^k · (s + 1)`.  Combined with the Shannon
  upper bound (`existQuantify_complexity_min`).

## Module structure

Public modules (definitions a reviewer should read):

* `Complexitylib.Circuits.Basic` — `BitString`, `BoolFunFamily`, `Circuit`, `Basis`, `Gate`,
  `CompleteBasis`, `size_complexity`, `wireDepth`, `depth`
* `Complexitylib.Circuits.BitString` — canonical bridges between `BitString n`
  and `List Bool`
* `Complexitylib.Circuits.Family` — circuit families, list semantics, pointwise
  size/depth bounds, and the polynomial-size characterization
* `Complexitylib.Circuits.Encoding` — canonical proof-free encoding, validation,
  and iterative evaluation of fan-in-two AND/OR circuits
* `Complexitylib.Circuits.Encoding.Family` — tagged encoding and evaluation at
  every input length, including the explicit empty-input answer
* `Complexitylib.Circuits.AON.Defs` — `AONOp`, `Basis.unboundedAON`,
  `Basis.boundedAON`, `Basis.andOr2`
* `Complexitylib.Circuits.NF.Defs` — `Literal`, `CNF`, `DNF`, `CNF.complexity`, `DNF.complexity`
* `Complexitylib.Circuits.NF` — CNF/DNF lower bound for XOR (`xorBool_complexity_lb`)
* `Complexitylib.Circuits.XOR` — `Schnorr.xorBool` (N-input parity)
* `Complexitylib.Circuits.EssentialInput` — `IsEssentialInput`, `EssentialInputs`
* `Complexitylib.Circuits.AC0.Defs` — `InAC0`
* `Complexitylib.Circuits.Nondeterminism.Defs` — `existQuantify`, `forallQuantify`

Theorem modules (re-export definitions + main results):

* `Complexitylib.Circuits.AON` — functional completeness of AND/OR
* `Complexitylib.Circuits.Shannon` — Shannon counting lower bound
* `Complexitylib.Circuits.LowerBound` — gate elimination lower bound
* `Complexitylib.Circuits.Schnorr` — Schnorr's XOR lower bound
* `Complexitylib.Circuits.Nondeterminism` — nondeterministic quantification complexity bounds

Internal modules contain proof machinery (CircDesc, DNF construction,
restriction/elimination arguments) and are not intended for direct use.
-/
