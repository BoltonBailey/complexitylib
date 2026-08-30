/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.L
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.BoundedReach
public import Complexitylib.Classes.Containments.Internal.NLSearchAssemble

/-!
# `NL ⊆ P`

⚠️ Unreviewed by Bolton

Nondeterministic logarithmic space is contained in deterministic polynomial time.

On an input of length `n`, a machine using `O(log n)` work space has only polynomially many
configurations: a state, an input head position, and `O(log n)` cells of work tape. The machine
accepts exactly when some accepting configuration is reachable from the initial one in the
configuration graph, and reachability in a polynomially sized graph is decidable in polynomial
time by breadth-first search.

## How it is proved

The graph half comes first. `NL_bounded_reachability` eliminates every trace of nondeterminism
from the membership condition, and `mem_iff_exists_accepting_reachable` states it as bare
reachability: `x` is in the language exactly when some accepting configuration is reachable from
the initial one.

The search half is *programmed*, not assembled. Cobham's theorem (`CobhamFP_eq_FP`) says a
function is polynomial-time exactly when it belongs to the machine-independent algebra, so the
search is built by composing polynomial-time functions:

- `Cobham.cfgCode` packs a configuration into `2(k+2)+1` fixed-width blocks and `Cobham.stepFn`
  is the encoded step of a *deterministic* machine; `NTM.succ_iff` reduces an edge of the
  configuration graph to a step of one of the two `NTM.branchTM`s, so both successors are
  available (`Complexitylib.Classes.Containments.Internal.CodeStep`);
- the visited set is a run of records, one code each, and the search is a worklist: one step
  expands one record, appending each successor that a scan does not already find
  (`Internal.BlockMember`, `Internal.BlockSearch`);
- `Cobham.iterate_mem_FP` is the loop — it turns a polynomial-time step, a ruler and a width
  bound into a polynomial-time iteration, and every loop here is an instance of it;
- the records are distinct codes of reachable configurations, so there are at most as many as
  there are configurations — polynomially many, by `exists_config_bound` — which both bounds the
  state and makes the run saturate (`Internal.BlockSearchCorrect`);
- acceptance is read off a record after driving its output head back to cell `0` with
  `Cobham.rewindFn` (`Internal.CodeRewind`, `Internal.CodeAccept`), and a final scan looks for an
  accepting record (`Internal.BlockAccept`).

`Internal.NLSearchAssemble` runs the search for as many steps as there are configurations and
turns the verdict into `P` membership with `mem_P_of_decisionFn`.

An earlier plan routed the search through `Complexitylib.Models.RandomAccessMachine` instead.
That still needs a compiler from RAM programs back to Turing machines, which the library does
not have; the algebra needs no such bridge.

## Main results

- `NL_subset_P` — the containment
- `coNL_subset_P` — its corollary, since `P` is closed under complement
- `NL_bounded_reachability` — membership as a bounded search in the configuration graph
-/

@[expose] public section

namespace Complexity

/-- **`NL ⊆ P`**: reachability in the polynomially sized configuration graph of a
logspace-bounded machine is decidable in polynomial time. -/
def NLSubsetP : Prop := NL ⊆ P

/-- **A language in `NL` is a polynomially bounded reachability search.** There is a machine
whose configuration graph decides membership: `x` is in the language exactly when an accepting
configuration turns up within `A · (|x| + 1) ^ B` rounds of successor-closure from the initial
configuration. Nondeterminism, choice sequences, time bounds, and asymptotic quantifiers have
all been discharged; only the search remains. -/
theorem NL_bounded_reachability {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (A B : ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
          tm.halted c ∧ c.output.cells 1 = Γ.one :=
  NL_bounded_reachability_internal hL


/-- **`NL ⊆ P`**: the configuration graph of a log-space nondeterministic machine has
polynomially many nodes, and a worklist search walks all of it in polynomial time. The search is
programmed rather than assembled: Cobham's theorem (`CobhamFP_eq_FP`) makes membership in `FP` a
matter of composing polynomial-time functions, `Cobham.stepFn` supplies the encoded machine step,
and `Cobham.iterate_mem_FP` supplies the loops. -/
theorem NL_subset_P : NL ⊆ P :=
  NL_subset_P_internal

/-- **`coNL ⊆ P`**: `P` is closed under complement, so the containment passes to the
complementary class — with no appeal to the Immerman–Szelepcsényi theorem. -/
theorem coNL_subset_P : coNL ⊆ P := by
  intro L hL
  have h : Lᶜ ∈ P := NL_subset_P hL
  have h' : (Lᶜ)ᶜ ∈ P := P_compl h
  rwa [compl_compl] at h'

/-- **`NL ⊆ P`, reduced to the existence of one machine.** For a log-space machine `tm` — the
space witness is part of the hypothesis, since without it the configuration graph is unbounded —
and a polynomial round bound, exhibit a deterministic machine running in explicit polynomial time
that decides whether the bounded breadth-first search turns up an accepting configuration. This
is the reduction the proof above does *not* take: the search is programmed as a polynomial-time
function instead of assembled as a machine. -/
theorem NL_subset_P_of_search
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (A B : ℕ),
      tm.DecidesInSpace L₀ S → S =O (fun n => Nat.log 2 n) →
      ∃ (k' : ℕ) (M : TM k') (q : Polynomial ℕ),
        M.DecidesInTime
          {x : List Bool | ∃ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
            tm.halted c ∧ c.output.cells 1 = Γ.one}
          (fun n => q.eval n)) :
    NL ⊆ P :=
  NL_subset_P_of_search_internal h

end Complexity
