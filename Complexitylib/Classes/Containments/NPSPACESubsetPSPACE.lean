/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.SavitchBound
public import Complexitylib.Classes.Containments.Internal.SpaceIterate
public import Complexitylib.Classes.Containments.Internal.SavitchStep
public import Complexitylib.Classes.NP

/-!
# `NPSPACE ⊆ PSPACE`

⚠️ Unreviewed by Bolton

Savitch's theorem: nondeterminism costs only a squaring of space.

The reachability predicate `Reach(u, v, 2^i)` — is `v` reachable from `u` in at most `2^i` steps —
satisfies `Reach(u, v, 2^i) ↔ ∃ m, Reach(u, m, 2^(i-1)) ∧ Reach(m, v, 2^(i-1))`. Recursing on `i`
and reusing the same space for the two subcalls costs `O(S)` bits per level and `O(log 2^S) = O(S)`
levels, so a machine using space `S` is simulated deterministically in space `O(S²)` — polynomial
space is closed under this squaring.

## Progress

The combinatorial core is done. `savitch_halving` below is the midpoint identity the recursion
turns on, in the form the machine uses it: a step bound of `2 ^ (i + 1)` splits into two
independent subproblems with bound `2 ^ i`, so the recursion has depth `i` and each level stores
exactly one midpoint configuration. `savitch_reaches_within_codes` supplies the base fact that
makes the depth finite: a walk longer than the number of configuration codes repeats a
configuration, so reachability is always witnessed within that many steps.

`NPSPACE_bounded_reachability` puts the two together: membership in a language of `NPSPACE` is
reachability within `2 ^ q(|x|)` steps for an explicit polynomial `q`. Halving that bound
`q(|x|)` times reaches a single step, so the recursion depth is polynomial — and each level
stores one configuration, which a polynomially space-bounded machine can afford.

## What the proof still needs

A space-accounted implementation of the recursion. The route, following `NL ⊆ P`, is to write
the recursion as a *pure function* and let a general tool supply the machine:

- Savitch's procedure is a stack machine. Its stack holds one frame per level — a level counter,
  the two endpoints and the midpoint being tried — so it is polynomially bounded, and one step of
  it (push, pop, or advance the midpoint) is a polynomial-time function of the stack, computable
  with the block toolkit of `Complexitylib.Classes.Containments.Internal.BlockMember` and the
  encoded machine step `Complexity.nstepFn` that `NL ⊆ P` already uses.
- What is missing is the tool that turns such a function into a `PSPACE` machine: *iterating a
  polynomial-time function on a polynomially bounded state is in `PSPACE`*, however many
  iterations it takes. `Complexitylib.Classes.Containments.Internal.SpaceIterate` is building it.
  The iteration machinery is already there — `Cobham.iterSetup` and `Cobham.iterBody` from the
  completeness half of Cobham's theorem apply the function once and restore the entry shape — and
  only the loop driver has to change: `TM.forRegTM` counts in unary, which cannot reach
  `2 ^ poly`, so the loop runs against a binary counter, exactly as in `PP ⊆ PSPACE` and
  `PH ⊆ PSPACE`. Its window comes from `TM.loopTM_keepsWindowOn_phases`, with each iteration's
  window read off that iteration's (polynomial) running time.

This tool is what `IP ⊆ PSPACE` will need too: a game-tree value is another
polynomially-bounded stack recursion.

## Main results

- `savitch_halving` — the midpoint recursion at a halved step bound
- `savitch_reaches_within_codes` — reachability is witnessed within the number of codes
- `NPSPACE_bounded_reachability` — membership is reachability within `2 ^ poly` steps
- `NPSPACE_subset_PSPACE_of_recursion` — the containment, granted one machine

## TODO

- Finish `Internal.SpaceIterate`, program Savitch's stack step as a polynomial-time function,
  and combine with `PSPACE_subset_NPSPACE` for `PSPACE = NPSPACE`.
-/

@[expose] public section

namespace Complexity

/-- **`NPSPACE ⊆ PSPACE`** (Savitch): halving the path length recursively simulates a
nondeterministic space-`S` machine deterministically in space `O(S²)`. -/
def NPSPACESubsetPSPACE : Prop := NPSPACE ⊆ PSPACE

/-- **The recursion Savitch's machine runs.** A step bound of `2 ^ (i + 1)` is met exactly when
some midpoint configuration is reachable within `2 ^ i` steps and reaches the target within
`2 ^ i` steps. Recursing on `i` costs one stored midpoint per level and bottoms out at `i = 0`,
where the question is a single step of the configuration graph. -/
theorem savitch_halving {k : ℕ} (tm : NTM k) (i : ℕ) (c c' : Cfg k tm.Q) :
    tm.ReachesCfgLe (2 ^ (i + 1)) c c' ↔
      ∃ mid, tm.ReachesCfgLe (2 ^ i) c mid ∧ tm.ReachesCfgLe (2 ^ i) mid c' :=
  NTM.reachesCfgLe_two_pow_succ_iff tm i c c'

/-- **Reachability is witnessed within the number of configuration codes.** Any coding map that
separates the reachable configurations bounds the length of a walk that has to be searched: a
longer walk repeats a configuration and the repetition can be cut out. This is what makes the
recursion depth of `savitch_halving` finite. -/
theorem savitch_reaches_within_codes {k : ℕ} {α : Type} [Fintype α] (tm : NTM k)
    (c₀ : Cfg k tm.Q) (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    {N : ℕ} (hN : Fintype.card α ≤ N) (c : Cfg k tm.Q) :
    tm.ReachesCfg c₀ c ↔ tm.ReachesCfgLe N c₀ c :=
  NTM.reachesCfg_iff_reachesCfgLe tm c₀ g hinj hN c

/-- **A language in `NPSPACE` is reachability within `2 ^ poly` steps.** This is what
`savitch_halving` is applied to: the step bound `2 ^ q(|x|)` halves `q(|x|)` times before
reaching a single step, so the recursion has polynomial depth, and each of its levels stores one
configuration of a polynomially space-bounded machine. -/
theorem NPSPACE_bounded_reachability {L : Language} (hL : L ∈ NPSPACE) :
    ∃ (k : ℕ) (tm : NTM k) (q : Polynomial ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧
          tm.halted c ∧ c.output.cells 1 = Γ.one :=
  NPSPACE_bounded_reachability_internal hL

/-- Savitch's theorem settles the equality, given the immediate inclusion. -/
theorem PSPACE_eq_NPSPACE_of (h : NPSPACESubsetPSPACE) (h' : PSPACE ⊆ NPSPACE) :
    PSPACE = NPSPACE :=
  subset_antisymm h' h


/-- **`NPSPACE ⊆ PSPACE`, reduced to the existence of one machine.** For a space-bounded machine
`tm` — the space witness is part of the hypothesis — and a polynomial `q`, exhibit a deterministic
machine keeping a polynomial window that decides whether an accepting configuration is reachable
within `2 ^ q(|x|)` steps. `savitch_halving` is the recursion that makes that search affordable;
implementing it with exact space accounting is what remains. -/
theorem NPSPACE_subset_PSPACE_of_recursion
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (m : ℕ) (q : Polynomial ℕ),
      tm.DecidesInSpace L₀ S → S =O (· ^ m) →
      ∃ (k' : ℕ) (M : TM k') (r : Polynomial ℕ),
        (∀ (x : List Bool) (c' : Cfg k' M.Q), M.reaches (M.initCfg x) c' →
          c'.WithinDecisionSpace x.length (r.eval x.length)) ∧
        (∀ x : List Bool, ∃ c', M.reaches (M.initCfg x) c' ∧ M.halted c' ∧
          ((∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧ tm.halted c ∧
            c.output.cells 1 = Γ.one) → c'.output.cells 1 = Γ.one) ∧
          ((¬ ∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧ tm.halted c ∧
            c.output.cells 1 = Γ.one) → c'.output.cells 1 = Γ.zero))) :
    NPSPACE ⊆ PSPACE :=
  NPSPACE_subset_PSPACE_of_recursion_internal h

end Complexity
