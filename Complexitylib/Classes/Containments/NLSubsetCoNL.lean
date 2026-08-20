/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.L
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Classes.Containments.Internal.InductiveCounting

/-!
# `NL ⊆ coNL`

⚠️ Unreviewed by Bolton

Nondeterministic logarithmic space is closed under complement — the
Immerman–Szelepcsényi theorem.

The proof is inductive counting. Write `r_i` for the number of configurations reachable from the
initial one within `i` steps. Given `r_i`, a nondeterministic logspace machine can verify
`r_(i+1)` by cycling over all configurations and, for each, guessing and checking a short path;
the count certifies that no configuration was missed. Running this to the end yields the exact
number of reachable configurations, and a machine that knows that number can reject exactly when
no accepting configuration is reachable.

## Progress

The two statements the argument turns on are proved. `NL_complement_characterization` says what
has to be certified: an input is outside the language exactly when *every* configuration the
bounded search reaches fails to be accepting — a universally quantified statement over the
rounds. `inductive_counting_certificate` says why guessing suffices: a subset of a round that is
at least as large as the round *is* the round, so a machine that has verified `r_i` distinct
members, and has not seen `c` among them, may conclude `c` is not in round `i`. That is how a
negative fact gets certified positively, with only the count `r_i` stored.

## What the proof still needs

- The guessing procedure and its space accounting: for each round, cycle over all configurations,
  guess membership, verify a guessed member by a guessed path, and compare the tally against the
  stored `r_i`. The delicate part is that every branch either aborts or agrees on the count.
- Configurations enumerable in logarithmic space, which the coding of
  `Complexitylib.Classes.Containments.Internal.ConfigCount` supplies.

## Main results

- `NL_complement_characterization` — what the complement of an `NL` language says
- `inductive_counting_certificate` — the counting principle that makes the guessing sound
- `NL_subset_coNL_of_counting` — the containment, granted one machine

## TODO

- Build the counting machine and discharge the hypothesis of `NL_subset_coNL_of_counting`.
  `CoNLSubsetNL.coNL_subset_NL_of_NL_subset_coNL` then gives the reverse inclusion, so this
  single direction settles `NL = coNL`.
-/

@[expose] public section

namespace Complexity

/-- **`NL ⊆ coNL`** (Immerman–Szelepcsényi): nondeterministic logarithmic space is closed
under complement, by inductive counting of the reachable configurations. -/
def NLSubsetCoNL : Prop := NL ⊆ coNL

/-- **The complement of an `NL` language, spelled out.** An input is outside the language exactly
when every configuration reached by the bounded search of `NLSubsetP.NL_bounded_reachability`
fails to be accepting. Inductive counting exists to certify this universally quantified
statement nondeterministically. -/
theorem NL_complement_characterization {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (A B : ℕ),
      ∀ x : List Bool, x ∉ L ↔
        ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
          ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one) :=
  NL_complement_characterization_internal hL

/-- **The counting principle behind inductive counting.** A subset of a round of the search that
is at least as large as the round is the whole round. A machine that has verified as many
distinct members of round `i` as the round contains, without meeting `c`, has therefore proved
the negative fact `c ∉ round i` — while storing only the count. -/
theorem inductive_counting_certificate {k : ℕ} (tm : NTM k) (c₀ : Cfg k tm.Q) (i : ℕ)
    {T : Set (Cfg k tm.Q)} (hsub : T ⊆ NTM.reachSet tm c₀ i)
    (hcard : (NTM.reachSet tm c₀ i).ncard ≤ T.ncard) : T = NTM.reachSet tm c₀ i :=
  NTM.reachSet_eq_of_ncard_le tm c₀ i hsub hcard


/-- **`NL ⊆ coNL`, reduced to the existence of one machine.** For a log-space machine `tm` — the
space witness is part of the hypothesis — and a polynomial round bound, exhibit a nondeterministic
log-space transducer deciding the *negative* condition, that no configuration the bounded search
reaches is accepting. `inductive_counting_certificate` is the principle that makes that
certifiable by guessing while storing only a count. -/
theorem NL_subset_coNL_of_counting
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (A B : ℕ),
      tm.DecidesInSpace L₀ S → S =O (fun n => Nat.log 2 n) →
      ∃ (k' : ℕ) (M : NTM k') (C D : ℕ), M.IsTransducer ∧
        M.DecidesInSpace
          {x : List Bool | ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
            ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one)}
          (logWindow C D)) :
    NL ⊆ coNL :=
  NL_subset_coNL_of_counting_internal h

end Complexity
