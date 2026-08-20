/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CodeSearch

/-!
# The counting principle behind inductive counting

⚠️ Unreviewed by Bolton

Immerman–Szelepcsényi's machine cannot store a round of the breadth-first search — that would
take polynomially many bits, not logarithmically many. It stores only the round's *size*, and
recovers everything else by guessing. The reason that is sound is a counting principle: a subset
of a round that is at least as large as the round is the whole round. So a machine that has
verified `r_i` distinct members of round `i`, and has not seen `c` among them, may conclude that
`c` is *not* in round `i` — which is a negative fact, certified positively.

This file isolates that principle and the round recursion it is applied to. Neither mentions a
machine: what remains for `NL ⊆ coNL` is the guessing procedure and its space accounting.

## Main results

- `NTM.reachCodes_mono` — the rounds only grow
- `NTM.eq_reachCodes_of_card_le` — **the counting certificate**
- `NTM.not_mem_reachCodes_of_card_le` — non-membership certified by a count
- `NTM.mem_reachCodes_succ_iff` — the round recursion the count is carried along
- `NTM.not_mem_iff_forall_not_accepting` — the complement characterization `coNL` needs
- `NTM.reachSet_eq_of_ncard_le` — the counting certificate for the specification-level rounds
- `NL_complement_characterization_internal` — the complement of an `NL` language, as a
  universally quantified statement over the rounds of the search
- `mem_NL_of_logWindow` — an explicit logarithmic window suffices for `NL`
- `NL_subset_coNL_of_counting_internal` — the containment, modulo one machine
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k} {x : List Bool} {S : ℕ}

/-! ## The rounds as growing finite sets -/

/-- The round recursion, as a membership statement: a code is in the next round exactly when it
is already present or is a successor of something present. -/
theorem mem_reachCodes_succ_iff (a₀ : Code tm.Q k x.length S) (i : ℕ)
    (a : Code tm.Q k x.length S) :
    a ∈ reachCodes tm x S a₀ (i + 1) ↔
      a ∈ reachCodes tm x S a₀ i ∨ ∃ b ∈ reachCodes tm x S a₀ i, a ∈ codeSucc tm x S b := by
  simp [reachCodes, codeRound]

/-- Each round contains the previous one. -/
theorem reachCodes_subset_succ (a₀ : Code tm.Q k x.length S) (i : ℕ) :
    reachCodes tm x S a₀ i ⊆ reachCodes tm x S a₀ (i + 1) :=
  fun _ h => (mem_reachCodes_succ_iff a₀ i _).mpr (Or.inl h)

/-- The rounds only grow. -/
theorem reachCodes_mono (a₀ : Code tm.Q k x.length S) {i j : ℕ} (hij : i ≤ j) :
    reachCodes tm x S a₀ i ⊆ reachCodes tm x S a₀ j := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact (ih (by omega)).trans (reachCodes_subset_succ a₀ j)
      · rw [show i = j + 1 from by omega]

/-! ## The counting certificate -/

/-- **The counting certificate.** A subset of a round that is at least as large as the round is
the whole round. This is what lets a machine that knows only the round's size conclude a
negative fact from a successful count. -/
theorem eq_reachCodes_of_card_le {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {T : Finset (Code tm.Q k x.length S)} (hsub : T ⊆ reachCodes tm x S a₀ i)
    (hcard : (reachCodes tm x S a₀ i).card ≤ T.card) :
    T = reachCodes tm x S a₀ i :=
  Finset.eq_of_subset_of_card_le hsub hcard

/-- **Non-membership certified by a count.** Having verified as many members of round `i` as the
round has, a code not among them is not in the round at all. -/
theorem not_mem_reachCodes_of_card_le {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {T : Finset (Code tm.Q k x.length S)} (hsub : T ⊆ reachCodes tm x S a₀ i)
    (hcard : (reachCodes tm x S a₀ i).card ≤ T.card) {a : Code tm.Q k x.length S}
    (ha : a ∉ T) : a ∉ reachCodes tm x S a₀ i := by
  rwa [eq_reachCodes_of_card_le hsub hcard] at ha

/-- Conversely, a verified subset can never exceed the round it sits inside, so the count a
machine accumulates is bounded by the true one. -/
theorem card_le_card_reachCodes {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {T : Finset (Code tm.Q k x.length S)} (hsub : T ⊆ reachCodes tm x S a₀ i) :
    T.card ≤ (reachCodes tm x S a₀ i).card :=
  Finset.card_le_card hsub

/-- The counting certificate at the level of the specification rounds: a subset of a round that
is at least as large is the whole round. -/
theorem reachSet_eq_of_ncard_le (tm : NTM k) (c₀ : Cfg k tm.Q) (i : ℕ)
    {T : Set (Cfg k tm.Q)} (hsub : T ⊆ reachSet tm c₀ i)
    (hcard : (reachSet tm c₀ i).ncard ≤ T.ncard) : T = reachSet tm c₀ i :=
  Set.eq_of_subset_of_ncard_le hsub hcard (reachSet_finite tm c₀ i)

/-! ## The complement characterization -/

/-- **What `coNL` has to certify.** An input is *outside* the language exactly when no reachable
configuration of the search is an accepting halted one — a universally quantified statement over
a finite set, which is what inductive counting turns into a nondeterministic verification. -/
theorem not_mem_iff_forall_not_accepting {L : Language} {Sf : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L Sf) (x : List Bool) {N : ℕ}
    (hN : Fintype.card (Code tm.Q k x.length (Sf x.length)) ≤ N) :
    x ∉ L ↔ ∀ a ∈ reachCodes tm x (Sf x.length)
        (cfgCode x.length (Sf x.length) (tm.initCfg x)) N,
      ¬ ((decodeCfg x (Sf x.length) a).state = tm.qhalt ∧
        (decodeCfg x (Sf x.length) a).output.cells 1 = Γ.one) := by
  rw [mem_iff_exists_mem_reachCodes hdec x hN]
  simp

end NTM

/-- **The complement of an `NL` language, spelled out.** An input is outside the language exactly
when *every* configuration the bounded search reaches fails to be accepting. This is the
universally quantified statement inductive counting has to certify nondeterministically. -/
theorem NL_complement_characterization_internal {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (A B : ℕ),
      ∀ x : List Bool, x ∉ L ↔
        ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
          ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one) := by
  obtain ⟨k, tm, A, B, hsearch⟩ := NL_bounded_reachability_internal hL
  refine ⟨k, tm, A, B, fun x => ?_⟩
  rw [hsearch x]
  simp


/-- A nondeterministic transducer respecting an explicit logarithmic window decides an `NL`
language: the `O(log n)` side is discharged once, here. -/
theorem mem_NL_of_logWindow {L : Language} {k : ℕ} (tm : NTM k) (C D : ℕ)
    (htrans : tm.IsTransducer) (hdec : tm.DecidesInSpace L (logWindow C D)) : L ∈ NL :=
  ⟨k, tm, logWindow C D, htrans, hdec, logWindow_bigO C D⟩

/-- **`NL ⊆ coNL`, reduced to the existence of one machine.** The hypothesis carries the
log-space witness for `tm`, without which the search language is not in `NL` at all. -/
theorem NL_subset_coNL_of_counting_internal
    (h : ∀ (k : ℕ) (tm : NTM k) (S : ℕ → ℕ) (L₀ : Language) (A B : ℕ),
      tm.DecidesInSpace L₀ S → S =O (fun n => Nat.log 2 n) →
      ∃ (k' : ℕ) (M : NTM k') (C D : ℕ), M.IsTransducer ∧
        M.DecidesInSpace
          {x : List Bool | ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
            ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one)}
          (logWindow C D)) :
    NL ⊆ coNL := by
  intro L hL
  obtain ⟨k, tm, S, -, hdec, hS⟩ := hL
  obtain ⟨A, B, hAB⟩ := exists_config_bound (k := k) tm.Q hS
  obtain ⟨k', M, C, D, htrans, hdecM⟩ := h k tm S L A B hdec hS
  show Lᶜ ∈ NL
  have hLeq : Lᶜ = {x : List Bool |
      ∀ c ∈ NTM.reachSet tm (tm.initCfg x) (A * (x.length + 1) ^ B),
        ¬ (tm.halted c ∧ c.output.cells 1 = Γ.one)} := by
    ext x
    rw [Set.mem_compl_iff, NTM.mem_iff_exists_mem_reachSet hdec x (hAB x.length)]
    simp
  rw [hLeq]
  exact mem_NL_of_logWindow M C D htrans hdecM

end Complexity
