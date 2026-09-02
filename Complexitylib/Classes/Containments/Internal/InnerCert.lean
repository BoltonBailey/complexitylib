/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.LtStep
public import Complexitylib.Classes.Containments.Internal.RoundCount

/-!
# What the inner counting loop proves

⚠️ Unreviewed by Bolton

The inner loop of inductive counting lists the members of round `i` — as many of them as the round
has — and checks each one against the code `u` under test. This file is the mathematics of that
list: increasing means distinct, distinct and as many as the round means *all* of them, and a code
that differs from every member and from both successors of every member is not in round `i + 1`.

The list itself is never on a tape. It exists only in the invariant of the loop that guesses it
one entry at a time.

## Main results

- `nodup_of_pairwise_codeLt` — an increasing list is duplicate-free
- `not_mem_round_succ_of_list` — what the inner loop establishes about `u`
-/

@[expose] public section

namespace Complexity

variable {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}

/-- **An increasing list of codes is duplicate-free.** -/
theorem nodup_of_pairwise_codeLt {l : List (Code tm.Q kk x.length S)}
    (h : l.Pairwise (codeLt tm x S)) : l.Nodup :=
  h.imp ne_of_codeLt

/-- **What the inner loop establishes.** Given as many distinct verified members of round `i` as
the round contains, none of which is `u` and none of whose two successors is `u`, the code `u` is
not in round `i + 1`. -/
theorem not_mem_round_succ_of_list {a₀ : Code tm.Q kk x.length S} {i : ℕ}
    {l : List (Code tm.Q kk x.length S)} (u : Code tm.Q kk x.length S)
    (hlt : l.Pairwise (codeLt tm x S))
    (hmem : ∀ v ∈ l, v ∈ NTM.reachCodes tm x S a₀ i)
    (hcard : (NTM.reachCodes tm x S a₀ i).card ≤ l.length)
    (hne : ∀ v ∈ l, u ≠ v ∧ u ≠ succCode tm x S false v ∧ u ≠ succCode tm x S true v) :
    u ∉ NTM.reachCodes tm x S a₀ (i + 1) :=
  NTM.not_mem_reachCodes_succ_of_ne ⟨nodup_of_pairwise_codeLt hlt, hmem, hcard⟩ u hne

/-- **And the same list is a round list**, which is what the certificate of the whole search
needs. -/
theorem roundList_of_pairwise {a₀ : Code tm.Q kk x.length S} {i : ℕ}
    {l : List (Code tm.Q kk x.length S)} (hlt : l.Pairwise (codeLt tm x S))
    (hmem : ∀ v ∈ l, v ∈ NTM.reachCodes tm x S a₀ i)
    (hcard : (NTM.reachCodes tm x S a₀ i).card ≤ l.length) :
    NTM.RoundList tm x S a₀ i l :=
  ⟨nodup_of_pairwise_codeLt hlt, hmem, hcard⟩

/-- **Adding a code above every one listed keeps the list increasing.** This is the step the
inner loop's invariant takes: the comparison the machine ran says the new code is above the one it
remembered, and transitivity carries that back over the whole list. -/
theorem pairwise_codeLt_concat {l : List (Code tm.Q kk x.length S)}
    {p v : Code tm.Q kk x.length S} (hlt : l.Pairwise (codeLt tm x S))
    (hp : ∀ w ∈ l, codeLt tm x S w p ∨ w = p) (hpv : codeLt tm x S p v) :
    (l ++ [v]).Pairwise (codeLt tm x S) := by
  refine List.pairwise_append.mpr ⟨hlt, List.pairwise_singleton _ _, fun w hw v' hv' => ?_⟩
  rw [List.mem_singleton.mp hv']
  rcases hp w hw with h | h
  · exact codeLt_trans h hpv
  · rw [h]
    exact hpv

end Complexity
