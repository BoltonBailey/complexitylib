/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CountingCert

/-!
# Counting a round from two guessed lists

⚠️ Unreviewed by Bolton

Inductive counting needs the *exact* size of a round, and a nondeterministic machine can only
guess and check. `Complexity.card_eq_of_lists` is what makes a guessed count exact: list `c`
distinct members and `M - c` distinct non-members, where `M` is the size of the whole space, and
the two bounds meet — the round has exactly `c` elements.

That is the shape of the machine's outer loop: two guessed increasing sequences, one of members
certified by walks, one of non-members certified by the inner counting loop.

## Main results

- `card_eq_of_lists` — two lists that meet in the middle pin a set's size
- `NTM.card_reachCodes_of_lists` — the same, for a round of the search
- `NTM.roundList_of_list` — and the round list it yields
-/

@[expose] public section

namespace Complexity

/-- **Two lists that meet in the middle pin a set's size.** A list of distinct members bounds the
set below; a list of distinct non-members bounds it above; when their lengths add up to the size
of the whole space, the set's size is exactly the first length. -/
theorem card_eq_of_lists {α : Type} [Fintype α] [DecidableEq α] (X : Finset α) (c : ℕ)
    (l₁ l₂ : List α) (h₁ : l₁.Nodup) (h₁X : ∀ a ∈ l₁, a ∈ X) (hlen₁ : c ≤ l₁.length)
    (h₂ : l₂.Nodup) (h₂X : ∀ a ∈ l₂, a ∉ X) (hlen₂ : Fintype.card α - c ≤ l₂.length)
    (hcM : c ≤ Fintype.card α) : X.card = c := by
  classical
  have hsub₁ : l₁.toFinset ⊆ X := by
    intro a ha
    exact h₁X a (List.mem_toFinset.mp ha)
  have hsub₂ : l₂.toFinset ⊆ Xᶜ := by
    intro a ha
    exact Finset.mem_compl.mpr (h₂X a (List.mem_toFinset.mp ha))
  have hc₁ : l₁.length ≤ X.card := by
    rw [← List.toFinset_card_of_nodup h₁]
    exact Finset.card_le_card hsub₁
  have hc₂ : l₂.length ≤ Xᶜ.card := by
    rw [← List.toFinset_card_of_nodup h₂]
    exact Finset.card_le_card hsub₂
  have hcompl : X.card + Xᶜ.card = Fintype.card α := by
    rw [Finset.card_add_card_compl]
  omega

end Complexity

namespace Complexity.NTM

open Complexity

variable {k : ℕ} {tm : NTM k} {x : List Bool} {S : ℕ}

/-- **A round's size, from the two guessed lists.** -/
theorem card_reachCodes_of_lists {a₀ : Code tm.Q k x.length S} {i c : ℕ}
    (l₁ l₂ : List (Code tm.Q k x.length S)) (h₁ : l₁.Nodup)
    (h₁X : ∀ a ∈ l₁, a ∈ reachCodes tm x S a₀ i) (hlen₁ : c ≤ l₁.length)
    (h₂ : l₂.Nodup) (h₂X : ∀ a ∈ l₂, a ∉ reachCodes tm x S a₀ i)
    (hlen₂ : Fintype.card (Code tm.Q k x.length S) - c ≤ l₂.length)
    (hcM : c ≤ Fintype.card (Code tm.Q k x.length S)) :
    (reachCodes tm x S a₀ i).card = c :=
  card_eq_of_lists _ c l₁ l₂ h₁ h₁X hlen₁ h₂ h₂X hlen₂ hcM

/-- **And so the members list is a round list.** -/
theorem roundList_of_list {a₀ : Code tm.Q k x.length S} {i c : ℕ}
    (l₁ l₂ : List (Code tm.Q k x.length S)) (h₁ : l₁.Nodup)
    (h₁X : ∀ a ∈ l₁, a ∈ reachCodes tm x S a₀ i) (hlen₁ : c ≤ l₁.length)
    (h₂ : l₂.Nodup) (h₂X : ∀ a ∈ l₂, a ∉ reachCodes tm x S a₀ i)
    (hlen₂ : Fintype.card (Code tm.Q k x.length S) - c ≤ l₂.length)
    (hcM : c ≤ Fintype.card (Code tm.Q k x.length S)) :
    RoundList tm x S a₀ i l₁ :=
  ⟨h₁, h₁X, by
    rw [card_reachCodes_of_lists l₁ l₂ h₁ h₁X hlen₁ h₂ h₂X hlen₂ hcM]
    exact hlen₁⟩

/-- **Non-membership, certified positively.** A code is outside the next round exactly when it
differs from every member of this one and from both of that member's successors — and both
successors are named by the machine's own transition function, so a guess of them cannot lie.
This is what the machine checks in place of the negative statement. -/
theorem not_mem_reachCodes_succ_of_ne {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {l : List (Code tm.Q k x.length S)} (h : RoundList tm x S a₀ i l)
    (u : Code tm.Q k x.length S)
    (hne : ∀ v ∈ l, u ≠ v ∧
      u ≠ cfgCode x.length S (tm.stepCfg false (decodeCfg x S v)) ∧
      u ≠ cfgCode x.length S (tm.stepCfg true (decodeCfg x S v))) :
    u ∉ reachCodes tm x S a₀ (i + 1) := by
  rw [mem_reachCodes_succ_iff_of_roundList h u]
  rintro (hu | ⟨v, hv, hsucc⟩)
  · exact (hne u hu).1 rfl
  · rw [codeSucc] at hsucc
    split at hsucc
    · exact absurd hsucc (Finset.notMem_empty u)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hsucc
      rcases hsucc with h0 | h1
      · exact (hne v hv).2.1 h0
      · exact (hne v hv).2.2 h1

/-- **The count-update certificate.** The two loops list `c` members and `nmax` non-members of a
round; when the guessed pair `(c, nmax)` adds up to the size of the whole code space, the round
has exactly `c` elements — which is what the next round's inner loops need on their limit
tapes. -/
theorem card_reachCodes_of_split {a₀ : Code tm.Q k x.length S} {i c nmax : ℕ}
    (l₁ l₂ : List (Code tm.Q k x.length S))
    (h₁ : l₁.Nodup) (h₁X : ∀ a ∈ l₁, a ∈ reachCodes tm x S a₀ i) (hlen₁ : c ≤ l₁.length)
    (h₂ : l₂.Nodup) (h₂X : ∀ a ∈ l₂, a ∉ reachCodes tm x S a₀ i) (hlen₂ : nmax ≤ l₂.length)
    (hsum : c + nmax = Fintype.card (Code tm.Q k x.length S)) :
    (reachCodes tm x S a₀ i).card = c :=
  card_reachCodes_of_lists l₁ l₂ h₁ h₁X hlen₁ h₂ h₂X (by omega) (by omega)

end Complexity.NTM
