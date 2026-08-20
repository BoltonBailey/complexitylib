/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ReachSet

/-!
# Step-counted reachability and the halving recursion

⚠️ Unreviewed by Bolton

Savitch's theorem rests on one combinatorial identity: a walk of at most `m + n` steps is a walk
of at most `m` steps followed by a walk of at most `n` steps, and conversely. Taking `m = n`
turns a bound of `2t` into two independent subproblems with bound `t`, so a bound of `2 ^ i`
recurses to depth `i` — the recursion whose stack a space-bounded machine can afford because
each level stores only one midpoint.

Nothing here is about space, and nothing is about a machine: this is the pure statement that the
midpoint search is correct, which is the part of Savitch's argument that has to be true before
any bookkeeping is attempted.

The same step counting supplies the numbers that the Immerman–Szelepcsényi counting argument
compares, so `NLSubsetCoNL` draws on this file too.

## Main results

- `NTM.ReachesCfgIn.trans`, `NTM.ReachesCfgIn.split` — walks concatenate and split
- `NTM.reachesCfgLe_add_iff` — **the midpoint recursion**
- `NTM.reachesCfgLe_two_mul_iff`, `NTM.reachesCfgLe_two_pow_succ_iff` — its halving forms
- `NTM.mem_reachSet_iff_reachesCfgLe` — the rounds of the search are exactly the step bounds
- `NTM.reachesCfg_iff_reachesCfgLe` — every reachable configuration is reachable within the
  number of configuration codes
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k}

/-! ## Walks concatenate and split -/

/-- Walks concatenate, and their lengths add. -/
theorem ReachesCfgIn.trans {s t : ℕ} {c c' c'' : Cfg k tm.Q}
    (h : tm.ReachesCfgIn s c c') (h' : tm.ReachesCfgIn t c' c'') :
    tm.ReachesCfgIn (s + t) c c'' := by
  induction h with
  | refl _ => simpa using h'
  | @head c₁ c₂ c₃ t₀ hstep _ ih =>
      rw [show t₀ + 1 + t = (t₀ + t) + 1 from by omega]
      exact .head hstep (ih h')

/-- **Walks split at any point.** A walk of `s + t` steps passes through a midpoint after
exactly `s` of them. -/
theorem ReachesCfgIn.split {s t : ℕ} {c c'' : Cfg k tm.Q}
    (h : tm.ReachesCfgIn (s + t) c c'') :
    ∃ m, tm.ReachesCfgIn s c m ∧ tm.ReachesCfgIn t m c'' := by
  induction s generalizing c with
  | zero => exact ⟨c, .refl c, by simpa using h⟩
  | succ s ih =>
      rw [show s + 1 + t = (s + t) + 1 from by omega] at h
      cases h with
      | head hstep hrest =>
          obtain ⟨m, hm, hm'⟩ := ih hrest
          exact ⟨m, .head hstep hm, hm'⟩

/-- A step bound can always be relaxed. -/
theorem ReachesCfgLe.mono {s t : ℕ} {c c' : Cfg k tm.Q} (h : tm.ReachesCfgLe s c c')
    (hst : s ≤ t) : tm.ReachesCfgLe t c c' := by
  obtain ⟨u, hu, hwalk⟩ := h
  exact ⟨u, by omega, hwalk⟩

/-- A configuration reaches itself in no steps. -/
theorem reachesCfgLe_refl (tm : NTM k) (t : ℕ) (c : Cfg k tm.Q) : tm.ReachesCfgLe t c c :=
  ⟨0, Nat.zero_le t, .refl c⟩

/-! ## The midpoint recursion -/

/-- **Savitch's recursion.** A walk of at most `m + n` steps is exactly a walk of at most `m`
steps to some midpoint followed by a walk of at most `n` steps from it. The midpoint is the only
thing a recursive procedure has to remember. -/
theorem reachesCfgLe_add_iff (tm : NTM k) (m n : ℕ) (c c'' : Cfg k tm.Q) :
    tm.ReachesCfgLe (m + n) c c'' ↔
      ∃ mid, tm.ReachesCfgLe m c mid ∧ tm.ReachesCfgLe n mid c'' := by
  constructor
  · rintro ⟨s, hs, hwalk⟩
    rcases Nat.lt_or_ge s m with hlt | hge
    · exact ⟨c'', ⟨s, hlt.le, hwalk⟩, reachesCfgLe_refl tm n c''⟩
    · obtain ⟨mid, h₁, h₂⟩ :=
        ReachesCfgIn.split (s := m) (t := s - m) (by rwa [show m + (s - m) = s from by omega])
      exact ⟨mid, ⟨m, le_rfl, h₁⟩, ⟨s - m, by omega, h₂⟩⟩
  · rintro ⟨mid, ⟨s, hs, h₁⟩, ⟨t, ht, h₂⟩⟩
    exact ⟨s + t, by omega, h₁.trans h₂⟩

/-- The halving form: a bound of `2 t` splits into two independent bounds of `t`. -/
theorem reachesCfgLe_two_mul_iff (tm : NTM k) (t : ℕ) (c c'' : Cfg k tm.Q) :
    tm.ReachesCfgLe (2 * t) c c'' ↔
      ∃ mid, tm.ReachesCfgLe t c mid ∧ tm.ReachesCfgLe t mid c'' := by
  rw [show 2 * t = t + t from by omega]
  exact reachesCfgLe_add_iff tm t t c c''

/-- **The recursion Savitch's machine runs.** A bound of `2 ^ (i + 1)` recurses to two
subproblems with bound `2 ^ i`, so the depth is `i` and each level stores one midpoint. -/
theorem reachesCfgLe_two_pow_succ_iff (tm : NTM k) (i : ℕ) (c c'' : Cfg k tm.Q) :
    tm.ReachesCfgLe (2 ^ (i + 1)) c c'' ↔
      ∃ mid, tm.ReachesCfgLe (2 ^ i) c mid ∧ tm.ReachesCfgLe (2 ^ i) mid c'' := by
  have h2 : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ, Nat.mul_comm]
  rw [h2]
  exact reachesCfgLe_two_mul_iff tm (2 ^ i) c c''

/-! ## Agreement with the breadth-first rounds -/

/-- The rounds of the breadth-first search are exactly the step bounds. -/
theorem mem_reachSet_iff_reachesCfgLe (tm : NTM k) (c₀ : Cfg k tm.Q) :
    ∀ (t : ℕ) (c : Cfg k tm.Q), c ∈ reachSet tm c₀ t ↔ tm.ReachesCfgLe t c₀ c := by
  intro t
  induction t with
  | zero =>
      intro c
      constructor
      · intro hc
        rw [Set.mem_singleton_iff.mp hc]
        exact reachesCfgLe_refl tm 0 c₀
      · rintro ⟨s, hs, hwalk⟩
        rw [Nat.le_zero.mp hs] at hwalk
        cases hwalk
        exact rfl
  | succ t ih =>
      intro c
      constructor
      · rintro (hc | ⟨c', hc', hstep⟩)
        · exact ((ih c).mp hc).mono (by omega)
        · obtain ⟨s, hs, hwalk⟩ := (ih c').mp hc'
          exact ⟨s + 1, by omega, hwalk.trans (.head hstep (.refl c))⟩
      · rintro ⟨s, hs, hwalk⟩
        rcases Nat.lt_or_ge s (t + 1) with hlt | hge
        · exact Or.inl ((ih c).mpr ⟨s, by omega, hwalk⟩)
        · have hst : s = t + 1 := by omega
          subst hst
          obtain ⟨mid, h₁, h₂⟩ := ReachesCfgIn.split (s := t) (t := 1) hwalk
          cases h₂ with
          | head hstep hrest =>
              cases hrest
              exact Or.inr ⟨mid, (ih mid).mpr ⟨t, le_rfl, h₁⟩, hstep⟩

/-- **Every reachable configuration is reachable within the number of codes.** A walk longer
than that repeats a configuration, and the repetition can be cut out. -/
theorem reachesCfg_iff_reachesCfgLe {α : Type} [Fintype α] (tm : NTM k) (c₀ : Cfg k tm.Q)
    (g : Cfg k tm.Q → α)
    (hinj : ∀ {c c' : Cfg k tm.Q}, tm.ReachesCfg c₀ c → tm.ReachesCfg c₀ c' → g c = g c' → c = c')
    {N : ℕ} (hN : Fintype.card α ≤ N) (c : Cfg k tm.Q) :
    tm.ReachesCfg c₀ c ↔ tm.ReachesCfgLe N c₀ c := by
  rw [← mem_reachSet_iff_reachesCfgLe]
  exact reachesCfg_iff_mem_reachSet tm c₀ g hinj hN c

end NTM

end Complexity
