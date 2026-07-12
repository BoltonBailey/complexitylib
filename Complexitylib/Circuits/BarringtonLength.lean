/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBridge
import Complexitylib.Circuits.Formula
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Log

/-!
# Barrington's theorem with a length bound

`Circuits/BarringtonRepr.lean` proves the *existence* of a width-`5` permutation
branching program for every Boolean formula, but discards the program's length.
This module re-runs the same construction while tracking length, obtaining an
explicit bound: every formula of tree-size `s` is computed by a program of length
at most `13 ^ s`.

The bound is honest but **not** the textbook `4 ^ depth` — that tighter constant
needs a smarter construction that avoids the constant conjugation overhead of the
retargeting step (`BP.Computes_retarget_len` adds `2` per re-aim, and the De
Morgan `disj` case adds a further constant). The `13 ^ size` bound here follows
directly from the recurrence of the present construction and already shows the
program is of size singly-exponential in the formula, polynomial in the number of
leaves at fixed depth — enough to place bounded-depth formulas in polynomial-size
width-`5` branching programs.

## Main results

- `Complexity.BP.length_inverse` — program inversion preserves length.
- `Complexity.BP.Computes_retarget_len`, `Complexity.BP.Computes_and5_len` —
  length-tracked versions of the bridge moves.
- `Complexity.barringtonBound`, `Complexity.barringtonBound_le` — the explicit
  length recurrence and its `13 ^ size` closed form.
- `Complexity.Computes_formula_len` — the length-tracked formula recursion.
- `Complexity.barrington_representation_len` — Barrington's theorem with the
  `13 ^ size` length bound.
-/

open scoped commutatorElement
open Equiv

set_option maxRecDepth 100000

namespace Complexity

/-- Inverting a branching program preserves its length. -/
theorem BP.length_inverse {w : ℕ} (p : BP w) : (BP.inverse p).length = p.length := by
  simp [BP.inverse]

/-- Both `5`-cycles of `S₅` have cycle type `{5}` (file-local copy). -/
private theorem cycleType5L {g : Perm (Fin 5)} (hc : g.IsCycle) (ho : orderOf g = 5) :
    g.cycleType = {5} := by
  have hs : g.support.card = 5 := by rw [← hc.orderOf]; exact ho
  rw [hc.cycleType, hs]

/-- Length-tracked retargeting: re-aiming a program to another `5`-cycle costs at
    most two extra instructions (the conjugating constants). -/
theorem BP.Computes_retarget_len {p : BP 5} {f : (ℕ → Bool) → Bool} {σ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    {a : Perm (Fin 5)} (hac : a.IsCycle) (hao : orderOf a = 5) :
    ∃ r : BP 5, BP.Computes a r f ∧ r.length ≤ p.length + 2 := by
  have hconj : IsConj σ a := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (by rw [cycleType5L hσc hσo, cycleType5L hac hao])
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  have h := BP.Computes_conj hp τ
  rw [hτ] at h
  exact ⟨_, h, by simp [List.length_append]⟩

/-- Length-tracked `AND` gate: the commutator construction at most doubles the two
    subprograms and adds a constant from the two retargetings. -/
theorem BP.Computes_and5_len {p q : BP 5} {f g : (ℕ → Bool) → Bool} {σ τ : Perm (Fin 5)}
    (hp : BP.Computes σ p f) (hσc : σ.IsCycle) (hσo : orderOf σ = 5)
    (hq : BP.Computes τ q g) (hτc : τ.IsCycle) (hτo : orderOf τ = 5)
    {c : Perm (Fin 5)} (hcc : c.IsCycle) (hco : orderOf c = 5) :
    ∃ r : BP 5, BP.Computes c r (fun α => f α && g α) ∧
      r.length ≤ 2 * p.length + 2 * q.length + 8 := by
  obtain ⟨a, b, hac, hao, hbc, hbo, hab⟩ := every_fiveCycle_is_commutator c hcc hco
  obtain ⟨p', hp', hlp'⟩ := BP.Computes_retarget_len hp hσc hσo hac hao
  obtain ⟨q', hq', hlq'⟩ := BP.Computes_retarget_len hq hτc hτo hbc hbo
  have hand := BP.Computes_and hp' hq'
  rw [hab] at hand
  refine ⟨p' ++ q' ++ BP.inverse p' ++ BP.inverse q', hand, ?_⟩
  simp only [List.length_append, BP.length_inverse]; omega

/-- Explicit length bound for the Barrington branching-program construction,
    following its recurrence: leaves cost `≤ 1`, negation adds `1`, and the `AND`
    / `OR` steps double the children and add a constant. -/
def barringtonBound : BoolFormula → ℕ
  | .var _ => 1
  | .tru => 1
  | .fls => 0
  | .neg φ => barringtonBound φ + 1
  | .conj φ ψ => 2 * barringtonBound φ + 2 * barringtonBound ψ + 8
  | .disj φ ψ => 2 * barringtonBound φ + 2 * barringtonBound ψ + 13

/-- The construction bound is dominated by `13 ^ (size φ)`. -/
theorem barringtonBound_le (φ : BoolFormula) : barringtonBound φ ≤ 13 ^ φ.size := by
  induction φ with
  | var i => simp [barringtonBound, BoolFormula.size]
  | tru => simp [barringtonBound, BoolFormula.size]
  | fls => simp [barringtonBound, BoolFormula.size]
  | neg φ ih =>
    have h1 : 1 ≤ 13 ^ φ.size := Nat.one_le_pow _ _ (by norm_num)
    simp only [barringtonBound, BoolFormula.size, pow_succ]; omega
  | conj φ ψ ihφ ihψ =>
    have hφ : (13 : ℕ) ≤ 13 ^ φ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size φ))
    have hψ : (13 : ℕ) ≤ 13 ^ ψ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size ψ))
    simp only [barringtonBound, BoolFormula.size, pow_succ, pow_add]
    nlinarith [ihφ, ihψ, hφ, hψ]
  | disj φ ψ ihφ ihψ =>
    have hφ : (13 : ℕ) ≤ 13 ^ φ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size φ))
    have hψ : (13 : ℕ) ≤ 13 ^ ψ.size :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (BoolFormula.one_le_size ψ))
    simp only [barringtonBound, BoolFormula.size, pow_succ, pow_add]
    nlinarith [ihφ, ihψ, hφ, hψ]

/-- The construction bound is also dominated by `17 ^ (depth φ)`. Because depth is
    the `NC¹` measure, this is the load-bearing bound: a formula of depth
    `d = O(log n)` compiles to a width-`5` program of length `17^d = poly(n)` — the
    `NC¹ ⊆` polynomial-size width-`5` branching programs direction of Barrington. -/
theorem barringtonBound_le_pow_depth (φ : BoolFormula) : barringtonBound φ ≤ 17 ^ φ.depth := by
  induction φ with
  | var i => simp [barringtonBound, BoolFormula.depth]
  | tru => simp [barringtonBound, BoolFormula.depth]
  | fls => simp [barringtonBound, BoolFormula.depth]
  | neg φ ih =>
    have h1 : 1 ≤ 17 ^ φ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega
  | conj φ ψ ihφ ihψ =>
    have h0 : (17 : ℕ) ^ φ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (17 : ℕ) ^ ψ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ 17 ^ max φ.depth ψ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega
  | disj φ ψ ihφ ihψ =>
    have h0 : (17 : ℕ) ^ φ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have h1 : (17 : ℕ) ^ ψ.depth ≤ 17 ^ max φ.depth ψ.depth :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hp : 1 ≤ 17 ^ max φ.depth ψ.depth := Nat.one_le_pow _ _ (by omega)
    simp only [barringtonBound, BoolFormula.depth, Nat.pow_succ]; omega

/-- **Length-tracked formula representability.** Every Boolean formula `φ` is
    computed through any target `5`-cycle by a program of length at most
    `barringtonBound φ`. Same recursion as `Computes_formula`, carrying the length
    bound through the length-tracked moves. -/
theorem Computes_formula_len (φ : BoolFormula) :
    ∀ (c : Perm (Fin 5)), c.IsCycle → orderOf c = 5 →
      ∃ r : BP 5, BP.Computes c r (fun α => BoolFormula.eval α φ) ∧
        r.length ≤ barringtonBound φ := by
  induction φ with
  | var i => intro c hcc hco; exact ⟨_, BP.Computes_var c i, by simp [barringtonBound]⟩
  | tru => intro c hcc hco; exact ⟨_, BP.Computes_true c, by simp [barringtonBound]⟩
  | fls => intro c hcc hco; exact ⟨_, BP.Computes_false c, by simp [barringtonBound]⟩
  | neg φ ih =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp, hlp⟩ := ih c⁻¹ hci hoi
    have h := BP.Computes_not hp
    rw [inv_inv] at h
    refine ⟨_, h, ?_⟩
    simp only [barringtonBound, List.length_append, List.length_cons, List.length_nil]; omega
  | conj φ ψ ihφ ihψ =>
    intro c hcc hco
    obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
    obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
    obtain ⟨r, hr, hlr⟩ := BP.Computes_and5_len hp hcc hco hq hcc hco hcc hco
    refine ⟨r, hr, ?_⟩
    simp only [barringtonBound]; omega
  | disj φ ψ ihφ ihψ =>
    intro c hcc hco
    have hci : c⁻¹.IsCycle := hcc.inv
    have hoi : orderOf c⁻¹ = 5 := by rw [orderOf_inv]; exact hco
    obtain ⟨p, hp, hlp⟩ := ihφ c hcc hco
    obtain ⟨q, hq, hlq⟩ := ihψ c hcc hco
    obtain ⟨s, hs, hls⟩ :=
      BP.Computes_and5_len (BP.Computes_not hp) hci hoi (BP.Computes_not hq) hci hoi hci hoi
    have h := BP.Computes_not hs
    rw [inv_inv] at h
    have hfun : (fun α => !((!BoolFormula.eval α φ) && (!BoolFormula.eval α ψ)))
              = (fun α => BoolFormula.eval α φ || BoolFormula.eval α ψ) := by
      funext α; simp [Bool.not_and, Bool.not_not]
    rw [hfun] at h
    refine ⟨_, h, ?_⟩
    simp only [barringtonBound, List.length_append, List.length_cons, List.length_nil] at hls ⊢
    omega

/-- **Barrington's theorem with a length bound.** Every Boolean formula `φ` is
    computed by a width-`5` permutation branching program (a nonidentity `σ ∈ S₅`
    with program-value `= σ ↔ φ` true) whose length is at most `13 ^ (size φ)`. -/
theorem barrington_representation_len (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ 13 ^ φ.size := by
  obtain ⟨hc, ho⟩ := isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨r, hr, hlr⟩ := Computes_formula_len φ (finRotate 5) hc ho
  refine ⟨r, finRotate 5, ?_, fun α => hr α, le_trans hlr (barringtonBound_le φ)⟩
  rw [Ne, ← orderOf_eq_one_iff, ho]; norm_num

/-- **Barrington's theorem, depth form.** Every Boolean formula `φ` is computed by
    a width-`5` permutation branching program of length at most `17 ^ (depth φ)`.
    For a log-depth (`NC¹`) formula this length is polynomial in the number of
    inputs — the polynomial-size direction of Barrington's characterization (with
    a loose base `17` in place of the textbook `4`). -/
theorem barrington_representation_depth (φ : BoolFormula) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ 17 ^ φ.depth := by
  obtain ⟨hc, ho⟩ := isCycle_orderOf_five_of_pow (g := finRotate 5) (by decide) (by decide)
  obtain ⟨r, hr, hlr⟩ := Computes_formula_len φ (finRotate 5) hc ho
  refine ⟨r, finRotate 5, ?_, fun α => hr α, le_trans hlr (barringtonBound_le_pow_depth φ)⟩
  rw [Ne, ← orderOf_eq_one_iff, ho]; norm_num

/-- `17 ^ (log₂ n) ≤ n ^ 5`: since `17 ≤ 2⁵`, `17^{log₂ n} ≤ (2^{log₂ n})⁵ ≤ n⁵`.
    This is the arithmetic behind "logarithmic depth gives polynomial size". -/
theorem pow_seventeen_log_le (n : ℕ) (hn : n ≠ 0) : 17 ^ Nat.log 2 n ≤ n ^ 5 := by
  calc 17 ^ Nat.log 2 n ≤ 32 ^ Nat.log 2 n := Nat.pow_le_pow_left (by omega) _
    _ = (2 ^ Nat.log 2 n) ^ 5 := by
        rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ n ^ 5 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) 5

/-- **`NC¹ ⟹` polynomial size (concrete form).** A formula of depth at most `log₂ n`
    is computed by a width-`5` permutation branching program of length at most
    `n ^ 5` — the polynomial-size direction of Barrington made explicit: the program
    is polynomial-size in `n` whenever the formula's depth is logarithmic. -/
theorem barrington_poly_of_log_depth (φ : BoolFormula) (n : ℕ) (hn : n ≠ 0)
    (hd : φ.depth ≤ Nat.log 2 n) :
    ∃ (r : BP 5) (σ : Perm (Fin 5)), σ ≠ 1 ∧
      (∀ α, BP.eval α r = if BoolFormula.eval α φ then σ else 1) ∧
      r.length ≤ n ^ 5 := by
  obtain ⟨r, σ, hσ, hev, hlen⟩ := barrington_representation_depth φ
  refine ⟨r, σ, hσ, hev, ?_⟩
  calc r.length ≤ 17 ^ φ.depth := hlen
    _ ≤ 17 ^ Nat.log 2 n := Nat.pow_le_pow_right (by omega) hd
    _ ≤ n ^ 5 := pow_seventeen_log_le n hn

end Complexity
