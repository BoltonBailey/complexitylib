/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ReachIn
public import Complexitylib.Classes.Containments.Internal.BoundedReach
public import Complexitylib.Classes.NP
public import Complexitylib.Classes.Containments.Internal.PolyWindow

/-!
# The step bound Savitch's recursion starts from

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.ReachIn` halves a step bound; this file supplies
the bound to start from. A machine using polynomial space has at most `2 ^ poly` configurations,
so reachability is always witnessed within `2 ^ poly` steps, and halving that bound bottoms out
after `poly` levels. That is the whole reason Savitch's recursion is affordable: its depth is
polynomial and each level stores one configuration, itself of polynomial size.

## Main definitions

- `codeExpBound` — a polynomial dominating the exponent of the configuration count

## Main results

- `card_Code_le_two_pow_poly` — the configuration count is `2` to a polynomial
- `NPSPACE_bounded_reachability_internal` — membership is reachability within `2 ^ poly` steps
- `NPSPACE_subset_PSPACE_of_recursion_internal` — the containment, modulo one machine
-/

@[expose] public section

namespace Complexity

/-- A polynomial dominating the exponent of the configuration count of a machine with `cardQ`
states, `k` work tapes, and space bounded by `p`. -/
noncomputable def codeExpBound (cardQ k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C cardQ + (Polynomial.X + p + Polynomial.C 2)
    + Polynomial.C (3 * k) * (p + 1) + Polynomial.C 3 * (p + Polynomial.C 2)

/-- **The configuration count is `2` to a polynomial.** -/
theorem card_Code_le_two_pow_poly (Q : Type) [Fintype Q] (k : ℕ) (S : ℕ → ℕ)
    (p : Polynomial ℕ) (hS : ∀ n, S n ≤ p.eval n) (n : ℕ) :
    Fintype.card (Code Q k n (S n)) ≤ 2 ^ (codeExpBound (Fintype.card Q) k p).eval n := by
  refine le_trans (card_Code_le_two_pow Q k n (S n)) (Nat.pow_le_pow_right (by norm_num) ?_)
  have h := hS n
  simp only [codeExpBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (le_refl _) (by omega))
    (Nat.mul_le_mul_left _ (by omega))) (Nat.mul_le_mul_left _ (by omega))

/-- **A language in `NPSPACE` is reachability within `2 ^ poly` steps.** This is the input to
Savitch's recursion: halving the bound `2 ^ q(|x|)` bottoms out after `q(|x|)` levels, so the
recursion depth is polynomial. -/
theorem NPSPACE_bounded_reachability_internal {L : Language} (hL : L ∈ NPSPACE) :
    ∃ (k : ℕ) (tm : NTM k) (q : Polynomial ℕ),
      ∀ x : List Bool, x ∈ L ↔
        ∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧
          tm.halted c ∧ c.output.cells 1 = Γ.one := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, S, hdec, hS⟩ := hm
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hS
  refine ⟨k, tm, codeExpBound (Fintype.card tm.Q) k p, fun x => ?_⟩
  rw [mem_iff_exists_accepting_reachable hdec x]
  constructor
  · rintro ⟨c, hreach, hhalt, hout⟩
    refine ⟨c, ?_, hhalt, hout⟩
    exact (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
      (fun hc hc' => NTM.cfgCode_inj_of_reachesCfg hdec x hc hc')
      (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mp hreach
  · rintro ⟨c, hle, hhalt, hout⟩
    refine ⟨c, ?_, hhalt, hout⟩
    exact (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
      (fun hc hc' => NTM.cfgCode_inj_of_reachesCfg hdec x hc hc')
      (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mpr hle


/-- **`NPSPACE ⊆ PSPACE`, reduced to the existence of one machine.** The hypothesis carries the
space witness for `tm`: without it the configuration graph is unbounded and the step bound
`2 ^ q(|x|)` is not enough to make the search decidable in polynomial space. -/
theorem NPSPACE_subset_PSPACE_of_recursion_internal
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
    NPSPACE ⊆ PSPACE := by
  intro L hL
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, tm, S, hdec, hS⟩ := hm
  obtain ⟨p, hp⟩ := BigO.pow_polynomial_bound hS
  set q : Polynomial ℕ := codeExpBound (Fintype.card tm.Q) k p with hq
  have hreach : ∀ x : List Bool, x ∈ L ↔
      ∃ c, tm.ReachesCfgLe (2 ^ q.eval x.length) (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.cells 1 = Γ.one := by
    intro x
    rw [mem_iff_exists_accepting_reachable hdec x]
    constructor
    · rintro ⟨c, hr, hh, ho⟩
      exact ⟨c, (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
        (fun ha hb => NTM.cfgCode_inj_of_reachesCfg hdec x ha hb)
        (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mp hr, hh, ho⟩
    · rintro ⟨c, hle, hh, ho⟩
      exact ⟨c, (NTM.reachesCfg_iff_reachesCfgLe tm _ (cfgCode x.length (S x.length))
        (fun ha hb => NTM.cfgCode_inj_of_reachesCfg hdec x ha hb)
        (card_Code_le_two_pow_poly tm.Q k S p hp x.length) c).mpr hle, hh, ho⟩
  obtain ⟨k', M, r, hwin, hdecM⟩ := h k tm S L m q hdec hS
  refine mem_PSPACE_of_polyWindow M r hwin fun x => ?_
  obtain ⟨c', hr, hh, hone, hzero⟩ := hdecM x
  exact ⟨c', hr, hh, fun hx => hone ((hreach x).mp hx),
    fun hx => hzero fun hc => hx ((hreach x).mpr hc)⟩

end Complexity
