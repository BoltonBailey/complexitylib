/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenState
public import Mathlib.Algebra.Field.ZMod

/-!
# Reading polynomials off messages, and the abstract run as a fold

⚠️ Unreviewed by Bolton

Two bridges between the concrete verifier and the abstract protocol:

- `parsePoly` reads a polynomial off a coefficient string of `D + 1` blocks of width `w`,
  highest degree first, and `coeffBlocks_parsePoly` says a well-formed string is exactly its
  coefficient blocks;
- `runFold` is `OpChain.accept` unrolled into a left fold over the rounds — the state after each
  round is a point, a claim and a flag — which is the shape the transcript invariant follows.

## Main results

- `coeffBlocks_parsePoly`, `parsePoly_natDegree_le`
- `encZMod_injective`
- `accept_iff_runFold`
-/

@[expose] public section

namespace Complexity

open OpChain

/-! ## Parsing -/

variable {p : ℕ} [NeZero p]

/-- The polynomial with coefficient blocks `msg`, `D + 1` blocks of width `w`, highest degree
first. -/
noncomputable def parsePoly (w D : ℕ) (msg : List Bool) : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range (D + 1),
    Polynomial.C ((binValLE (wBlock msg (j * w) w) : ℕ) : ZMod p) * Polynomial.X ^ (D - j)

omit [NeZero p] in
theorem parsePoly_natDegree_le (w D : ℕ) (msg : List Bool) :
    (parsePoly (p := p) w D msg).natDegree ≤ D := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
  omega

omit [NeZero p] in
theorem parsePoly_coeff (w D : ℕ) (msg : List Bool) {j : ℕ} (hj : j ≤ D) :
    (parsePoly (p := p) w D msg).coeff (D - j)
      = ((binValLE (wBlock msg (j * w) w) : ℕ) : ZMod p) := by
  rw [parsePoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro k hk hkj
    rw [Finset.mem_range] at hk
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem encZMod_injective (w : ℕ) (hp : p < 2 ^ w) :
    Function.Injective (encZMod w : ZMod p → List Bool) := by
  intro a b h
  have := congrArg binValLE h
  rw [binValLE_encZMod w hp, binValLE_encZMod w hp] at this
  exact ZMod.val_injective p this

/-- **A well-formed coefficient string is the coefficient blocks of the polynomial it
parses to.** -/
theorem coeffBlocks_parsePoly (w D : ℕ) (hp : p < 2 ^ w) (bs : List (List Bool))
    (hlen : bs.length = D + 1) (hw : ∀ b ∈ bs, b.length = w) (hv : ∀ b ∈ bs, binValLE b < p) :
    coeffBlocks w (parsePoly (p := p) w D bs.flatten) (D + 1) = bs := by
  refine List.ext_getElem (by simp [coeffBlocks, hlen]) fun j h1 h2 => ?_
  have hj : j < D + 1 := by simpa [coeffBlocks] using h1
  simp only [coeffBlocks, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]
  rw [show D + 1 - 1 - j = D - j by omega, parsePoly_coeff w D _ (by omega),
    wBlock_flatten w bs j hw (by omega)]
  refine eq_of_binValLE_eq ?_ ?_
  · rw [encZMod_length, hw _ (List.getElem_mem (by omega))]
  · rw [binValLE_encZMod w hp, ZMod.val_natCast,
      Nat.mod_eq_of_lt (hv _ (List.getElem_mem (by omega)))]

/-! ## The run as a fold -/

variable {F : Type} [Field F] [DecidableEq F]

/-- One round of the abstract run: the point, the claim and the flag, given the operator, its
degree bound, the prover's polynomial and the challenge. -/
def runStep (o : Op) (d : ℕ) (s : Polynomial F) (t : F) :
    (ℕ → F) × F × Bool → (ℕ → F) × F × Bool
  | (a, C, ok) => (Function.update a o.var t, s.eval t,
      ok && decide (s.natDegree ≤ d) && decide (o.check a s = C))

/-- The abstract run, as a fold over the rounds. -/
def runFold : List Op → List ℕ → SumCheck.Strategy F → List F →
    (ℕ → F) × F × Bool → (ℕ → F) × F × Bool
  | [], _, _, _, st => st
  | _ :: _, _, _, [], st => (st.1, st.2.1, false)
  | o :: os, ds, P, t :: ts, st =>
      runFold os ds.tail (fun h => P (t :: h)) ts (runStep o (ds.headD 0) (P []) t st)

/-- The flag of the fold factors through the initial flag; the point and the claim ignore it. -/
theorem runFold_flag : ∀ (ops : List Op) (ds : List ℕ) (P : SumCheck.Strategy F) (ts : List F)
    (a : ℕ → F) (C : F) (ok : Bool),
    runFold ops ds P ts (a, C, ok)
      = ((runFold ops ds P ts (a, C, true)).1, (runFold ops ds P ts (a, C, true)).2.1,
          ok && (runFold ops ds P ts (a, C, true)).2.2)
  | [], _, _, _, a, C, ok => by simp [runFold]
  | _ :: _, _, _, [], a, C, ok => by simp [runFold]
  | o :: os, ds, P, t :: ts, a, C, ok => by
      rw [runFold, runFold, runStep, runStep, runFold_flag os _ _ _ _ _
        (ok && decide ((P []).natDegree ≤ ds.headD 0) && decide (o.check a (P []) = C)),
        runFold_flag os _ _ _ _ _
        (true && decide ((P []).natDegree ≤ ds.headD 0) && decide (o.check a (P []) = C))]
      simp only [Bool.true_and, Bool.and_assoc]

/-- **`accept` is the fold.** -/
theorem accept_iff_runFold (f : (ℕ → F) → F) :
    ∀ (ops : List Op) (ds : List ℕ) (P : SumCheck.Strategy F) (a : ℕ → F) (C : F)
      (r : Fin ops.length → F),
      accept ops ds f a C P r
        ↔ (runFold ops ds P (List.ofFn r) (a, C, true)).2.2 = true ∧
          f (runFold ops ds P (List.ofFn r) (a, C, true)).1
            = (runFold ops ds P (List.ofFn r) (a, C, true)).2.1
  | [], _, _, a, C, _ => by simp [accept, runFold]
  | o :: os, ds, P, a, C, r => by
      rw [List.ofFn_succ, runFold, runStep, runFold_flag]
      simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      show (_ ∧ _ ∧ accept os ds.tail f _ _ _ (Fin.tail r)) ↔ _
      rw [accept_iff_runFold f os ds.tail (fun h => P (r 0 :: h)) _ _ (Fin.tail r)]
      tauto

end Complexity
