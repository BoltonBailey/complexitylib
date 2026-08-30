/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P
public import Complexitylib.Classes.P.Cobham.Internal.BumpBits
public import Complexitylib.Classes.P.Cobham.Internal.FPBridge
public import Complexitylib.Classes.P.Cobham.Internal.HeadOps
public import Complexitylib.Classes.P.Cobham.Internal.BinValLE
public import Complexitylib.Classes.PCP.Internal.SubsetNP

/-!
# Coin strings from their index

A loop over the coin strings of a verifier receives its index in unary, since
that is the form a polynomial-time loop counter takes. This module turns such an
index into the coin string itself: the fixed-width binary counter of
`SavitchBits` is incremented that many times, starting from all zeros.

Nothing here is arithmetic on the index. `bumpBits` is the width-preserving
increment already proved polynomial-time for Savitch's theorem, and iterating a
polynomial-time step a polynomial number of times is `iterate_mem_FP`.

## Main results

- `Complexity.coinStr` — the counter after that many increments
- `Complexity.coinStr_mem_FP` — in polynomial time, for any index
- `Complexity.toList_coinOfIndex` — it is the coin string `SubsetNP` names
-/

@[expose] public section

namespace Complexity

/-- A block of zeros as wide as a computed string. -/
theorem zeroBlockFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => List.replicate (a z).length false) ∈ FP :=
  unFn_mem_FP (g := fun s => List.replicate s.length false)
    (Cobham.zeroBlockFn (Cobham.proj 0)) ha

theorem bumpBits_mem_FP : bumpBits ∈ FP := by
  have h := bumpCodeFn_mem_FP id_mem_FP
  refine mem_FP_of_eq h fun z => ?_
  simp

theorem length_bumpBits_iterate (n : ℕ) (w : List Bool) :
    (bumpBits^[n] w).length = w.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', bumpBits_length, ih]

/-- The width-`t` counter after `c` increments. Total: past `2 ^ t` it wraps,
which never happens where it is used but keeps the function unconditional. -/
def coinStr (t c : ℕ) : List Bool := bumpBits^[c] (List.replicate t false)

theorem coinStr_eq {t c : ℕ} (h : c < 2 ^ t) : coinStr t c = bitsOfLenLE t c := by
  rw [coinStr, ← bitsOfLenLE_zero t, bumpBits_iterate _ _ h]

/-- **The counter value in polynomial time.** With the width and the index both
supplied in unary, the counter is polynomial-time computable — with no bound on
the index, so that the function is total where a loop guard has not yet been
applied. -/
theorem coinStr_mem_FP {t c : List Bool → ℕ}
    (ht : (fun z => List.replicate (t z) true) ∈ FP)
    (hc : (fun z => List.replicate (c z) true) ∈ FP) :
    (fun z => coinStr (t z) (c z)) ∈ FP := by
  have hinit : (fun z => List.replicate (t z) false) ∈ FP := by
    have := zeroBlockFn_mem_FP ht
    simpa using this
  have hbound : ∀ z : List Bool, ∀ n ≤ (List.replicate (c z) true).length,
      (bumpBits^[n] (List.replicate (t z) false)).length
        ≤ (List.replicate (t z) false).length := fun z n _ =>
    le_of_eq (length_bumpBits_iterate n _)
  have hiter := Cobham.iterate_mem_FP bumpBits_mem_FP hinit hc hinit hbound
  refine mem_FP_of_eq hiter fun z => ?_
  rw [List.length_replicate, coinStr]

/-- **The counter is the coin string.** `SubsetNP` indexes coin strings by their
little-endian binary value, which is exactly what the counter holds. -/
theorem toList_coinOfIndex (t c : ℕ) (h : c < 2 ^ t) :
    BitString.toList (PCPVerifier.coinOfIndex (t := t) ⟨c, h⟩) = bitsOfLenLE t c := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < t := by simpa using h1
  rw [bitsOfLenLE_getElem t c j hj,
    BitString.getElem_toList (PCPVerifier.coinOfIndex (t := t) ⟨c, h⟩) ⟨j, hj⟩,
    PCPVerifier.coinOfIndex]
  have hval := finFunctionFinEquiv_symm_apply_val (⟨c, h⟩ : Fin (2 ^ t)) (⟨j, hj⟩ : Fin t)
  have h2 : (finFunctionFinEquiv.symm (⟨c, h⟩ : Fin (2 ^ t)) ⟨j, hj⟩ = 1)
      ↔ (c / 2 ^ j % 2 = 1) := by
    rw [Fin.ext_iff, hval]
    exact Iff.rfl
  exact decide_eq_decide.mpr h2

/-- The index of the coin string an index names. -/
theorem coinIndex_coinOfIndex {t : ℕ} (c : Fin (2 ^ t)) :
    PCPVerifier.coinIndex (PCPVerifier.coinOfIndex c) = c.val := by
  have hd : PCPVerifier.coinDigits (PCPVerifier.coinOfIndex c)
      = finFunctionFinEquiv.symm c := by
    funext i
    rw [PCPVerifier.coinDigits, PCPVerifier.coinOfIndex]
    have hv : (finFunctionFinEquiv.symm c i).val = 0
        ∨ (finFunctionFinEquiv.symm c i).val = 1 := by omega
    rcases hv with hv | hv
    · have h0 : finFunctionFinEquiv.symm c i = 0 := Fin.ext hv
      simp [h0]
    · have h1 : finFunctionFinEquiv.symm c i = 1 := Fin.ext hv
      simp [h1]
  rw [PCPVerifier.coinIndex, hd, Equiv.apply_symm_apply]

/-- **The value of a coin string is its index.** -/
theorem binValLE_toList {T : ℕ} (ρ : Fin T → Bool) :
    binValLE (BitString.toList ρ) = PCPVerifier.coinIndex ρ := by
  have hlt : PCPVerifier.coinIndex ρ < 2 ^ T := PCPVerifier.coinIndex_lt ρ
  have hρ : BitString.toList ρ = bitsOfLenLE T (PCPVerifier.coinIndex ρ) := by
    rw [← PCPVerifier.coinOfIndex_coinIndex ρ hlt, toList_coinOfIndex]
    congr 1
    rw [PCPVerifier.coinOfIndex_coinIndex ρ hlt]
  rw [hρ, binValLE_bitsOfLenLE _ _ hlt]

/-- **Counting coin strings is counting indices.** -/
theorem card_filter_coinIndex (T : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun ρ : Fin T → Bool => Q (PCPVerifier.coinIndex ρ))).card
      = ((Finset.range (2 ^ T)).filter Q).card := by
  classical
  refine Finset.card_bij (fun ρ _ => PCPVerifier.coinIndex ρ) ?_ ?_ ?_
  · intro ρ hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (PCPVerifier.coinIndex_lt ρ), hρ⟩
  · intro ρ₁ h₁ ρ₂ h₂ heq
    exact PCPVerifier.coinIndex_injective heq
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_range] at hc
    refine ⟨PCPVerifier.coinOfIndex ⟨c, hc.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [coinIndex_coinOfIndex]
      exact hc.2
    · exact coinIndex_coinOfIndex ⟨c, hc.1⟩

end Complexity
