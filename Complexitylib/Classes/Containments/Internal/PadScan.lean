/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SuccStepTriple

/-!
# Pinning the padding of a code tuple

⚠️ Unreviewed by Bolton

A code's blocks are laid out after the parameter block, so every block but the first begins with
as many padding cells as a transition's parameters occupy. The walk never reads those cells, so
what a walk establishes — `Complexity.HoldsCodeTail` — says nothing about them.

A *comparison* between two tuples does read them, so a certificate that compares tuples has to pin
them: `Complexity.padZeroScanner` checks that they are zero, and then a tuple that holds a code
holds it cell for cell (`Complexity.holdsBlocks_of_holdsCodeTail`). An honest guess writes zeros
there anyway — `Complexity.codeBlockScan` begins each block with them.

## Main definitions

- `padZeroScanner` — the check that a tuple's padding is zero

## Main results

- `padZeroScanner_decides` — what it decides
- `holdsBlocks_of_holdsCodeTail` — a code tuple with zero padding is exactly the code's blocks
-/

@[expose] public section

namespace Complexity

/-- **The check that every block's padding is zero.** -/
noncomputable def padZeroScanner {kk jj : ℕ} (tm : NTM kk)
    (j : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.all (kk + 2) (fun i =>
    ((Scanner.isConst jj (j (i.val + 1)) Γ.zero).after 0).upTo (succParamsCodec tm.Q kk).width)

/-- **What it decides.** -/
theorem padZeroScanner_decides {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (j : ℕ → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) :
    (padZeroScanner tm j).emit
        ((padZeroScanner tm j).run cols (walkScanLen tm nn S)) = true ↔
      ∀ i : Fin (kk + 2), ∀ q, 1 ≤ q → q ≤ (succParamsCodec tm.Q kk).width →
        cols q (j (i.val + 1)) = Γ.zero := by
  have hle : (succParamsCodec tm.Q kk).width ≤ walkScanLen tm nn S := by
    rw [walkScanLen]
    omega
  rw [padZeroScanner, Scanner.all_emit_run]
  constructor
  · intro h i q h1 h2
    have hi := h i
    rw [Scanner.isConst_range_run jj (j (i.val + 1)) Γ.zero cols 0
      ((succParamsCodec tm.Q kk).width) (walkScanLen tm nn S) hle] at hi
    exact hi q (by omega) h2
  · intro h i
    rw [Scanner.isConst_range_run jj (j (i.val + 1)) Γ.zero cols 0
      ((succParamsCodec tm.Q kk).width) (walkScanLen tm nn S) hle]
    intro q h1 h2
    exact h i q (by omega) h2

/-- **A code tuple with zero padding spells the code out.** With the padding pinned, the fields
pinned by `Complexity.HoldsCodeScan` and the last cell pinned by the tail check, every cell of
every block is determined — which is what a comparison between tuples needs. -/
theorem holdsBlocks_of_holdsCodeTail {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (ha : HoldsCodeTail tm x S cols j a)
    (hpad : ∀ i : Fin (kk + 2), ∀ q, 1 ≤ q → q ≤ (succParamsCodec tm.Q kk).width →
      cols q (j (i.val + 1)) = Γ.zero) :
    ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p) := by
  obtain ⟨⟨hst, hhd, hwk, hot⟩, htail⟩ := ha
  have hfield : ∀ p, p ≠ 0 → p < kk + 3 →
      HoldsBits cols (succParamsCodec tm.Q kk).width (j p) (codeBlock tm x S a p) := by
    intro p hp0 hp
    by_cases hp1 : p = 1
    · subst hp1
      rw [codeBlock, dif_neg (by omega), dif_pos rfl]
      exact hhd
    · by_cases hplt : p < kk + 2
      · have hi : (⟨p - 2, by omega⟩ : Fin kk).val + 2 = p := by
          show p - 2 + 2 = p
          omega
        have h := (hwk ⟨p - 2, by omega⟩).bits
        rw [show (codeRegsOf (kk := kk) j).wk ⟨p - 2, by omega⟩ = j p by
          show j ((⟨p - 2, by omega⟩ : Fin kk).val + 2) = j p
          rw [hi]] at h
        rw [codeBlock, dif_neg hp0, dif_neg hp1, dif_pos (by omega)]
        exact h
      · have hpk : p = kk + 2 := by omega
        subst hpk
        rw [codeBlock, dif_neg hp0, dif_neg hp1, dif_neg (by omega)]
        exact hot.bits
  intro p hp
  by_cases hp0 : p = 0
  · subst hp0
    have hblk0 : codeBlockScan tm x S a 0 = codeBlock tm x S a 0 := by
      rw [codeBlockScan, if_pos rfl]
    rw [hblk0, codeBlock_st]
    exact hst
  · have hblk : codeBlockScan tm x S a p
        = List.replicate (succParamsCodec tm.Q kk).width false
          ++ (codeBlock tm x S a p ++ [false]) := by
      rw [codeBlockScan, if_neg hp0]
    have hlenc : (codeBlock tm x S a p).length = codeWidthRaw tm x.length S p :=
      codeBlock_length tm x S a p
    intro q hq
    have hqlen : q < (succParamsCodec tm.Q kk).width + (codeWidthRaw tm x.length S p + 1) := by
      have hl := codeBlockScan_length tm x S a p
      rw [blockLen, if_neg hp0] at hl
      omega
    have hgetD : (codeBlockScan tm x S a p)[q] = (codeBlockScan tm x S a p).getD q false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      rfl
    rw [hgetD, hblk, List.getD_eq_getElem?_getD]
    set w := (succParamsCodec tm.Q kk).width with hw
    by_cases hqw : q < w
    · rw [List.getElem?_append_left (by rw [List.length_replicate]; omega),
        List.getElem?_replicate_of_lt hqw, Nat.zero_add]
      have h := hpad ⟨p - 1, by omega⟩ (q + 1) (by omega) (by omega)
      rw [show (⟨p - 1, by omega⟩ : Fin (kk + 2)).val + 1 = p by
        show p - 1 + 1 = p
        omega] at h
      rw [h]
      rfl
    · rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
        List.length_replicate]
      by_cases hqf : q - w < (codeBlock tm x S a p).length
      · rw [List.getElem?_append_left hqf, List.getElem?_eq_getElem hqf]
        have h := hfield p hp0 hp (q - w) hqf
        rw [show w + (q - w) + 1 = 0 + q + 1 by omega] at h
        rw [h]
        rfl
      · rw [List.getElem?_append_right (by omega),
          show q - w - (codeBlock tm x S a p).length = 0 by
            rw [codeBlock_length tm x S a p]
            omega]
        have h := htail ⟨p - 1, by omega⟩
        rw [show (⟨p - 1, by omega⟩ : Fin (kk + 2)).val + 1 = p by
          show p - 1 + 1 = p
          omega, blockLen, if_neg hp0] at h
        rw [Nat.zero_add, show q + 1 = w + (codeWidthRaw tm x.length S p + 1) by
          rw [codeBlock_length tm x S a p] at hqf
          omega, h]
        rfl

end Complexity
