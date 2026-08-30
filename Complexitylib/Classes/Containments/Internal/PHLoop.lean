/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHBody
public import Complexitylib.Classes.Containments.Internal.PPTest

/-!
# The enumerator's loop

⚠️ Unreviewed by Bolton

The pass of `PolyExists.bodyTM` and the counting loop's own test are the two obligations of
`NTM.tallyLoop_hoareTime_of_hoare_indexed`. The test is the *same machine* the path-counting
machine of `PP ⊆ PSPACE` uses — `TM.tallyTestTM` compares the counter with the horizon and
publishes the answer, and its contract is generic in the bank — so only the body has to be
matched to the loop's state.

That matching is an identity: the loop's state at index `v` names the counter `v` and the two
tallies of `PolyExists.enumP` below, over the bank `PolyExists.enumRest` at `v + 1`, which is
exactly `PolyExists.enumBank`.

## Main results

- `PolyExists.enumP` — the predicate the loop tallies: does the witness this count denotes work?
- `PolyExists.enumBody_hoareTime` — the pass, as the loop rule's body obligation
- `PolyExists.enumTest_hoareTime` — the test, as the loop rule's test obligation
- `PolyExists.enumLoop_hoareTime` — the two composed: the loop's contract
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

open Classical in
/-- The predicate the enumerator's loop tallies: whether the witness a count denotes puts the
pair in the matrix language. The count is shifted by one — the witness at count `v` is the one
`v + 1` denotes — which is what makes every witness of the admitted lengths appear. -/
noncomputable def enumP (L' : Language) (x : List Bool) (v : ℕ) : Bool :=
  decide (pair x (dropTop (v + 1)) ∈ L')

theorem enumP_iff (L' : Language) (x : List Bool) (v : ℕ) :
    enumP L' x v = true ↔ pair x (dropTop (v + 1)) ∈ L' := by
  classical
  rw [enumP, decide_eq_true_iff]

/-- One more tally step, in the shape the pass produces. -/
theorem tally_succ_pos (P : ℕ → Bool) (v : ℕ) :
    NTM.tally P v + (if P v then 1 else 0) = NTM.tally P (v + 1) := rfl

/-- And the same for the failing tally, whose bump is the complementary one. -/
theorem tally_succ_neg (P : ℕ → Bool) (v : ℕ) :
    NTM.tally (fun u => !P u) v + (if P v then 0 else 1)
      = NTM.tally (fun u => !P u) (v + 1) := by
  show _ = NTM.tally (fun u => !P u) v + (if !P v then 1 else 0)
  cases hp : P v <;> simp

/-- **The pass, as the loop rule's body obligation.** The loop's state at index `v` *is* the bank
the pass starts from, and the state the pass leaves is the loop's state at `v + 1`. -/
theorem enumBody_hoareTime (M : TM k) {L' : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L' T) (hdecS : M.DecidesInSpace L' S)
    (x : List Bool) (N H v : ℕ) (I : Tape) (hI : TM.Parked I) (hISI : Tape.StartInvariant I)
    (hIhead : I.head = 1) (hIz : I.cells 0 = Γ.start)
    (B Hb : ℕ) (hB : 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B) (hB1 : 1 ≤ B)
    (hHb1 : 1 ≤ Hb)
    (hHS : (pair x (dropTop (v + 1))).length + S (pair x (dropTop (v + 1))).length + 2 ≤ Hb)
    (hHbH : Hb + 1 ≤ H) (hpairH : (pair x (dropTop (v + 1))).length + 1 ≤ H) :
    (bodyTM M).HoareTime
      (NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H (v + 1)) (enumP L' x) v)
      (fun inp work out => inp = I ∧
        work = enumBank k x N H (v + 1) (NTM.tally (enumP L' x) (v + 1))
          (NTM.tally (fun u => !enumP L' x u) (v + 1)) ∧
        out = TM.blankTape)
      (bodyTime k x T H Hb B v (NTM.tally (enumP L' x) v)
        (NTM.tally (fun u => !enumP L' x u) v)) := by
  have h := bodyTM_hoareTime M hdec hdecS x N H v (NTM.tally (enumP L' x) v)
    (NTM.tally (fun u => !enumP L' x u) v) I hI hISI hIhead hIz B Hb hB hB1 hHb1 hHS
    hHbH hpairH (enumP L' x v) (enumP_iff L' x v)
  refine h.consequence (fun _ _ _ hp => hp) (fun inp work out hp => ?_) (le_refl _)
  obtain ⟨hi, hw, ho⟩ := hp
  refine ⟨hi, ?_, ho⟩
  rw [hw, tally_succ_pos, tally_succ_neg]

theorem enumRest_cells_zero (k : ℕ) (x : List Bool) (N H v : ℕ) (i : Fin (enumTapes k)) :
    (enumRest k x N H v i).cells 0 = Γ.start := by
  rw [enumRest]
  split
  · exact strTape_cells_zero x
  · split
    · exact strTape_cells_zero _
    · split
      · exact NTM.natTape_cells_zero N
      · split
        · rfl
        · exact TM.blankTape_startInvariant.1

@[simp] theorem enumRest_res (k : ℕ) (x : List Bool) (N H v : ℕ) :
    enumRest k x N H v (resIdx k) = TM.blankTape :=
  enumRest_blank k x N H v _
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 0; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 1; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 3; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 7; omega))

/-- **The test, as the loop rule's test obligation.** The counting machine's own test serves the
enumerator unchanged: its contract is generic in the bank, and the enumerator's bank meets it. -/
theorem enumTest_hoareTime {L' : Language} (k : ℕ) (x : List Bool) (N H v : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (B : ℕ)
    (hB : 1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B) :
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)).HoareTime
      (fun inp work out => inp = I ∧
        work = enumBank k x N H (v + 1) (NTM.tally (enumP L' x) (v + 1))
          (NTM.tally (fun u => !enumP L' x u) (v + 1)) ∧
        out = TM.blankTape)
      (NTM.tallyPost (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H (v + 1 + 1))
        (enumP L' x) N (v + 1))
      (TM.binaryEqTime (v + 1).bits N.bits + 1 +
        (3 * (max (3 * (B + 3) + 1) (TM.resetBinaryWorkTime B 1) + 1) + 1)) := by
  have hd : TM.BinaryEqDistinct (cIdx k) (nIdx k) (resIdx k) :=
    ⟨Fin.ne_of_val_ne (by show 3 + k + 2 ≠ 3 + k + 3; omega),
      Fin.ne_of_val_ne (by show 3 + k + 2 ≠ 3 + k + 4; omega),
      Fin.ne_of_val_ne (by show 3 + k + 3 ≠ 3 + k + 4; omega)⟩
  refine (NTM.tallyTestTM_hoareTime_tallyPost (cIdx k) (aIdx k) (rIdx k) (nIdx k) (resIdx k)
    hd
    (Fin.ne_of_val_ne (by show 3 + k + 3 ≠ 3 + k + 2; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 3 ≠ 3 + k + 5; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 3 ≠ 3 + k + 8; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 2; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 5; omega))
    (Fin.ne_of_val_ne (by show 3 + k + 4 ≠ 3 + k + 8; omega))
    I (enumRest k x N H (v + 1 + 1)) (enumP L' x) N (v + 1) B 1 hI hIz
    (enumRest_parked k x N H (v + 1 + 1)) (enumRest_cells_zero k x N H (v + 1 + 1))
    (enumRest_head k x N H (v + 1 + 1)) (enumRest_n k x N H (v + 1 + 1))
    (by rw [enumRest_res]; rfl) hB).consequence ?_ (fun _ _ _ hp => hp) (le_refl _)
  rintro inp work out ⟨hi, hw, ho⟩
  exact ⟨hi, hw, by rw [ho, NTM.outSlot_blank_eq_blankTape]⟩

/-- The test's running time at one index. -/
def testTime (B N v : ℕ) : ℕ :=
  TM.binaryEqTime (v + 1).bits N.bits + 1 +
    (3 * (max (3 * (B + 3) + 1) (TM.resetBinaryWorkTime B 1) + 1) + 1)

/-- **The enumerator's loop.** Every count below the horizon is tested, the tallies come out as
the two counts of `PolyExists.enumP`, and the loop's state ends at the horizon. -/
theorem enumLoop_hoareTime (M : TM k) {L' : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L' T) (hdecS : M.DecidesInSpace L' S)
    (x : List Bool) (N H : ℕ) (hN : 1 ≤ N) (I : Tape)
    (hI : TM.Parked I) (hISI : Tape.StartInvariant I) (hIhead : I.head = 1)
    (hIz : I.cells 0 = Γ.start) (B Hb bBody bTest : ℕ) (hB1 : 1 ≤ B) (hHb1 : 1 ≤ Hb)
    (hpair : ∀ v, v < N → 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B)
    (hspace : ∀ v, v < N → (pair x (dropTop (v + 1))).length +
      S (pair x (dropTop (v + 1))).length + 2 ≤ Hb)
    (hHbH : Hb + 1 ≤ H)
    (hlenH : ∀ v, v < N → (pair x (dropTop (v + 1))).length + 1 ≤ H)
    (hbodyB : ∀ v, v < N → bodyTime k x T H Hb B v (NTM.tally (enumP L' x) v)
      (NTM.tally (fun u => !enumP L' x u) v) ≤ bBody)
    (heqB : ∀ v, v < N → 1 + 1 + TM.binaryEqTime (v + 1).bits N.bits ≤ B)
    (htestB : ∀ v, v < N → testTime B N v ≤ bTest) :
    (TM.loopTM (bodyTM M) (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k))).HoareTime
      (NTM.tallyPre (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H 1) (enumP L' x) 0)
      (NTM.tallyPost (cIdx k) (aIdx k) (rIdx k) I (enumRest k x N H (N + 1)) (enumP L' x) N N)
      (N * (bBody + bTest + 5)) :=
  NTM.tallyLoop_hoareTime_of_hoare_indexed (bodyTM M)
    (TM.tallyTestTM (cIdx k) (nIdx k) (resIdx k)) (cIdx k) (aIdx k) (rIdx k) I
    (fun j => enumRest k x N H (j + 1)) (enumP L' x)
    (fun v inp work out => inp = I ∧
      work = enumBank k x N H (v + 1) (NTM.tally (enumP L' x) (v + 1))
        (NTM.tally (fun u => !enumP L' x u) (v + 1)) ∧
      out = TM.blankTape)
    N bBody bTest hN hI (fun j i => enumRest_parked k x N H (j + 1) i)
    (fun v hv => (enumBody_hoareTime M hdec hdecS x N H v I hI hISI hIhead hIz B Hb
      (hpair v hv) hB1 hHb1 (hspace v hv) hHbH (hlenH v hv)).mono_bound (hbodyB v hv))
    (fun v inp work out h => by
      obtain ⟨hi, hw, ho⟩ := h
      exact ⟨by rw [hi]; exact hI, fun i => by
          rw [hw]; exact enumBank_parked k x N H (v + 1) _ _ i,
        by rw [ho]; exact TM.blankTape_parked,
        by rw [ho]; exact TM.blankTape_startInvariant.1,
        by rw [ho]; rfl⟩)
    (fun v hv => (enumTest_hoareTime (L' := L') k x N H v I hI hIz B
      (heqB v hv)).mono_bound (htestB v hv))

end PolyExists

end Complexity
