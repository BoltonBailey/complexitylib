/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.PHBody
public import Complexitylib.Classes.Containments.Internal.PHMatrix

/-!
# One pass of the enumerator, in space

⚠️ Unreviewed by Bolton

Nine of the pass's ten stages are short, and their windows come straight from their running
times. The tenth — the matrix machine — is not short at all: it may run for exponentially many
steps, and its window has to come from its space bound instead
(`PolyExists.matrixTM_keepsWindowOn`). Composing the ten is what
`TM.seqTM_keepsWindowOn` is for.

## Main results

- `PolyExists.afterCopy_head_le`, `PolyExists.mid*_heads` — how far each intermediate state's
  heads can be
-/

@[expose] public section

namespace Complexity

namespace PolyExists

variable {k : ℕ}

/-- Every tape the copy stage leaves has its head inside the pair's width. -/
theorem afterCopy_head_le (k : ℕ) (x : List Bool) (N H v a r G : ℕ)
    (hG : (pair x (dropTop (v + 1))).length + 1 ≤ G) (i : Fin (enumTapes k)) :
    (afterCopy k x N H v a r i).head ≤ G := by
  rw [afterCopy]
  by_cases h1 : i = y1Idx k
  · rw [h1, Function.update_self]
    exact hG
  · rw [Function.update_of_ne h1]
    by_cases h2 : i = yIdx k
    · rw [h2, Function.update_self]
      show 1 ≤ G
      omega
    · rw [Function.update_of_ne h2, enumBank_head]
      omega

/-- Every tape of the loop's own state has its head at cell one. -/
theorem enumBank_head_le (k : ℕ) (x : List Bool) (N H v a r G : ℕ) (hG : 1 ≤ G)
    (i : Fin (enumTapes k)) : (enumBank k x N H v a r i).head ≤ G := by
  rw [enumBank_head]
  exact hG

theorem midMatrix_heads (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb G : ℕ)
    (b : Bool) (hHb : Hb ≤ G) (hpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midMatrix k x N H v a r I Hb b inp work out) : ∀ i, (work i).head ≤ G := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · have := (h.2.2.2.2 i hm).2.1
    omega
  · rw [h.2.2.2.1 i hm]
    exact afterCopy_head_le k x N H v a r G hpair i

theorem midParked_heads (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb G : ℕ)
    (b : Bool) (hHb : Hb + 1 ≤ G) (hpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midParked k x N H v a r I Hb b inp work out) : ∀ i, (work i).head ≤ G := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · have := (h.2.2.2.2.2 i hm).2.1
    omega
  · rw [h.2.2.2.1 i hm]
    exact afterCopy_head_le k x N H v a r G hpair i

theorem midPublish_heads (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb G : ℕ)
    (b : Bool) (hHb : Hb + 1 ≤ G) (hpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midPublish k x N H v a r I Hb b inp work out) : ∀ i, (work i).head ≤ G := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · have := (h.2.2.2.2 i hm).2.1
    omega
  · rw [h.2.2.1 i hm]
    exact afterCopy_head_le k x N H v a r G hpair i

theorem midBump_heads (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb G : ℕ)
    (b : Bool) (hHb : Hb + 1 ≤ G) (hpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (hG1 : 1 ≤ G)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midBump k x N H v a r I Hb b inp work out) : ∀ i, (work i).head ≤ G := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · have := (h.2.2.2.2.2.2.2.2 i hm).1
    omega
  · by_cases h1 : i = cIdx k
    · rw [h1, h.2.2.1, natTape_head_one]
      omega
    · by_cases h2 : i = aIdx k
      · rw [h2, h.2.2.2.1, natTape_head_one]
        omega
      · by_cases h3 : i = rIdx k
        · rw [h3, h.2.2.2.2.1, natTape_head_one]
          omega
        · rw [h.2.2.2.2.2.1 i hm h1 h2 h3]
          exact afterCopy_head_le k x N H v a r G hpair i

theorem midBumped_heads (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb G : ℕ)
    (b : Bool) (hHb : Hb + 1 ≤ G) (hpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (hG1 : 1 ≤ G)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midBumped k x N H v a r I Hb b inp work out) : ∀ i, (work i).head ≤ G := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · have := (h.2.2.2.2.2.2.2.2.2 i hm).1
    omega
  · by_cases h1 : i = cIdx k
    · rw [h1, h.2.2.1, natTape_head_one]
      omega
    · by_cases h2 : i = aIdx k
      · rw [h2, h.2.2.2.1, natTape_head_one]
        omega
      · by_cases h3 : i = rIdx k
        · rw [h3, h.2.2.2.2.1, natTape_head_one]
          omega
        · by_cases h4 : i = wIdx k
          · rw [h4, h.2.2.2.2.2.1]
            show 1 ≤ G
            omega
          · rw [h.2.2.2.2.2.2.1 i hm h1 h2 h3 h4]
            exact afterCopy_head_le k x N H v a r G hpair i

/-- The wipe's window. -/
theorem wipe_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1)
    (Hb G : ℕ) (b : Bool) (hHbH : Hb + 1 ≤ H)
    (hpairH : (pair x (dropTop (v + 1))).length + 1 ≤ H)
    (hG1 : 1 ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G) :
    (TM.wipeRewindTM (scratchTargets k) (regIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.wipeRewindTM (scratchTargets k) (regIdx k)).qstart ∧
        midBumped k x N H v a r I Hb b c.input c.work c.output) x.length
      (G + ((scratchTargets k).length * (H + 4) + H * 4 + 8 + 1 +
        ((scratchTargets k).length * (H + 4) + 1))) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (wipe_hoareTime k x N H v a r I hI hIsi Hb b hHbH hpairH)
    (fun inp work out hpre i => midBumped_heads k x N H v a r I Hb G b hGHb hGpair hG1
      inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.1]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The witness bump's window. -/
theorem witnessBump_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIhead : I.head = 1) (Hb G : ℕ) (b : Bool)
    (hG1 : 1 ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G) :
    (TM.binaryBumpTM (wIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.binaryBumpTM (wIdx k)).qstart ∧
        midBump k x N H v a r I Hb b c.input c.work c.output) x.length
      (G + TM.binaryBumpTime (dropTop (v + 1))) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (witnessBump_hoareTime k x N H v a r I hI Hb b)
    (fun inp work out hpre i => midBump_heads k x N H v a r I Hb G b hGHb hGpair hG1
      inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.1]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The tally bump's window. -/
theorem tallyBump_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIz : I.cells 0 = Γ.start) (hIhead : I.head = 1) (Hb G : ℕ) (b : Bool)
    (hG1 : 1 ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G) :
    (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k)).qstart ∧
        midPublish k x N H v a r I Hb b c.input c.work c.output) x.length
      (G + (3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
        (TM.binarySuccTime v) + 1) + 1)) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (tallyBump_hoareTime k x N H v a r I hI hIz Hb b)
    (fun inp work out hpre i => midPublish_heads k x N H v a r I Hb G b hGHb hGpair
      inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      obtain ⟨-, ⟨s, -, hs⟩, -⟩ := hpre
      rw [hs]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The publication's window. -/
theorem publishVerdict_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIhead : I.head = 1) (Hb G : ℕ) (b : Bool)
    (hG1 : 1 ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G) :
    (TM.writeOutputBitTM (vIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.writeOutputBitTM (vIdx k)).qstart ∧
        midParked k x N H v a r I Hb b c.input c.work c.output) x.length (G + 1) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (publishVerdict_hoareTime k x N H v a r I hI Hb b)
    (fun inp work out hpre i => midParked_heads k x N H v a r I Hb G b hGHb hGpair
      inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.1]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The verdict rewind's window. -/
theorem parkVerdict_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (Hb G : ℕ) (hHb1 : 1 ≤ Hb) (b : Bool)
    (hG1 : 1 ≤ G) (hGHb : Hb ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G) :
    (TM.parkRewindTM [vIdx k]).KeepsWindowOn
      (fun c => c.state = (TM.parkRewindTM [vIdx k]).qstart ∧
        midMatrix k x N H v a r I Hb b c.input c.work c.output) x.length
      (G + (1 + 1 + (2 * (max (Hb + 2) (1 * (Hb + 3) + 1) + 1) + 1))) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G)
    (parkVerdict_hoareTime k x N H v a r I hIsi hIhead Hb hHb1 b)
    (fun inp work out hpre i => midMatrix_heads k x N H v a r I Hb G b hGHb hGpair
      inp work out hpre i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.1]
      show (1 : ℕ) ≤ G + 1
      omega)

theorem afterPair_startInvariant (k : ℕ) (x : List Bool) (N H v a r : ℕ)
    (i : Fin (enumTapes k)) : Tape.StartInvariant (afterPair k x N H v a r i) := by
  rw [afterPair]
  by_cases h : i = y1Idx k
  · rw [h, Function.update_self]
    exact strTape_startInvariant _
  · rw [Function.update_of_ne h]
    exact enumBank_startInvariant k x N H v a r i

theorem afterPair_head (k : ℕ) (x : List Bool) (N H v a r : ℕ) (i : Fin (enumTapes k)) :
    (afterPair k x N H v a r i).head = 1 := by
  rw [afterPair]
  by_cases h : i = y1Idx k
  · rw [h, Function.update_self]
    exact strTape_head _
  · rw [Function.update_of_ne h, enumBank_head]

/-- The blanking stage's window. -/
theorem blankSlot_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIhead : I.head = 1) (G : ℕ) (hG1 : 1 ≤ G) :
    (TM.writeOutputBitTM (zIdx k)).KeepsWindowOn
      (fun c => c.state = (TM.writeOutputBitTM (zIdx k)).qstart ∧
        (c.input = I ∧ c.work = enumBank k x N H v a r ∧
          ∃ s : Γw, s ≠ Γw.one ∧ c.output = NTM.outSlot s)) x.length (G + 1) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G) (blankSlot_hoareTime k x N H v a r I hI)
    (fun inp work out hpre i => by
      rw [hpre.2.1]
      exact enumBank_head_le k x N H v a r G hG1 i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      obtain ⟨-, -, s, -, hs⟩ := hpre
      rw [hs]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The emitter's window. -/
theorem emit_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (B G : ℕ)
    (hB : 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B) (hG1 : 1 ≤ G) :
    (emitTM k).KeepsWindowOn
      (fun c => c.state = (emitTM k).qstart ∧
        (c.input = I ∧ c.work = enumBank k x N H v a r ∧ c.output = TM.blankTape))
      x.length (G + TM.pairInputWorkTime x (dropTop (v + 1))) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G) (emit_hoareTime k x N H v a r I hI hIsi B hB)
    (fun inp work out hpre i => by
      rw [hpre.2.1]
      exact enumBank_head_le k x N H v a r G hG1 i)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The rewinding stage's window. -/
theorem parkPair_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (B G : ℕ) (hB1 : 1 ≤ B)
    (hGB : B ≤ G) :
    (TM.parkRewindTM [xIdx k, wIdx k, y1Idx k]).KeepsWindowOn
      (fun c => c.state = (TM.parkRewindTM [xIdx k, wIdx k, y1Idx k]).qstart ∧
        midEmit k x N H v a r I B c.input c.work c.output) x.length
      (G + (1 + 1 + (2 * (max (B + 2) (3 * (B + 3) + 1) + 1) + 1))) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G) (parkPair_hoareTime k x N H v a r I hIsi hIhead B hB1)
    (fun inp work out hpre i => by
      have := hpre.2.2.2.2.2.2.2 i
      omega)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.1]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The copy stage's window. -/
theorem copyPair_keepsWindowOn (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape)
    (hI : TM.Parked I) (hIhead : I.head = 1) (G : ℕ) (hG1 : 1 ≤ G) :
    (copyPairTM k).KeepsWindowOn
      (fun c => c.state = (copyPairTM k).qstart ∧
        (c.input = I ∧ c.work = afterPair k x N H v a r ∧ c.output = TM.blankTape))
      x.length (G + (2 * (pair x (dropTop (v + 1))).length + 5)) :=
  TM.keepsWindowOn_of_hoareTime (h₀ := G) (copyPair_hoareTime k x N H v a r I hI)
    (fun inp work out hpre i => by
      rw [hpre.2.1, afterPair_head]
      omega)
    (fun inp work out hpre => by rw [hpre.1, hIhead]; omega)
    (fun inp work out hpre => by
      rw [hpre.2.2]
      show (1 : ℕ) ≤ G + 1
      omega)

/-- The evaluating stage's window, at the tapes the copy stage leaves. -/
theorem matrix_keepsWindowOn (M : TM k) {L' : Language} {S : ℕ → ℕ}
    (hdecS : M.DecidesInSpace L' S) (hne : M.qstart ≠ M.qhalt)
    (x : List Bool) (N H v a r : ℕ) (I : Tape) (hIsi : Tape.StartInvariant I)
    (hIhead : I.head = 1) (W : ℕ)
    (hW : (pair x (dropTop (v + 1))).length + S (pair x (dropTop (v + 1))).length + 2 ≤ W)
    (hWpair : (pair x (dropTop (v + 1))).length + 1 ≤ W) :
    (matrixTM M).KeepsWindowOn
      (fun c => c.state = (matrixTM M).qstart ∧
        (c.input = I ∧ c.work = afterCopy k x N H v a r ∧ c.output = TM.blankTape))
      x.length W := by
  have h := matrixTM_keepsWindowOn M hdecS hne (pair x (dropTop (v + 1))) I hIsi
    (afterCopy k x N H v a r)
    (fun i _ => afterCopy_startInvariant k x N H v a r i)
    (fun i _ => afterCopy_head_pos k x N H v a r i)
    (inputLength := x.length) (space := W)
    (fun i _ => afterCopy_head_le k x N H v a r W hWpair i) hW
    (by rw [hIhead]; omega)
  intro c hc D hD
  refine h c ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩ D hD
  rw [hc.2.2.1, matrixEntry_afterCopy]

theorem midMatrix_si (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midMatrix k x N H v a r I Hb b inp work out) :
    ∀ i, Tape.StartInvariant (work i) := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · exact (h.2.2.2.2 i hm).1
  · rw [h.2.2.2.1 i hm]
    exact afterCopy_startInvariant k x N H v a r i

theorem midParked_si (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midParked k x N H v a r I Hb b inp work out) :
    ∀ i, Tape.StartInvariant (work i) := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · exact (h.2.2.2.2.2 i hm).1
  · rw [h.2.2.2.1 i hm]
    exact afterCopy_startInvariant k x N H v a r i

theorem midPublish_si (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midPublish k x N H v a r I Hb b inp work out) :
    ∀ i, Tape.StartInvariant (work i) := by
  intro i
  by_cases hm : TM.placeWorkInMiddle 3 (k + 2) i
  · exact (h.2.2.2.2 i hm).1
  · rw [h.2.2.1 i hm]
    exact afterCopy_startInvariant k x N H v a r i

theorem midBump_si (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midBump k x N H v a r I Hb b inp work out) :
    ∀ i, Tape.StartInvariant (work i) :=
  fun i => ⟨h.2.2.2.2.2.2.2.1 i, fun j hj => (h.2.2.2.2.2.2.1 i).2 j hj⟩

theorem midBumped_si (k : ℕ) (x : List Bool) (N H v a r : ℕ) (I : Tape) (Hb : ℕ) (b : Bool)
    (inp : Tape) (work : Fin (enumTapes k) → Tape) (out : Tape)
    (h : midBumped k x N H v a r I Hb b inp work out) :
    ∀ i, Tape.StartInvariant (work i) :=
  fun i => ⟨h.2.2.2.2.2.2.2.2.1 i, fun j hj => (h.2.2.2.2.2.2.2.1 i).2 j hj⟩

/-- A contract yields the halting witness the window composition asks for. -/
theorem hoare_post_of {m : ℕ} {tm : TM m} {pre post : TM.TapePred m} {bnd : ℕ}
    (h : tm.HoareTime pre post bnd) (c : Cfg m tm.Q) (hst : c.state = tm.qstart)
    (hpre : pre c.input c.work c.output) :
    ∃ e, tm.reaches c e ∧ tm.halted e ∧ post e.input e.work e.output := by
  obtain ⟨e, t, -, hreach, hhalt, hpost⟩ := h c.input c.work c.output hpre
  refine ⟨e, ?_, hhalt, hpost⟩
  rw [show (⟨tm.qstart, c.input, c.work, c.output⟩ : Cfg m tm.Q) = c from
    Cfg.ext hst.symm rfl rfl rfl] at hreach
  exact TM.reaches_of_reachesIn hreach

/-- A configuration whose heads are inside `G` is inside any wider window. -/
theorem windowed_of_heads {Q : Type} (c : Cfg (enumTapes k) Q) (lx G W : ℕ) (hGW : G ≤ W)
    (hw : ∀ i, (c.work i).head ≤ G) (hi : c.input.head ≤ 1) (ho : c.output.head ≤ 1)
    (h1 : 1 ≤ W) : c.WithinDecisionSpace lx W :=
  ⟨⟨fun i => le_trans (hw i) hGW, by omega⟩, by omega⟩

/-- And it satisfies the left-marker invariant if each of its tapes does. -/
theorem cfgStartInvariant_of {Q : Type} (c : Cfg (enumTapes k) Q)
    (hi : Tape.StartInvariant c.input) (hw : ∀ i, Tape.StartInvariant (c.work i))
    (ho : Tape.StartInvariant c.output) : TM.CfgStartInvariant c := ⟨hi, hw, ho⟩

/-- **One pass of the enumerator keeps a window.** Nine stages are bounded by their running
times; the matrix machine is bounded by its space, which is the only bound of the ten that is
polynomial in the input length. -/
theorem bodyTM_keepsWindowOn (M : TM k) {L' : Language} {T S : ℕ → ℕ}
    (hdec : M.DecidesInTime L' T) (hdecS : M.DecidesInSpace L' S)
    (hne : M.qstart ≠ M.qhalt)
    (x : List Bool) (N H v a r : ℕ) (I : Tape) (hI : TM.Parked I)
    (hIsi : Tape.StartInvariant I) (hIhead : I.head = 1) (hIz : I.cells 0 = Γ.start)
    (B Hb G W : ℕ) (hB : 1 + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ B) (hB1 : 1 ≤ B)
    (hHb1 : 1 ≤ Hb)
    (hHS : (pair x (dropTop (v + 1))).length + S (pair x (dropTop (v + 1))).length + 2 ≤ Hb)
    (hHbH : Hb + 1 ≤ H) (hpairH : (pair x (dropTop (v + 1))).length + 1 ≤ H)
    (b : Bool) (hb : b = true ↔ pair x (dropTop (v + 1)) ∈ L')
    (hG1 : 1 ≤ G) (hGB : B ≤ G) (hGHb : Hb + 1 ≤ G)
    (hGpair : (pair x (dropTop (v + 1))).length + 1 ≤ G)
    (hW1 : G + 1 ≤ W)
    (hW2 : G + TM.pairInputWorkTime x (dropTop (v + 1)) ≤ W)
    (hW3 : G + (1 + 1 + (2 * (max (B + 2) (3 * (B + 3) + 1) + 1) + 1)) ≤ W)
    (hW4 : G + (2 * (pair x (dropTop (v + 1))).length + 5) ≤ W)
    (hW6 : G + (1 + 1 + (2 * (max (Hb + 2) (1 * (Hb + 3) + 1) + 1) + 1)) ≤ W)
    (hW8 : G + (3 * (max (1 + 1 + max (TM.binarySuccTime a) (TM.binarySuccTime r) + 5)
      (TM.binarySuccTime v) + 1) + 1) ≤ W)
    (hW9 : G + TM.binaryBumpTime (dropTop (v + 1)) ≤ W)
    (hW10 : G + ((scratchTargets k).length * (H + 4) + H * 4 + 8 + 1 +
      ((scratchTargets k).length * (H + 4) + 1)) ≤ W) :
    (bodyTM M).KeepsWindowOn
      (fun c => c.state = (bodyTM M).qstart ∧ c.input = I ∧
        c.work = enumBank k x N H v a r ∧ ∃ s : Γw, s ≠ Γw.one ∧ c.output = NTM.outSlot s)
      x.length W := by
  have hs : 1 ≤ W := by omega
  have hGW : G ≤ W := by omega
  have w1 := (blankSlot_keepsWindowOn k x N H v a r I hI hIhead G hG1).mono_space hW1
  have w2 := (emit_keepsWindowOn k x N H v a r I hI hIsi hIhead B G hB hG1).mono_space hW2
  have w3 := (parkPair_keepsWindowOn k x N H v a r I hIsi hIhead B G hB1 hGB).mono_space hW3
  have w4 := (copyPair_keepsWindowOn k x N H v a r I hI hIhead G hG1).mono_space hW4
  have w5 := matrix_keepsWindowOn M hdecS hne x N H v a r I hIsi hIhead W (by omega) (by omega)
  have w6 := (parkVerdict_keepsWindowOn k x N H v a r I hIsi hIhead Hb G (by omega) b hG1
    (by omega) hGpair).mono_space hW6
  have w7 := (publishVerdict_keepsWindowOn k x N H v a r I hI hIhead Hb G b hG1 hGHb
    hGpair).mono_space hW1
  have w8 := (tallyBump_keepsWindowOn k x N H v a r I hI hIz hIhead Hb G b hG1 hGHb
    hGpair).mono_space hW8
  have w9 := (witnessBump_keepsWindowOn k x N H v a r I hI hIhead Hb G b hG1 hGHb
    hGpair).mono_space hW9
  have w10 := (wipe_keepsWindowOn k x N H v a r I hI hIsi hIhead Hb G b hHbH hpairH hG1
    hGHb hGpair).mono_space hW10
  -- Stage 9 with the wipe.
  have c910 := TM.seqTM_keepsWindowOn (TM.binaryBumpTM (wIdx k))
    (TM.wipeRewindTM (scratchTargets k) (regIdx k)) hs
    (mid := midBumped k x N H v a r I Hb b)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (midBump_heads k x N H v a r I Hb G b hGHb hGpair hG1 _ _ _ hc.2)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.1]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (midBump_si k x N H v a r I Hb b _ _ _ hc.2)
        (by rw [hc.2.2.1]; exact TM.blankTape_startInvariant)⟩)
    w9
    (fun c hc => hoare_post_of (witnessBump_hoareTime k x N H v a r I hI Hb b) c hc.1 hc.2)
    w10
    (fun inp work out h => ⟨rfl,
      trans_of_parked_pred (P := midBumped k x N H v a r I Hb b)
        (by rw [h.1]; exact hI) (h.2.2.2.2.2.2.2.1)
        (by rw [h.2.1]; exact TM.blankTape_parked) h⟩)
  -- Stage 8.
  have c810 := TM.seqTM_keepsWindowOn (TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k))
    (TM.seqTM (TM.binaryBumpTM (wIdx k)) (TM.wipeRewindTM (scratchTargets k) (regIdx k))) hs
    (mid := midBump k x N H v a r I Hb b)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (midPublish_heads k x N H v a r I Hb G b hGHb hGpair _ _ _ hc.2)
        (by rw [hc.2.1, hIhead]) (by
          obtain ⟨-, ⟨sy, -, hsy⟩, -⟩ := hc.2
          rw [hsy]
          exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (midPublish_si k x N H v a r I Hb b _ _ _ hc.2)
        (by
          obtain ⟨-, ⟨sy, -, hsy⟩, -⟩ := hc.2
          rw [hsy]
          exact ⟨rfl, fun j hj => (NTM.outSlot_parked sy).2 j hj⟩)⟩)
    w8
    (fun c hc => hoare_post_of (tallyBump_hoareTime k x N H v a r I hI hIz Hb b) c hc.1 hc.2)
    c910
    (fun inp work out h => ⟨⟨(TM.binaryBumpTM (wIdx k)).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred (P := midBump k x N H v a r I Hb b)
        (by rw [h.1]; exact hI) (h.2.2.2.2.2.2.1)
        (by rw [h.2.1]; exact TM.blankTape_parked) h⟩, rfl⟩)
  -- Stage 7.
  have c710 := TM.seqTM_keepsWindowOn (TM.writeOutputBitTM (vIdx k)) _ hs
    (mid := midPublish k x N H v a r I Hb b)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (midParked_heads k x N H v a r I Hb G b hGHb hGpair _ _ _ hc.2)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.1]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (midParked_si k x N H v a r I Hb b _ _ _ hc.2)
        (by rw [hc.2.2.1]; exact TM.blankTape_startInvariant)⟩)
    w7
    (fun c hc => hoare_post_of (publishVerdict_hoareTime k x N H v a r I hI Hb b) c hc.1 hc.2)
    c810
    (fun inp work out h => ⟨⟨(TM.tallyBumpTM (cIdx k) (aIdx k) (rIdx k) (zIdx k)).qstart,
        TM.transitionInput inp, fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred (P := midPublish k x N H v a r I Hb b)
        (by rw [h.1]; exact hI) h.2.2.2.1
        (by
          obtain ⟨-, ⟨sy, -, hsy⟩, -⟩ := h
          rw [hsy]
          exact NTM.outSlot_parked sy) h⟩, rfl⟩)
  -- Stage 6.
  have c610 := TM.seqTM_keepsWindowOn (TM.parkRewindTM [vIdx k]) _ hs
    (mid := midParked k x N H v a r I Hb b)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (midMatrix_heads k x N H v a r I Hb G b (by omega) hGpair _ _ _ hc.2)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.1]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (midMatrix_si k x N H v a r I Hb b _ _ _ hc.2)
        (by rw [hc.2.2.1]; exact TM.blankTape_startInvariant)⟩)
    w6
    (fun c hc => hoare_post_of (parkVerdict_hoareTime k x N H v a r I hIsi hIhead Hb hHb1 b) c
      hc.1 hc.2)
    c710
    (fun inp work out h => ⟨⟨(TM.writeOutputBitTM (vIdx k)).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred (P := midParked k x N H v a r I Hb b)
        (by rw [h.1]; exact hI) h.2.2.2.2.1
        (by rw [h.2.1]; exact TM.blankTape_parked) h⟩, rfl⟩)
  -- Stage 5: the matrix machine.
  have c510 := TM.seqTM_keepsWindowOn (matrixTM M) _ hs
    (mid := midMatrix k x N H v a r I Hb b)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (fun i => by rw [hc.2.2.1]; exact afterCopy_head_le k x N H v a r G hGpair i)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.2]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (fun i => by rw [hc.2.2.1]; exact afterCopy_startInvariant k x N H v a r i)
        (by rw [hc.2.2.2]; exact TM.blankTape_startInvariant)⟩)
    w5
    (fun c hc => hoare_post_of
      (matrix_hoareTime_bool M hdec hdecS x N H v a r I hI hIsi Hb hHS b hb) c hc.1
      ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩)
    c610
    (fun inp work out h => ⟨⟨(TM.parkRewindTM [vIdx k]).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, midMatrix_trans k x N H v a r I hI Hb (by omega) b inp work out h⟩, rfl⟩)
  -- Stage 4.
  have c410 := TM.seqTM_keepsWindowOn (copyPairTM k) _ hs
    (mid := fun inp work out => inp = I ∧ work = afterCopy k x N H v a r ∧
      out = TM.blankTape)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (fun i => by rw [hc.2.2.1, afterPair_head]; omega)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.2]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (fun i => by rw [hc.2.2.1]; exact afterPair_startInvariant k x N H v a r i)
        (by rw [hc.2.2.2]; exact TM.blankTape_startInvariant)⟩)
    w4
    (fun c hc => hoare_post_of (copyPair_hoareTime k x N H v a r I hI) c hc.1
      ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩)
    c510
    (fun inp work out h => ⟨⟨(matrixTM M).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred
        (P := fun inp work out => inp = I ∧ work = afterCopy k x N H v a r ∧
          out = TM.blankTape) (by rw [h.1]; exact hI)
        (fun i => by rw [h.2.1]; exact afterCopy_parked k x N H v a r i)
        (by rw [h.2.2]; exact TM.blankTape_parked) h⟩, rfl⟩)
  -- Stage 3.
  have c310 := TM.seqTM_keepsWindowOn (TM.parkRewindTM [xIdx k, wIdx k, y1Idx k]) _ hs
    (mid := fun inp work out => inp = I ∧ work = afterPair k x N H v a r ∧
      out = TM.blankTape)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (fun i => le_trans (hc.2.2.2.2.2.2.2.2 i) hGB)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.1]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi) hc.2.2.2.2.2.2.2.1
        (by rw [hc.2.2.1]; exact TM.blankTape_startInvariant)⟩)
    w3
    (fun c hc => hoare_post_of (parkPair_hoareTime k x N H v a r I hIsi hIhead B hB1) c hc.1
      hc.2)
    c410
    (fun inp work out h => ⟨⟨(copyPairTM k).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred
        (P := fun inp work out => inp = I ∧ work = afterPair k x N H v a r ∧
          out = TM.blankTape) (by rw [h.1]; exact hI)
        (fun i => by rw [h.2.1]; exact afterPair_parked k x N H v a r i)
        (by rw [h.2.2]; exact TM.blankTape_parked) h⟩, rfl⟩)
  -- Stage 2.
  have c210 := TM.seqTM_keepsWindowOn (emitTM k) _ hs
    (mid := midEmit k x N H v a r I B)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (fun i => by rw [hc.2.2.1]; exact enumBank_head_le k x N H v a r G hG1 i)
        (by rw [hc.2.1, hIhead]) (by rw [hc.2.2.2]; exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (fun i => by rw [hc.2.2.1]; exact enumBank_startInvariant k x N H v a r i)
        (by rw [hc.2.2.2]; exact TM.blankTape_startInvariant)⟩)
    w2
    (fun c hc => hoare_post_of (emit_hoareTime k x N H v a r I hI hIsi B hB) c hc.1
      ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩)
    c310
    (fun inp work out h => ⟨⟨(TM.parkRewindTM [xIdx k, wIdx k, y1Idx k]).qstart,
        TM.transitionInput inp, fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, midEmit_trans k x N H v a r I hI B (by omega) inp work out h⟩, rfl⟩)
  -- Stage 1.
  have c110 := TM.seqTM_keepsWindowOn (TM.writeOutputBitTM (zIdx k)) _ hs
    (mid := fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧
      out = TM.blankTape)
    (fun c hc => ⟨hc.1,
      windowed_of_heads c x.length G W hGW
        (fun i => by rw [hc.2.2.1]; exact enumBank_head_le k x N H v a r G hG1 i)
        (by rw [hc.2.1, hIhead]) (by
          obtain ⟨-, -, -, sy, -, hsy⟩ := hc
          rw [hsy]
          exact le_of_eq rfl) hs,
      cfgStartInvariant_of c (by rw [hc.2.1]; exact hIsi)
        (fun i => by rw [hc.2.2.1]; exact enumBank_startInvariant k x N H v a r i)
        (by
          obtain ⟨-, -, -, sy, -, hsy⟩ := hc
          rw [hsy]
          exact ⟨rfl, fun j hj => (NTM.outSlot_parked sy).2 j hj⟩)⟩)
    w1
    (fun c hc => hoare_post_of (blankSlot_hoareTime k x N H v a r I hI) c hc.1
      ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩)
    c210
    (fun inp work out h => ⟨⟨(emitTM k).qstart, TM.transitionInput inp,
        fun i => TM.transitionTape (work i), TM.transitionTape out⟩,
      ⟨rfl, trans_of_parked_pred
        (P := fun inp work out => inp = I ∧ work = enumBank k x N H v a r ∧
          out = TM.blankTape) (by rw [h.1]; exact hI)
        (fun i => by rw [h.2.1]; exact enumBank_parked k x N H v a r i)
        (by rw [h.2.2]; exact TM.blankTape_parked) h⟩, rfl⟩)
  intro c hc D hD
  exact c110 c ⟨⟨(TM.writeOutputBitTM (zIdx k)).qstart, c.input, c.work, c.output⟩,
    ⟨rfl, hc.2.1, hc.2.2.1, hc.2.2.2⟩, Cfg.ext hc.1 rfl rfl rfl⟩ D hD

end PolyExists

end Complexity
