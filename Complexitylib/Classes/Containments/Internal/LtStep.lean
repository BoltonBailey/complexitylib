/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FamStep
public import Complexitylib.Classes.Containments.Internal.OrderScan

/-!
# Ordering and copying code tuples

⚠️ Unreviewed by Bolton

Inductive counting guesses the members of a round one at a time, and needs them distinct. The
stage that forces it is `Complexity.TM.guessCheckTM` run with `Complexity.ltScanner`: the
tuple the loop guessed last must come *below* the one it has now, in the order the scan computes
(`Complexity.lastLt`). Since that order is strict, the codes the loop meets are all different.

The same stage shape, run with `Complexity.eqScanner`, is how the loop remembers the tuple it has
just checked: guess the spare family, and check it agrees cell by cell with the family the walk
left its answer in — a copy, without a copying machine.

## Main definitions

- `ltScanner` — the check that one tuple is below another

## Main results

- `ltScanner_run` — what it decides
- `ne_of_lastLt` — tuples the order separates hold different codes
- `eqScanner_of_agree` — the equality check accepts when the tuples do agree
-/

@[expose] public section

namespace Complexity

variable {kk jj : ℕ} {tm : NTM kk}

/-- **The check that tuple `cP` is below tuple `cA`** in the order a scan computes. -/
noncomputable def ltScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (cP cA : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.tupleLt jj (kk + 3) (walkScanLen tm nn S) cP cA (blockLen tm nn S)

/-- **What it decides**: the order on the two tuples' keys. -/
theorem ltScanner_run {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (cP cA : ℕ → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) :
    (ltScanner tm nn S cP cA).emit
        ((ltScanner tm nn S cP cA).run cols (walkScanLen tm nn S))
      = lastLt (scanKey cols cP (kk + 3) (blockLen tm nn S) (walkScanLen tm nn S))
          (scanKey cols cA (kk + 3) (blockLen tm nn S) (walkScanLen tm nn S)) :=
  Scanner.tupleLt_run (kk + 3) (walkScanLen tm nn S) cP cA (blockLen tm nn S)
    (fun p _ => blockLen_le tm nn S p) cols (walkScanLen tm nn S)

/-- **Tuples the order separates hold different codes.** This is what makes a guessed increasing
sequence a sequence of distinct codes. -/
theorem ne_of_lastLt {S : ℕ} (x : List Bool) (cols : ℕ → Fin (jj + 1) → Γ)
    (cP cA : ℕ → Fin (jj + 1)) (a b : Code tm.Q kk x.length S)
    (hP : ∀ p, p < kk + 3 → HoldsBits cols 0 (cP p) (codeBlockScan tm x S a p))
    (hA : ∀ p, p < kk + 3 → HoldsBits cols 0 (cA p) (codeBlockScan tm x S b p))
    (hlt : lastLt
        (scanKey cols cP (kk + 3) (blockLen tm x.length S) (walkScanLen tm x.length S))
        (scanKey cols cA (kk + 3) (blockLen tm x.length S) (walkScanLen tm x.length S))
      = true) : a ≠ b := by
  rintro rfl
  rw [scanKey_congr_blocks cols cP cA (kk + 3) (blockLen tm x.length S)
      (walkScanLen tm x.length S) (codeBlockScan tm x S a) hP hA
      (fun p _ => le_of_eq (codeBlockScan_length tm x S a p).symm),
    lastLt_irrefl] at hlt
  exact Bool.noConfusion hlt

/-- **The equality check accepts when the tuples do agree.** The converse of
`Complexity.eqScanner_agree`, which is what the guess that copies a tuple needs. -/
theorem eqScanner_of_agree {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j j' : ℕ → Fin (jj + 1))
    (h : ∀ p, p < kk + 3 → ∀ q, 1 ≤ q → q ≤ blockLen tm nn S p → cols q (j p) = cols q (j' p)) :
    (eqScanner tm nn S j j').emit
      ((eqScanner tm nn S j j').run cols (walkScanLen tm nn S)) = true := by
  rw [eqScanner, Scanner.all_emit_run]
  intro p
  rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj (j p.val) (j' p.val)) _ _
    (blockLen_le tm nn S p.val)]
  show (Scanner.eq jj (j p.val) (j' p.val)).run cols (blockLen tm nn S p.val) = true
  exact (Scanner.eq_run jj (j p.val) (j' p.val) cols (blockLen tm nn S p.val)).mpr
    (fun q h1 h2 => h p.val p.isLt q h1 h2)

/-! ## The order, read on codes

A loop invariant cannot mention the cells of a scan, because they change with every stage. What
it can mention is the key of a *code* — the bits a tuple holding it would show — which is what the
scan's comparison is really about. -/

private theorem filterMap_range_congr {α : Type} (P : ℕ → Prop) [DecidablePred P]
    (f g : ℕ → α) : ∀ (m : ℕ), (∀ p, p < m → P p → f p = g p) →
      (List.range m).filterMap (fun p => if P p then some (f p) else none)
        = (List.range m).filterMap (fun p => if P p then some (g p) else none) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [List.range_succ, List.filterMap_append, List.filterMap_append,
      ih (fun p hp => h p (by omega))]
    by_cases hP : P m
    · rw [show (List.filterMap (fun p => if P p then some (f p) else none) [m]) = [f m] by
        simp [hP],
        show (List.filterMap (fun p => if P p then some (g p) else none) [m]) = [g m] by
        simp [hP], h m (by omega) hP]
    · rw [show (List.filterMap (fun p => if P p then some (f p) else none) [m]) = [] by simp [hP],
        show (List.filterMap (fun p => if P p then some (g p) else none) [m]) = [] by simp [hP]]

/-- The bits one column of a tuple holding `a` would show. -/
noncomputable def codeColKey {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (q : ℕ) : List Bool :=
  (List.range (kk + 3)).filterMap (fun p =>
    if q ≤ blockLen tm x.length S p then some ((codeBlockScan tm x S a p).getD (q - 1) false)
    else none)

/-- **A code's key**: the bits a scan of `N` columns would read off a tuple holding it. -/
noncomputable def codeKey {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) : ℕ → List Bool
  | 0 => []
  | N + 1 => codeKey tm x S a N ++ codeColKey tm x S a (N + 1)

/-- **A tuple holding a code shows that code's key.** -/
theorem scanKey_eq_codeKey {kk jj : ℕ} {tm : NTM kk} {S : ℕ} (x : List Bool)
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (N : ℕ)
    (h : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p)) :
    scanKey cols j (kk + 3) (blockLen tm x.length S) N = codeKey tm x S a N := by
  have hcol : ∀ q, 1 ≤ q →
      colKey cols j (kk + 3) (blockLen tm x.length S) q = codeColKey tm x S a q := by
    intro q hq
    refine filterMap_range_congr (fun p => q ≤ blockLen tm x.length S p) _ _ (kk + 3)
      (fun p hp hle => ?_)
    have hlen : (codeBlockScan tm x S a p).length = blockLen tm x.length S p :=
      codeBlockScan_length tm x S a p
    have hq' : q - 1 < (codeBlockScan tm x S a p).length := by omega
    have hc := h p hp (q - 1) hq'
    rw [show 0 + (q - 1) + 1 = q by omega] at hc
    rw [Scanner.bitAt, hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']
    cases (codeBlockScan tm x S a p)[q - 1] <;> rfl
  induction N with
  | zero => rfl
  | succ N ih => rw [scanKey, codeKey, ih, hcol (N + 1) (by omega)]

/-- **The order on codes** the machine's comparison decides. -/
noncomputable def codeLt {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a b : Code tm.Q kk x.length S) : Prop :=
  lastLt (codeKey tm x S a (walkScanLen tm x.length S))
    (codeKey tm x S b (walkScanLen tm x.length S)) = true

/-- It is irreflexive. -/
theorem codeLt_irrefl {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    (a : Code tm.Q kk x.length S) : ¬ codeLt tm x S a a := by
  rw [codeLt, lastLt_irrefl]
  exact fun h => Bool.noConfusion h

private theorem filterMap_range_length_congr {α β : Type} (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → α) (g : ℕ → β) : ∀ m : ℕ,
      ((List.range m).filterMap (fun p => if P p then some (f p) else none)).length
        = ((List.range m).filterMap (fun p => if P p then some (g p) else none)).length := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append, List.length_append,
      List.length_append, ih]
    by_cases hP : P m
    · rw [show (List.filterMap (fun p => if P p then some (f p) else none) [m]) = [f m] by
        simp [hP], show (List.filterMap (fun p => if P p then some (g p) else none) [m])
        = [g m] by simp [hP]]
      rfl
    · rw [show (List.filterMap (fun p => if P p then some (f p) else none) [m]) = [] by simp [hP],
        show (List.filterMap (fun p => if P p then some (g p) else none) [m]) = [] by simp [hP]]
      rfl

/-- A column of a key has a length that does not depend on the code. -/
theorem codeColKey_length {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    (a b : Code tm.Q kk x.length S) (q : ℕ) :
    (codeColKey tm x S a q).length = (codeColKey tm x S b q).length :=
  filterMap_range_length_congr (fun p => q ≤ blockLen tm x.length S p) _ _ (kk + 3)

/-- A code's key has a length that does not depend on the code. -/
theorem codeKey_length {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    (a b : Code tm.Q kk x.length S) (N : ℕ) :
    (codeKey tm x S a N).length = (codeKey tm x S b N).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [codeKey, codeKey, List.length_append, List.length_append, ih,
      codeColKey_length a b (N + 1)]

/-- And it is transitive. -/
theorem codeLt_trans {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    {a b c : Code tm.Q kk x.length S} (hab : codeLt tm x S a b) (hbc : codeLt tm x S b c) :
    codeLt tm x S a c :=
  lastLt_trans _ _ _ (codeKey_length a b _) (codeKey_length b c _) hab hbc

/-- **Codes the order separates are different.** -/
theorem ne_of_codeLt {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    {a b : Code tm.Q kk x.length S} (h : codeLt tm x S a b) : a ≠ b := by
  rintro rfl
  exact codeLt_irrefl a h

/-- **An accepting comparison orders the two codes.** -/
theorem codeLt_of_ltScanner {S : ℕ} (x : List Bool) (cols : ℕ → Fin (jj + 1) → Γ)
    (cP cA : ℕ → Fin (jj + 1)) (p v : Code tm.Q kk x.length S)
    (hP : ∀ q, q < kk + 3 → HoldsBits cols 0 (cP q) (codeBlockScan tm x S p q))
    (hA : ∀ q, q < kk + 3 → HoldsBits cols 0 (cA q) (codeBlockScan tm x S v q))
    (hv : (ltScanner tm x.length S cP cA).emit
      ((ltScanner tm x.length S cP cA).run cols (walkScanLen tm x.length S)) = true) :
    codeLt tm x S p v := by
  rw [ltScanner_run, scanKey_eq_codeKey x cols cP p _ hP,
    scanKey_eq_codeKey x cols cA v _ hA] at hv
  exact hv

/-- **And an ordered pair of codes is accepted**, so an honest guess passes. -/
theorem ltScanner_of_codeLt {S : ℕ} (x : List Bool) (cols : ℕ → Fin (jj + 1) → Γ)
    (cP cA : ℕ → Fin (jj + 1)) (p v : Code tm.Q kk x.length S)
    (hP : ∀ q, q < kk + 3 → HoldsBits cols 0 (cP q) (codeBlockScan tm x S p q))
    (hA : ∀ q, q < kk + 3 → HoldsBits cols 0 (cA q) (codeBlockScan tm x S v q))
    (hlt : codeLt tm x S p v) :
    (ltScanner tm x.length S cP cA).emit
      ((ltScanner tm x.length S cP cA).run cols (walkScanLen tm x.length S)) = true := by
  rw [ltScanner_run, scanKey_eq_codeKey x cols cP p _ hP, scanKey_eq_codeKey x cols cA v _ hA]
  exact hlt

/-- **The negation of a check.** -/
def Scanner.not {j : ℕ} (S : Scanner j) : Scanner j where
  σ := S.σ
  decEqσ := S.decEqσ
  finσ := S.finσ
  start := S.start
  stepR := S.stepR
  stepL := S.stepL
  emit s := !S.emit s

theorem Scanner.not_runR {j : ℕ} (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p, (Scanner.not S).runR cols p = S.runR cols p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih => rw [Scanner.runR, Scanner.runR, ih]; rfl

theorem Scanner.not_runL {j : ℕ} (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p (s : S.σ), (Scanner.not S).runL cols p s = S.runL cols p s := by
  intro p
  induction p with
  | zero => exact fun _ => rfl
  | succ p ih => exact fun s => by rw [Scanner.runL, Scanner.runL, ih]; rfl

/-- **What it decides**: the opposite of what the check decides. -/
theorem Scanner.not_run {j : ℕ} (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ) :
    (Scanner.not S).emit ((Scanner.not S).run cols len) = !S.emit (S.run cols len) := by
  have h : (Scanner.not S).run cols len = S.run cols len := by
    rw [Scanner.run, Scanner.run, Scanner.not_runL, Scanner.not_runR]
  rw [h]
  rfl

/-- **Tuples an inequality check separates hold different codes.** This is the shape of a
certificate that a code is not among a round's successors. -/
theorem ne_of_notEqScanner {S : ℕ} (x : List Bool) (cols : ℕ → Fin (jj + 1) → Γ)
    (j j' : ℕ → Fin (jj + 1)) (a b : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hv : (Scanner.not (eqScanner tm x.length S j j')).emit
      ((Scanner.not (eqScanner tm x.length S j j')).run cols (walkScanLen tm x.length S))
      = true) : a ≠ b := by
  rintro rfl
  have heq : (eqScanner tm x.length S j j').emit
      ((eqScanner tm x.length S j j').run cols (walkScanLen tm x.length S)) = true := by
    refine eqScanner_of_agree tm x.length S cols j j' (fun p hp q hq hql => ?_)
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hq' : q' < (codeBlockScan tm x S a p).length := by
      rw [codeBlockScan_length tm x S a p]
      omega
    have h1 := ha p hp q' hq'
    have h2 := hb p hp q' hq'
    rw [Nat.zero_add] at h1 h2
    rw [h1, h2]
  rw [Scanner.not_run, heq] at hv
  exact Bool.noConfusion hv

end Complexity
