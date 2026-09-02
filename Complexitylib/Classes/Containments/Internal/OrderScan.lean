/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ConstScan

/-!
# Comparing two register tuples

⚠️ Unreviewed by Bolton

Inductive counting guesses the members of a round one at a time and needs them to be *distinct*.
The cheapest way to force that is to demand they arrive in increasing order, which needs a strict
total order on register tuples that a single scan can decide.

The order is the one a scan computes for free: read the cells in scan order, and let the **last**
disagreement decide. That is `Complexity.lastLt` on the list of bits a scan reads, and
`Complexity.Scanner.tupleLt` is the scanner that computes it — one state bit, updated whenever a
column disagrees.

Because the order is a strict order (`Complexity.lastLt_irrefl`, `Complexity.lastLt_trans`) and
separates distinct patterns (`Complexity.lastLt_total`), a guessed increasing sequence is a
sequence of distinct patterns.

## Main definitions

- `lastLt` — the order on bit lists the last disagreement decides
- `scanKey` — the bits a scan reads off a tuple, in scan order
- `Scanner.tupleLt` — the scanner that decides it

## Main results

- `lastLt_irrefl`, `lastLt_trans`, `lastLt_total`
- `Scanner.tupleLt_run` — the scan decides the order on the tuples' keys
-/

@[expose] public section

namespace Complexity

/-! ## The order the last disagreement decides -/

/-- **The order a scan decides**: run through the two lists in order, remembering the verdict of
the most recent disagreement. -/
def lastLt (as bs : List Bool) : Bool :=
  (as.zip bs).foldl (fun s ab => if ab.1 = ab.2 then s else ab.2) false

theorem lastLt_nil (bs : List Bool) : lastLt [] bs = false := by
  rw [lastLt]
  simp

/-- **Reading a whole block more.** -/
theorem lastLt_append (as bs xs ys : List Bool) (h : as.length = bs.length) :
    lastLt (as ++ xs) (bs ++ ys)
      = (xs.zip ys).foldl (fun s ab => if ab.1 = ab.2 then s else ab.2) (lastLt as bs) := by
  rw [lastLt, lastLt, List.zip_append h, List.foldl_append]

/-- **Reading one more pair.** -/
theorem lastLt_concat (as bs : List Bool) (a b : Bool) (h : as.length = bs.length) :
    lastLt (as ++ [a]) (bs ++ [b]) = if a = b then lastLt as bs else b := by
  rw [lastLt, lastLt, List.zip_append h]
  rw [List.foldl_append]
  rfl

/-- Nothing is below itself. -/
theorem lastLt_irrefl (as : List Bool) : lastLt as as = false := by
  rw [lastLt]
  have h : ∀ (l : List Bool) (s : Bool),
      (l.zip l).foldl (fun s ab => if ab.1 = ab.2 then s else ab.2) s = s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons a l ih =>
      intro s
      show (List.zip (a :: l) (a :: l)).foldl _ s = s
      rw [List.zip_cons_cons, List.foldl_cons, if_pos rfl, ih]
  exact h as false

private theorem eq_concat_of_length_eq {as bs : List Bool} (a : Bool)
    (h : (as ++ [a]).length = bs.length) : ∃ (bs' : List Bool) (b : Bool), bs = bs' ++ [b] := by
  rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
  · simp at h
  · exact ⟨bs', b, by simp⟩

/-- The order is transitive. -/
theorem lastLt_trans : ∀ (as bs cs : List Bool), as.length = bs.length →
    bs.length = cs.length → lastLt as bs = true → lastLt bs cs = true →
    lastLt as cs = true := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro bs cs _ _ h _
    rw [lastLt_nil] at h
    exact absurd h (by simp)
  | append_singleton as a ih =>
    intro bs cs hab hbc h1 h2
    obtain ⟨bs', b, rfl⟩ := eq_concat_of_length_eq a hab
    obtain ⟨cs', c, rfl⟩ := eq_concat_of_length_eq b hbc
    have hab' : as.length = bs'.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hab
      omega
    have hbc' : bs'.length = cs'.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hbc
      omega
    rw [lastLt_concat as bs' a b hab'] at h1
    rw [lastLt_concat bs' cs' b c hbc'] at h2
    rw [lastLt_concat as cs' a c (hab'.trans hbc')]
    have hih := ih bs' cs' hab' hbc'
    cases a <;> cases b <;> cases c <;> simp_all

/-- Distinct patterns of the same shape are comparable. -/
theorem lastLt_total : ∀ (as bs : List Bool), as.length = bs.length →
    lastLt as bs = false → lastLt bs as = false → as = bs := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
    intro bs h _ _
    exact (List.eq_nil_of_length_eq_zero h.symm).symm
  | append_singleton as a ih =>
    intro bs hlen h1 h2
    obtain ⟨bs', b, rfl⟩ := eq_concat_of_length_eq a hlen
    have hlen' : as.length = bs'.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rw [lastLt_concat as bs' a b hlen'] at h1
    rw [lastLt_concat bs' as b a hlen'.symm] at h2
    have hih := ih bs' hlen'
    cases a <;> cases b <;> simp_all

/-! ## The key a scan reads off a tuple -/

/-- The bits one column contributes: the blocks still running, in register order. -/
def colKey {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A : ℕ → Fin (jj + 1)) (m : ℕ)
    (len : ℕ → ℕ) (q : ℕ) : List Bool :=
  (List.range m).filterMap
    (fun p => if q ≤ len p then some (Scanner.bitAt cols (A p) q) else none)

/-- **The bits a scan of `N` columns reads off a tuple**, in the order it reads them. -/
def scanKey {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A : ℕ → Fin (jj + 1)) (m : ℕ)
    (len : ℕ → ℕ) : ℕ → List Bool
  | 0 => []
  | N + 1 => scanKey cols A m len N ++ colKey cols A m len (N + 1)

/-- **One more block's contribution to a column.** -/
theorem colKey_succ {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (q : ℕ) :
    colKey cols A (m + 1) len q
      = colKey cols A m len q ++ (if q ≤ len m then [Scanner.bitAt cols (A m) q] else []) := by
  rw [colKey, colKey, List.range_succ, List.filterMap_append]
  congr 1
  by_cases h : q ≤ len m <;> simp [h]

/-- A column contributes as many bits as it has blocks running, whatever the tuple. -/
theorem colKey_length {jj : ℕ} (cols cols' : ℕ → Fin (jj + 1) → Γ) (A B : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (q : ℕ) :
    (colKey cols A m len q).length = (colKey cols' B m len q).length := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [colKey_succ, colKey_succ, List.length_append, List.length_append, ih]
    by_cases h : q ≤ len m
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]

/-- And so a key's length does not depend on the tuple. -/
theorem scanKey_length {jj : ℕ} (cols cols' : ℕ → Fin (jj + 1) → Γ) (A B : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (N : ℕ) :
    (scanKey cols A m len N).length = (scanKey cols' B m len N).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [scanKey, scanKey, List.length_append, List.length_append, ih,
      colKey_length cols cols' A B m len (N + 1)]

/-- **Tuples that hold the same bits have the same key.** -/
theorem scanKey_congr {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A B : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (N : ℕ)
    (h : ∀ p, p < m → ∀ q, 1 ≤ q → q ≤ len p →
      Scanner.bitAt cols (A p) q = Scanner.bitAt cols (B p) q) :
    scanKey cols A m len N = scanKey cols B m len N := by
  have hcol : ∀ q, 1 ≤ q → colKey cols A m len q = colKey cols B m len q := by
    intro q hq
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [colKey_succ, colKey_succ, ih (fun p hp => h p (by omega))]
      by_cases hlt : q ≤ len m
      · rw [if_pos hlt, if_pos hlt, h m (by omega) q hq hlt]
      · rw [if_neg hlt, if_neg hlt]
  induction N with
  | zero => rfl
  | succ N ih => rw [scanKey, scanKey, ih, hcol (N + 1) (by omega)]

private theorem foldl_range_congr {α : Type} (f g : α → ℕ → α) :
    ∀ (m : ℕ), (∀ p, p < m → ∀ a, f a p = g a p) → ∀ s : α,
      (List.range m).foldl f s = (List.range m).foldl g s := by
  intro m
  induction m with
  | zero => intro _ s; rfl
  | succ m ih =>
    intro h s
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun p hp a => h p (by omega) a) s]
    show f _ m = g _ m
    rw [h m (by omega)]

/-- **Tuples holding the same bits have the same key.** Two register tuples the scan reports as
*ordered* therefore hold different bits — which is how a guessed increasing sequence is a sequence
of distinct patterns. -/
theorem scanKey_congr_blocks {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A B : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (N : ℕ) (bits : ℕ → List Bool)
    (hA : ∀ p, p < m → HoldsBits cols 0 (A p) (bits p))
    (hB : ∀ p, p < m → HoldsBits cols 0 (B p) (bits p))
    (hlen : ∀ p, p < m → len p ≤ (bits p).length) :
    scanKey cols A m len N = scanKey cols B m len N := by
  refine scanKey_congr cols A B m len N (fun p hp q hq hql => ?_)
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hq' : q' < (bits p).length := by have := hlen p hp; omega
  have hAq := hA p hp q' hq'
  have hBq := hB p hp q' hq'
  rw [Nat.zero_add] at hAq hBq
  rw [Scanner.bitAt, Scanner.bitAt, hAq, hBq]

/-! ## The scanner -/

namespace Scanner

/-- **Compare two register tuples**, letting the last disagreement decide. -/
def tupleLt (jj m mx : ℕ) (A B : ℕ → Fin (jj + 1)) (len : ℕ → ℕ) : Scanner jj :=
  ofRight (Fin (mx + 1) × Bool) (⟨0, Nat.zero_lt_succ _⟩, false)
    (fun s col =>
      (⟨min (s.1.val + 1) mx, by omega⟩,
        (List.range m).foldl (fun t p =>
          if s.1.val + 1 ≤ len p then
            (if decide (col (A p) = Γ.one) = decide (col (B p) = Γ.one) then t
              else decide (col (B p) = Γ.one))
          else t) s.2))
    Prod.snd

theorem rightOnly_tupleLt (jj m mx : ℕ) (A B : ℕ → Fin (jj + 1)) (len : ℕ → ℕ) :
    RightOnly (tupleLt jj m mx A B len) :=
  rightOnly_ofRight _ _ _ _

/-- **One column's worth of the order**, whichever way it is computed. -/
theorem foldl_colKey {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (A B : ℕ → Fin (jj + 1))
    (m : ℕ) (len : ℕ → ℕ) (q : ℕ) (s : Bool) :
    ((colKey cols A m len q).zip (colKey cols B m len q)).foldl
        (fun s ab => if ab.1 = ab.2 then s else ab.2) s
      = (List.range m).foldl (fun t p =>
          if q ≤ len p then
            (if bitAt cols (A p) q = bitAt cols (B p) q then t else bitAt cols (B p) q)
          else t) s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    rw [colKey_succ, colKey_succ, List.zip_append (colKey_length cols cols A B m len q),
      List.foldl_append, ih s, List.range_succ, List.foldl_append]
    by_cases hlt : q ≤ len m
    · rw [if_pos hlt, if_pos hlt]
      simp [hlt]
    · rw [if_neg hlt, if_neg hlt]
      simp [hlt]

/-- **What the comparison knows after `N` columns.** -/
theorem tupleLt_runR {jj : ℕ} (m mx : ℕ) (A B : ℕ → Fin (jj + 1)) (len : ℕ → ℕ)
    (hlen : ∀ p, p < m → len p ≤ mx) (cols : ℕ → Fin (jj + 1) → Γ) :
    ∀ N : ℕ, ((tupleLt jj m mx A B len).runR cols N).1.val = min N mx ∧
      ((tupleLt jj m mx A B len).runR cols N).2
        = lastLt (scanKey cols A m len N) (scanKey cols B m len N) := by
  intro N
  induction N with
  | zero => exact ⟨by simp [runR, tupleLt, ofRight], rfl⟩
  | succ N ih =>
    obtain ⟨hpos, hval⟩ := ih
    refine ⟨?_, ?_⟩
    · show min (((tupleLt jj m mx A B len).runR cols N).1.val + 1) mx = min (N + 1) mx
      rw [hpos]
      omega
    show (List.range m).foldl (fun t p =>
        if ((tupleLt jj m mx A B len).runR cols N).1.val + 1 ≤ len p then
          (if decide (cols (N + 1) (A p) = Γ.one) = decide (cols (N + 1) (B p) = Γ.one) then t
            else decide (cols (N + 1) (B p) = Γ.one))
        else t) ((tupleLt jj m mx A B len).runR cols N).2 = _
    rw [hpos, hval, scanKey, scanKey,
      lastLt_append _ _ _ _ (scanKey_length cols cols A B m len N),
      foldl_colKey cols A B m len (N + 1)]
    refine foldl_range_congr _ _ m (fun p hp a => ?_) _
    by_cases hsat : N + 1 ≤ mx
    · rw [show min N mx + 1 = N + 1 by omega]
      rfl
    · rw [if_neg (by have := hlen p hp; omega), if_neg (by have := hlen p hp; omega)]

/-- **The comparison decides the order on the two tuples' keys.** -/
theorem tupleLt_run {jj : ℕ} (m mx : ℕ) (A B : ℕ → Fin (jj + 1)) (len : ℕ → ℕ)
    (hlen : ∀ p, p < m → len p ≤ mx) (cols : ℕ → Fin (jj + 1) → Γ) (N : ℕ) :
    (tupleLt jj m mx A B len).emit ((tupleLt jj m mx A B len).run cols N)
      = lastLt (scanKey cols A m len N) (scanKey cols B m len N) := by
  rw [run, runL_of_rightOnly (rightOnly_tupleLt jj m mx A B len)]
  exact (tupleLt_runR m mx A B len hlen cols N).2

end Scanner

end Complexity
