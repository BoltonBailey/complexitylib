/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FPBridge
public import Complexitylib.Classes.P.Cobham.Internal

/-!
# Indexed folds in the polynomial-time algebra

⚠️ Unreviewed by Bolton

A polynomial-time loop `for i < n: acc := F (acc, x, i)` with the index handed to the body in
unary. `foldLoop` runs it by iterating a packed step (`Cobham.iterate_mem_FP`), and
`foldLoopFn_mem_FP` says it is polynomial-time whenever the body is and keeps the accumulator
within a polynomial width. This is the loop shape of every arithmetic verifier: a product over
clauses, a product over literals, a Horner scheme.

## Main definitions

- `foldIdx` — the loop, as a recursion
- `foldLoop` — the loop, as an iterated packed step

## Main results

- `foldLoop_eq` — the packed loop is the recursion
- `foldLoopFn_mem_FP` — it is polynomial-time
-/

@[expose] public section

namespace Complexity

/-- The loop as a recursion: `n` steps from index `i`, the body reading
`pair acc (pair x (unary index))`. -/
def foldIdx (F : List Bool → List Bool) (x : List Bool) : List Bool → ℕ → ℕ → List Bool
  | acc, _, 0 => acc
  | acc, i, n + 1 => foldIdx F x (F (pair acc (pair x (List.replicate i true)))) (i + 1) n

@[simp] theorem foldIdx_zero (F : List Bool → List Bool) (x acc : List Bool) (i : ℕ) :
    foldIdx F x acc i 0 = acc := rfl

theorem foldIdx_succ (F : List Bool → List Bool) (x acc : List Bool) (i n : ℕ) :
    foldIdx F x acc i (n + 1)
      = foldIdx F x (F (pair acc (pair x (List.replicate i true)))) (i + 1) n := rfl

/-- The packed step on `pair acc (pair x (unary i))`. -/
def loopStep (F : List Bool → List Bool) (s : List Bool) : List Bool :=
  pair (F (pair (pairFst s) (pair (pairFst (pairSnd s)) (pairSnd (pairSnd s)))))
    (pair (pairFst (pairSnd s)) (true :: pairSnd (pairSnd s)))

theorem loopStep_iterate (F : List Bool → List Bool) (x : List Bool) :
    ∀ (n : ℕ) (acc : List Bool) (i : ℕ),
      (loopStep F)^[n] (pair acc (pair x (List.replicate i true)))
        = pair (foldIdx F x acc i n) (pair x (List.replicate (i + n) true))
  | 0, acc, i => by simp
  | n + 1, acc, i => by
      rw [Function.iterate_succ_apply, loopStep]
      simp only [pairFst_pair, pairSnd_pair]
      rw [← List.replicate_succ, loopStep_iterate F x n _ (i + 1), foldIdx_succ,
        show i + 1 + n = i + (n + 1) by omega]

/-- The loop: `|len|` steps from index `0` and accumulator `init`. -/
def foldLoop (F : List Bool → List Bool) (init x len : List Bool) : List Bool :=
  pairFst ((loopStep F)^[len.length] (pair init (pair x [])))

/-- **The packed loop is the recursion.** -/
theorem foldLoop_eq (F : List Bool → List Bool) (init x len : List Bool) :
    foldLoop F init x len = foldIdx F x init 0 len.length := by
  rw [foldLoop, show ([] : List Bool) = List.replicate 0 true from rfl, loopStep_iterate,
    pairFst_pair]

theorem foldIdx_length_le (F : List Bool → List Bool) (x : List Bool) (B : ℕ)
    (hF : ∀ acc i, (F (pair acc (pair x (List.replicate i true)))).length ≤ B) :
    ∀ (n : ℕ) (acc : List Bool) (i : ℕ), acc.length ≤ B →
      (foldIdx F x acc i n).length ≤ B
  | 0, _, _, h => h
  | n + 1, acc, i, _ => by
      rw [foldIdx_succ]
      exact foldIdx_length_le F x B hF n _ (i + 1) (hF acc i)

theorem loopStep_mem_FP {F : List Bool → List Bool} (hF : F ∈ FP) : loopStep F ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairFst (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.fstBlock_mem_FP
    simpa [Function.comp] using this
  have hsnd : ∀ {a : List Bool → List Bool}, a ∈ FP → (fun z => pairSnd (a z)) ∈ FP := by
    intro a ha
    have := mem_FP_comp ha Cobham.sndBlock_mem_FP
    simpa [Function.comp] using this
  have hacc := hfst hid
  have hw := hsnd hid
  have hx := hfst hw
  have hi := hsnd hw
  have harg : (fun s => pair (pairFst s) (pair (pairFst (pairSnd s)) (pairSnd (pairSnd s))))
      ∈ FP := Cobham.pairFn_mem_FP hacc (Cobham.pairFn_mem_FP hx hi)
  have hbody : (fun s => F (pair (pairFst s) (pair (pairFst (pairSnd s))
      (pairSnd (pairSnd s))))) ∈ FP := by
    have := mem_FP_comp harg hF
    simpa [Function.comp] using this
  have hcons : (fun s => true :: pairSnd (pairSnd s)) ∈ FP := by
    have := mem_FP_comp hi (Cobham.cons_mem_FP true)
    simpa [Function.comp] using this
  exact Cobham.pairFn_mem_FP hbody (Cobham.pairFn_mem_FP hx hcons)

/-- **An indexed fold with a polynomial-time body is polynomial-time**, provided the
accumulator stays within the width of `bnd`. -/
theorem foldLoopFn_mem_FP {F : List Bool → List Bool} (hF : F ∈ FP)
    {init x len bnd : List Bool → List Bool} (hinit : init ∈ FP) (hx : x ∈ FP)
    (hlen : len ∈ FP) (hbnd : bnd ∈ FP) (hinit_le : ∀ z, (init z).length ≤ (bnd z).length)
    (hF_le : ∀ z acc i, (F (pair acc (pair (x z) (List.replicate i true)))).length
      ≤ (bnd z).length) :
    (fun z => foldLoop F (init z) (x z) (len z)) ∈ FP := by
  have hstart : (fun z => pair (init z) (pair (x z) [])) ∈ FP :=
    Cobham.pairFn_mem_FP hinit (Cobham.pairFn_mem_FP hx (constFn_mem_FP []))
  have hwidth : (fun z => pair (bnd z) (pair (x z) (len z))) ∈ FP :=
    Cobham.pairFn_mem_FP hbnd (Cobham.pairFn_mem_FP hx hlen)
  have hbound : ∀ z, ∀ n ≤ (len z).length,
      ((loopStep F)^[n] (pair (init z) (pair (x z) []))).length
        ≤ (pair (bnd z) (pair (x z) (len z))).length := by
    intro z n hn
    rw [show ([] : List Bool) = List.replicate 0 true from rfl, loopStep_iterate, pair_length,
      pair_length, pair_length, pair_length, List.length_replicate]
    have := foldIdx_length_le F (x z) (bnd z).length (hF_le z) n (init z) 0 (hinit_le z)
    omega
  have h := Cobham.iterate_mem_FP (loopStep_mem_FP hF) hstart hlen hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simpa [Function.comp, foldLoop] using h1

end Complexity
