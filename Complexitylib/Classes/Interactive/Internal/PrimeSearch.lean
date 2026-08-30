/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ModArith
public import Complexitylib.Classes.PCP.Internal.Materialize
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Mathlib.NumberTheory.Bertrand

/-!
# Finding a prime of polynomial size in polynomial time

⚠️ Unreviewed by Bolton

Shamir's verifier needs a prime field, and only a *polynomially large* one: the soundness error
is `Σ d / p`, and `Σ d` is polynomial in the input. A prime of polynomial size can be found by
brute force — trial division is polynomial time in unary — and Bertrand's postulate guarantees
one between `N` and `2 N`. `nextPrime N` is the least such prime, in unary, and `primeBits N`
its binary form at width `N + 1`, the modulus string `ModArith` works with.

## Main definitions

- `primeFlag` — trial-division primality, on unary
- `nextPrime`, `primeBits` — the least prime above `N`, in unary and in binary

## Main results

- `primeFlag_eq_true_iff` — the test is primality
- `nextPrime_spec` — the search finds a prime in `(N, 2 N]`
- `primeBits_eq` — its binary form is `bitsOfLenLE`
- `nextPrimeFn_mem_FP`, `primeBitsFn_mem_FP` — both are polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## Trial division -/

/-- On `pair n (unary i)`: a mark if `i + 2` divides `n`. -/
noncomputable def divisorMark (z : List Bool) : List Bool :=
  selectHead (emptyFlag (modFn2 (pair (pairSnd z ++ [true, true]) (pairFst z)))) [true] []

theorem divisorMark_mem_FP : divisorMark ∈ FP := by
  have harg : (fun z : List Bool => pair (pairSnd z ++ [true, true]) (pairFst z)) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP Cobham.sndBlock_mem_FP (constFn_mem_FP _))
      Cobham.fstBlock_mem_FP
  have hmod : (fun z => modFn2 (pair (pairSnd z ++ [true, true]) (pairFst z))) ∈ FP := by
    have := mem_FP_comp harg modFn2_mem_FP
    simpa [Function.comp] using this
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hmod) (constFn_mem_FP _) (constFn_mem_FP _)

theorem emptyFlag_eq_true_iff (y : List Bool) : emptyFlag y = [true] ↔ y = [] := by
  rw [emptyFlag, lenLeFlag_eq_true_iff]
  simp

theorem emptyFlag_flag (y : List Bool) : emptyFlag y = [true] ∨ emptyFlag y = [false] :=
  lenLeFlag_flag _ _

theorem divisorMark_length (n i : ℕ) :
    (divisorMark (pair (List.replicate n true) (List.replicate i true))).length
      = if n % (i + 2) = 0 then 1 else 0 := by
  rw [divisorMark, pairSnd_pair, pairFst_pair, modFn2_eq (by simp), List.length_replicate,
    List.length_append, List.length_replicate]
  simp only [List.length_cons, List.length_nil]
  rcases emptyFlag_flag (List.replicate (n % (i + 2)) true) with h | h
  · rw [h, selectHead_cons_true]
    have := (emptyFlag_eq_true_iff _).mp h
    rw [List.replicate_eq_nil_iff] at this
    rw [if_pos this]
    rfl
  · rw [h, selectHead_cons_false]
    have : ¬ List.replicate (n % (i + 2)) true = [] := by
      intro heq
      rw [← emptyFlag_eq_true_iff, h] at heq
      exact absurd heq (by decide)
    rw [List.replicate_eq_nil_iff] at this
    rw [if_neg this]
    rfl

/-- The number of divisors of `n` in `[2, n)`, in unary. -/
noncomputable def divisorCount (n : List Bool) : List Bool :=
  countOver divisorMark (pair (n.drop 2) n)

theorem divisorCount_mem_FP : divisorCount ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hdrop : (fun z : List Bool => z.drop 2) ∈ FP := by
    have := dropLenFn_mem_FP (constFn_mem_FP [false, false]) hid
    simpa using this
  have := mem_FP_comp (Cobham.pairFn_mem_FP hdrop hid) (countOver_mem_FP divisorMark_mem_FP)
  simpa [Function.comp, divisorCount] using this

theorem divisorCount_length (n : ℕ) :
    (divisorCount (List.replicate n true)).length
      = ∑ i ∈ Finset.range (n - 2), if n % (i + 2) = 0 then 1 else 0 := by
  rw [divisorCount, List.drop_replicate, length_countOver]
  exact Finset.sum_congr rfl fun i _ => divisorMark_length n i

/-- The primality test: at least two, and no divisor in `[2, n)`. -/
noncomputable def primeFlag (n : List Bool) : List Bool :=
  andBit (lenLeFlag n [false, false]) (emptyFlag (divisorCount n))

theorem primeFlag_mem_FP : primeFlag ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  exact andBitFn_mem_FP (lenLeFlagFn_mem_FP hid (constFn_mem_FP _))
    (emptyFlagFn_mem_FP divisorCount_mem_FP)

/-- **The test is primality.** -/
theorem primeFlag_eq_true_iff (n : ℕ) :
    primeFlag (List.replicate n true) = [true] ↔ n.Prime := by
  rw [primeFlag, andBit_eq_true_iff (lenLeFlag_flag _ _) (emptyFlag_flag _), lenLeFlag_eq_true_iff,
    emptyFlag_eq_true_iff, List.length_replicate, Nat.prime_def_lt]
  simp only [List.length_cons, List.length_nil]
  have hcount : divisorCount (List.replicate n true) = []
      ↔ ∀ i ∈ Finset.range (n - 2), n % (i + 2) ≠ 0 := by
    rw [← List.length_eq_zero_iff, divisorCount_length, Finset.sum_eq_zero_iff]
    constructor
    · intro h i hi
      have := h i hi
      split_ifs at this with hh
      exact hh
    · intro h i hi
      rw [if_neg (h i hi)]
  rw [hcount]
  constructor
  · rintro ⟨h2, hdiv⟩
    refine ⟨by omega, fun m hm hmd => ?_⟩
    by_contra hm1
    have hm2 : 2 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hmd
        omega
      · omega
    have := hdiv (m - 2) (Finset.mem_range.mpr (by omega))
    rw [show m - 2 + 2 = m by omega] at this
    exact this (Nat.dvd_iff_mod_eq_zero.mp hmd)
  · rintro ⟨h2, hdiv⟩
    refine ⟨by omega, fun i hi hmod => ?_⟩
    rw [Finset.mem_range] at hi
    have := hdiv (i + 2) (by omega) (Nat.dvd_of_mod_eq_zero hmod)
    omega

/-! ## The search -/

/-- On `pair N (unary k)`: a mark if `N + 1 + k` is prime. -/
noncomputable def primeMark (z : List Bool) : List Bool :=
  selectHead (primeFlag (pairFst z ++ [true] ++ pairSnd z)) [true] []

theorem primeMark_mem_FP : primeMark ∈ FP := by
  have harg : (fun z : List Bool => pairFst z ++ [true] ++ pairSnd z) ∈ FP :=
    Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP Cobham.fstBlock_mem_FP (constFn_mem_FP _))
      Cobham.sndBlock_mem_FP
  have hflag : (fun z => primeFlag (pairFst z ++ [true] ++ pairSnd z)) ∈ FP := by
    have := mem_FP_comp harg primeFlag_mem_FP
    simpa [Function.comp] using this
  exact Cobham.selectHeadFn_mem_FP hflag (constFn_mem_FP _) (constFn_mem_FP _)

theorem primeMark_length (N k : ℕ) :
    (primeMark (pair (List.replicate N true) (List.replicate k true))).length
      = if (N + 1 + k).Prime then 1 else 0 := by
  rw [primeMark, pairFst_pair, pairSnd_pair, show List.replicate N true ++ [true]
      ++ List.replicate k true = List.replicate (N + 1 + k) true by
    rw [List.replicate_add, List.replicate_add, List.replicate_one]]
  by_cases hp : (N + 1 + k).Prime
  · rw [if_pos hp, (primeFlag_eq_true_iff _).mpr hp, selectHead_cons_true]
    rfl
  · rw [if_neg hp]
    rcases andBit_flag (lenLeFlag (List.replicate (N + 1 + k) true) [false, false])
      (emptyFlag (divisorCount (List.replicate (N + 1 + k) true))) with h | h
    · exact absurd ((primeFlag_eq_true_iff _).mp h) hp
    · rw [primeFlag, h, selectHead_cons_false]
      rfl

/-- The least prime above `N`, in unary. -/
noncomputable def nextPrime (N : List Bool) : List Bool :=
  N ++ [true] ++ findFirst primeMark (pair N N)

theorem nextPrimeFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => nextPrime (a z)) ∈ FP := by
  have hfind : (fun z => findFirst primeMark (pair (a z) (a z))) ∈ FP := by
    have := mem_FP_comp (Cobham.pairFn_mem_FP ha ha) (findFirst_mem_FP primeMark_mem_FP)
    simpa [Function.comp] using this
  exact Cobham.appendFn_mem_FP (Cobham.appendFn_mem_FP ha (constFn_mem_FP _)) hfind

/-- **The search finds a prime in `(N, 2 N]`**, the least one. -/
theorem nextPrime_spec (N : ℕ) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p ≤ 2 * N ∧
      nextPrime (List.replicate N true) = List.replicate p true := by
  classical
  obtain ⟨q, hq, hNq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hq' : N + 1 + (q - N - 1) = q := by omega
  have H : ∃ k, (N + 1 + k).Prime := ⟨q - N - 1, by rw [hq']; exact hq⟩
  set c := Nat.find H with hc
  have hcp : (N + 1 + c).Prime := Nat.find_spec H
  have hcle : c ≤ q - N - 1 := Nat.find_min' H (by rw [hq']; exact hq)
  refine ⟨N + 1 + c, hcp, by omega, by omega, ?_⟩
  rw [nextPrime, findFirst_eq_replicate, length_findFirst_eq (c := c) (by omega)
    (by rw [primeMark_length, if_pos hcp]; exact one_ne_zero)
    (fun k hk => by
      rw [primeMark_length, if_neg]
      exact Nat.find_min H hk),
    List.replicate_add, List.replicate_add, List.replicate_one]

/-- The least prime above `N`, as an `N + 1`-bit string. -/
noncomputable def primeBits (N : List Bool) : List Bool :=
  coinStr (N ++ [true]).length (nextPrime N).length

theorem primeBitsFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => primeBits (a z)) ∈ FP := by
  refine coinStr_mem_FP (t := fun z => (a z ++ [true]).length)
    (c := fun z => (nextPrime (a z)).length) ?_ ?_
  · have := marks_mem_FP (Cobham.appendFn_mem_FP ha (constFn_mem_FP [true]))
    refine mem_FP_of_eq this fun z => ?_
    rw [marks_eq]
  · have := marks_mem_FP (nextPrimeFn_mem_FP ha)
    refine mem_FP_of_eq this fun z => ?_
    rw [marks_eq]

/-- **The binary form of the prime found.** -/
theorem primeBits_eq (N : ℕ) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ p ≤ 2 * N ∧ p < 2 ^ (N + 1) ∧
      primeBits (List.replicate N true) = bitsOfLenLE (N + 1) p := by
  obtain ⟨p, hp, hNp, hp2, heq⟩ := nextPrime_spec N hN
  have hlt : p < 2 ^ (N + 1) := by
    have := Nat.lt_two_pow_self (n := N)
    rw [pow_succ]
    omega
  refine ⟨p, hp, hNp, hp2, hlt, ?_⟩
  rw [primeBits, heq, List.length_replicate, List.length_append, List.length_replicate,
    coinStr_eq (by simpa using hlt)]
  rfl

end Complexity
