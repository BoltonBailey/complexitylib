/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PH.SipserLautemann.Covering
public import Complexitylib.Classes.Randomized
public import Complexitylib.Models.TuringMachine.Repetition.Correctness

/-!
# The amplified Lautemann characterization

Combining majority amplification with the covering lemma of
`Complexitylib.Classes.PH.SipserLautemann.Covering`, this file proves the
`∃∀` characterization at the heart of the Sipser–Lautemann theorem.
-/

@[expose] public section

namespace Complexity

namespace Lautemann

variable {k : ℕ}

/-- `13 K²  < 2 ^ K` from `K = 11` on: the numeric fact making the amplified
seed count smaller than the amplified error denominator. -/
private theorem thirteen_mul_sq_lt_two_pow : ∀ K, 11 ≤ K → 13 * K ^ 2 < 2 ^ K := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.lt_or_ge n 11 with hn | hn
    · have hn10 : n = 10 := by omega
      subst hn10
      norm_num
    · have hprev := ih (by omega)
      calc 13 * (n + 1) ^ 2 ≤ 2 * (13 * n ^ 2) := by nlinarith
        _ < 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Amplification exponent for inputs of length `n`: the amplified error is
`2 ^ (-ampExp f n)`. It is taken large enough to dominate the amplified seed
length, which is what the covering lemma's soundness direction needs. -/
def ampExp (f : ℕ → ℕ) (n : ℕ) : ℕ := f n + 11

/-- Number of independent trials of the source machine, an odd count so that
majority votes cannot tie. -/
def ampRuns (f : ℕ → ℕ) (n : ℕ) : ℕ := 12 * ampExp f n + 1

/-- Number of shifts used to cover the seed space: one more than the seed
length, so that the degenerate zero-length seed space is still covered. -/
def ampShifts (f : ℕ → ℕ) (n : ℕ) : ℕ := ampRuns f n * f n + 1

/-- The amplified accepting event: the long seeds on which a strict majority
of the `ampRuns f n` independent trials accepts. -/
def ampEvent (tm : NTM k) (f : ℕ → ℕ) (x : List Bool) :
    Finset (Fin (ampRuns f x.length * f x.length) → Bool) :=
  Finset.univ.filter fun w =>
    blockMajority (NTM.repeatAcceptEvent tm x (f x.length)) w = true

/-- Membership in the amplified event is the majority verdict. -/
@[simp] theorem mem_ampEvent (tm : NTM k) (f : ℕ → ℕ) (x : List Bool)
    (w : Fin (ampRuns f x.length * f x.length) → Bool) :
    w ∈ ampEvent tm f x ↔
      blockMajority (NTM.repeatAcceptEvent tm x (f x.length)) w = true := by
  simp [ampEvent]

/-- The complement of the amplified event is the majority-rejecting event. -/
theorem compl_ampEvent (tm : NTM k) (f : ℕ → ℕ) (x : List Bool) :
    (ampEvent tm f x)ᶜ = Finset.univ.filter fun w =>
      blockMajority (NTM.repeatAcceptEvent tm x (f x.length)) w = false := by
  ext w
  simp [ampEvent, Bool.not_eq_true]

/-- Membership in the complement of the amplified event is the rejecting
majority verdict. Not a `simp` lemma: `simp` reaches the same normal form
through `Finset.mem_compl` and `mem_ampEvent`. -/
theorem mem_compl_ampEvent (tm : NTM k) (f : ℕ → ℕ) (x : List Bool)
    (w : Fin (ampRuns f x.length * f x.length) → Bool) :
    w ∈ (ampEvent tm f x)ᶜ ↔
      blockMajority (NTM.repeatAcceptEvent tm x (f x.length)) w = false := by
  rw [compl_ampEvent]
  simp

/-- The number of shifts is below the amplified error denominator. -/
theorem ampShifts_lt_two_pow_ampExp (f : ℕ → ℕ) (n : ℕ) :
    ampShifts f n < 2 ^ ampExp f n := by
  have hK : 11 ≤ ampExp f n := by simp [ampExp]
  have hfn : f n ≤ ampExp f n := by simp [ampExp]
  have hnum : ampShifts f n ≤ 13 * (ampExp f n) ^ 2 := by
    have hmul : ampRuns f n * f n ≤ (12 * ampExp f n + 1) * ampExp f n :=
      Nat.mul_le_mul_left _ hfn
    simp only [ampShifts, ampRuns] at *
    nlinarith
  exact lt_of_le_of_lt hnum (thirteen_mul_sq_lt_two_pow _ hK)

/-- **Completeness.** On an accepted input the amplified event fails with
probability at most `2 ^ (-ampExp f n)`, so the covering lemma supplies
`ampShifts f n` shifts covering the whole seed space. -/
theorem exists_covers_of_mem {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3)) {x : List Bool} (hx : x ∈ L) :
    ∃ u : Fin (ampShifts f x.length) →
        Fin (ampRuns f x.length * f x.length) → Bool,
      Covers (ampEvent tm f x) u := by
  have hE : 2 / 3 ≤ eventProb (NTM.repeatAcceptEvent tm x (f x.length)) := by
    rw [← NTM.acceptProb_eq_eventProb_repeatAcceptEvent]
    exact haccept x hx
  have herr : eventProb (ampEvent tm f x)ᶜ ≤ 1 / 2 ^ ampExp f x.length := by
    rw [compl_ampEvent]
    exact eventProb_blockMajority_false_le_two_pow (f x.length) (ampExp f x.length) _ hE
  refine exists_covers_of_eventProb_compl_le _ ?_ herr
  have hK : 1 ≤ ampExp f x.length := by simp [ampExp]
  have := Nat.mul_le_mul_right (ampShifts f x.length) hK
  simp only [ampShifts, one_mul] at this ⊢
  omega

/-- **Soundness.** On a rejected input the amplified event holds with
probability at most `2 ^ (-ampExp f n)`, which is too small for
`ampShifts f n` shifts of it to cover the seed space. -/
theorem not_covers_of_notMem {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (hreject : tm.RejectsWithProb L f (1 / 3)) {x : List Bool} (hx : x ∉ L)
    (u : Fin (ampShifts f x.length) → Fin (ampRuns f x.length * f x.length) → Bool) :
    ¬ Covers (ampEvent tm f x) u := by
  have hE : eventProb (NTM.repeatAcceptEvent tm x (f x.length)) ≤ 1 / 3 := by
    rw [← NTM.acceptProb_eq_eventProb_repeatAcceptEvent]
    exact hreject x hx
  have herr : eventProb (ampEvent tm f x) ≤ 1 / 2 ^ ampExp f x.length :=
    eventProb_blockMajority_true_le_two_pow (f x.length) (ampExp f x.length) _ hE
  exact not_covers_of_eventProb_le _ (ampShifts_lt_two_pow_ampExp f x.length) herr u

/-- **The Lautemann characterization.** For a bounded-error machine deciding
`L`, membership is equivalent to the existence of a tuple of shifts whose
translates of the amplified accepting event cover the seed space — an `∃∀`
form with a deterministic, polynomially-checkable matrix. -/
theorem mem_iff_exists_covers {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3)) (hreject : tm.RejectsWithProb L f (1 / 3))
    (x : List Bool) :
    x ∈ L ↔ ∃ u : Fin (ampShifts f x.length) →
        Fin (ampRuns f x.length * f x.length) → Bool, Covers (ampEvent tm f x) u := by
  constructor
  · exact fun hx => exists_covers_of_mem haccept hx
  · intro hcov
    by_contra hx
    obtain ⟨u, hu⟩ := hcov
    exact not_covers_of_notMem hreject hx u hu

/-- **The complementary Lautemann characterization.** Non-membership is
equivalent to the existence of shifts covering the seed space with translates
of the majority-*rejecting* event. Together with `mem_iff_exists_covers` this
puts both `L` and its complement in the same `∃∀` form, which is what places
`BPP` in `Σ₂ᵖ ∩ Π₂ᵖ` rather than only in `Σ₂ᵖ`. -/
theorem notMem_iff_exists_covers_compl {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (haccept : tm.AcceptsWithProb L f (2 / 3)) (hreject : tm.RejectsWithProb L f (1 / 3))
    (x : List Bool) :
    x ∉ L ↔ ∃ u : Fin (ampShifts f x.length) →
        Fin (ampRuns f x.length * f x.length) → Bool, Covers (ampEvent tm f x)ᶜ u := by
  constructor
  · intro hx
    have hE : eventProb (NTM.repeatAcceptEvent tm x (f x.length)) ≤ 1 / 3 := by
      rw [← NTM.acceptProb_eq_eventProb_repeatAcceptEvent]
      exact hreject x hx
    have herr : eventProb ((ampEvent tm f x)ᶜ)ᶜ ≤ 1 / 2 ^ ampExp f x.length := by
      rw [compl_compl]
      exact eventProb_blockMajority_true_le_two_pow (f x.length) (ampExp f x.length) _ hE
    refine exists_covers_of_eventProb_compl_le _ ?_ herr
    have hK : 1 ≤ ampExp f x.length := by simp [ampExp]
    have := Nat.mul_le_mul_right (ampShifts f x.length) hK
    simp only [ampShifts, one_mul] at this ⊢
    omega
  · intro hcov hx
    obtain ⟨u, hu⟩ := hcov
    have hE : 2 / 3 ≤ eventProb (NTM.repeatAcceptEvent tm x (f x.length)) := by
      rw [← NTM.acceptProb_eq_eventProb_repeatAcceptEvent]
      exact haccept x hx
    have herr : eventProb (ampEvent tm f x)ᶜ ≤ 1 / 2 ^ ampExp f x.length := by
      rw [compl_ampEvent]
      exact eventProb_blockMajority_false_le_two_pow (f x.length) (ampExp f x.length) _ hE
    exact not_covers_of_eventProb_le _ (ampShifts_lt_two_pow_ampExp f x.length) herr u hu

end Lautemann

end Complexity
