/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.RepeatProb
public import Complexitylib.Classes.Containments.Internal.PVerdict

/-!
# Amplification for interactive proofs

⚠️ Unreviewed by Bolton

`IP` is defined with completeness `2/3` and soundness `1/3`. Sequential repetition with a majority
vote drives both errors down exponentially, so the thresholds are immaterial: `IPWith c s` is the
class defined with completeness `c` and soundness `s`, and for every `k`,
`IPWith (1 - 2⁻ᵏ) 2⁻ᵏ = IP`.

The repetition is built in `Complexitylib.Classes.Interactive.Internal.RepeatDefs` (the verifier,
in Cobham's algebra), analysed in `Complexitylib.Classes.Interactive.Internal.RepeatSem` (its
transcripts, run by run) and `Complexitylib.Classes.Interactive.Internal.RepeatProb` (its
acceptance probability). The prover of the repeated protocol is adaptive — it may play run `i`
knowing how the earlier runs went — which is why soundness needs the sequential tail bound of
`Complexitylib.Classes.Interactive.Internal.SeqBound` rather than plain independence.

## Main definitions

- `IPWith` — `IP` with arbitrary completeness and soundness thresholds

## Main results

- `IP_eq_IPWith` — `IP` is `IPWith (2/3) (1/3)`
- `IPWith_mono` — weaker thresholds give a larger class
- `IP_subset_IPWith_two_pow` — **amplification**: `IP ⊆ IPWith (1 - 2⁻ᵏ) 2⁻ᵏ`
- `IPWith_two_pow_eq_IP` — threshold robustness: `IPWith (1 - 2⁻ᵏ) 2⁻ᵏ = IP` for `k ≥ 2`
-/

@[expose] public section

namespace Complexity

/-- **`IP` with thresholds**: interactive proof systems with completeness at least `c` and
soundness at most `s`, everything else as in `IP`. -/
def IPWith (c s : ℚ) : Set Language :=
  {L | ∃ (prot : Protocol) (rp cp mp : Polynomial ℕ),
    (∀ n, prot.rounds n = rp.eval n) ∧ (∀ n, prot.coins n = cp.eval n) ∧
    (∀ n, prot.msgLen n = mp.eval n) ∧
    (∀ x ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen x.length) ∧
      c ≤ eventProb (prot.acceptEvent S x)) ∧
    (∀ x ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen x.length) →
      eventProb (prot.acceptEvent S x) ≤ s)}

/-- `IP` is the class with the conventional thresholds. -/
theorem IP_eq_IPWith : IP = IPWith (2 / 3) (1 / 3) := rfl

/-- Weakening the thresholds enlarges the class. -/
theorem IPWith_mono {c c' s s' : ℚ} (hc : c' ≤ c) (hs : s ≤ s') :
    IPWith c s ⊆ IPWith c' s' := by
  rintro L ⟨prot, rp, cp, mp, hr, hcp, hm, hyes, hno⟩
  refine ⟨prot, rp, cp, mp, hr, hcp, hm, fun x hx => ?_, fun x hx S hS => ?_⟩
  · obtain ⟨S, hS, h⟩ := hyes x hx
    exact ⟨S, hS, le_trans hc h⟩
  · exact le_trans (hno x hx S hS) hs

/-- **Amplification.** Sequential repetition `12 k + 1` times with a majority vote brings the
completeness error and the soundness error of any `IP` protocol down to `2⁻ᵏ`. -/
theorem IP_subset_IPWith_two_pow (k : ℕ) :
    IP ⊆ IPWith (1 - 1 / (2 : ℚ) ^ k) (1 / (2 : ℚ) ^ k) := by
  rintro L ⟨prot, rp, cp, mp, hr, hcp, hm, hyes, hno⟩
  obtain ⟨g, hg, hgs⟩ := exists_decisionFn_of_mem_P prot.verdict_mem
  let A : RepArgs := ⟨prot, rp, cp, hr, hcp, g, hg, hgs⟩
  refine ⟨A.repeatProtocol (12 * k + 1), Polynomial.C (12 * k + 1) * rp,
    Polynomial.C (12 * k + 1) * cp, mp, fun n => ?_, fun n => ?_, fun n => hm n,
    fun x hx => ?_, fun x hx S hS => ?_⟩
  · rw [RepArgs.repeatProtocol_rounds, Polynomial.eval_mul, Polynomial.eval_C, hr n]
  · rw [RepArgs.repeatProtocol_coins, Polynomial.eval_mul, Polynomial.eval_C, hcp n]
  · obtain ⟨S₀, hS₀, h⟩ := hyes x hx
    exact ⟨RepArgs.replayStrategy S₀ (prot.rounds x.length),
      RepArgs.replayStrategy_bounded hS₀ _, A.le_eventProb_repeat x k h⟩
  · exact A.eventProb_repeat_le x k hS fun S' hS' => hno x hx S' hS'

/-- **Threshold robustness.** For `k ≥ 2` the class defined with thresholds `1 - 2⁻ᵏ` and
`2⁻ᵏ`
is `IP` itself. -/
theorem IPWith_two_pow_eq_IP {k : ℕ} (hk : 2 ≤ k) :
    IPWith (1 - 1 / (2 : ℚ) ^ k) (1 / (2 : ℚ) ^ k) = IP := by
  have h4 : (4 : ℚ) ≤ 2 ^ k := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hk
    norm_num at this
    exact this
  have hs : 1 / (2 : ℚ) ^ k ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine subset_antisymm (IPWith_mono (by linarith) hs) (IP_subset_IPWith_two_pow k)

end Complexity
