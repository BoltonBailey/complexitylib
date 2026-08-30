/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.RepeatSem
public import Complexitylib.Classes.Interactive.Internal.SeqBound

/-!
# The acceptance probability of a repeated protocol

⚠️ Unreviewed by Bolton

The coins of the `K`-fold repetition are `K` blocks of the base protocol's coins
(`Complexity.blocksEquiv`), and by `Complexity.RepArgs.accepts_iff` the verifier accepts when a
majority of the runs accept. On a no-instance every run is accepted with conditional probability
at most `1/3`, whatever the earlier runs were, so the sequential tail bound
`Complexity.card_fireCount_le` applies; on a yes-instance the honest prover replays the honest
strategy in every run, the runs become independent, and the block-majority bound
`Complexity.eventProb_blockMajority_true_ge_one_sub_two_pow` applies.

## Main results

- `Complexity.RepArgs.eventProb_repeat_le` — soundness of the repetition
- `Complexity.RepArgs.le_eventProb_repeat` — completeness of the repetition
-/

@[expose] public section

namespace Complexity

namespace RepArgs

variable (A : RepArgs) (x : List Bool) (K : ℕ)

/-! ## Coins as blocks -/

/-- The coin blocks of a seed given block by block. -/
def bOf {T : ℕ} (f : Fin K → (Fin T → Bool)) (i : ℕ) : List Bool :=
  if h : i < K then BitString.toList (f ⟨i, h⟩) else []

theorem bOf_of_lt {T : ℕ} (f : Fin K → (Fin T → Bool)) (i : ℕ) (h : i < K) :
    bOf K f i = BitString.toList (f ⟨i, h⟩) := dif_pos h

theorem toList_getElem {n : ℕ} (r : BitString n) (i : ℕ) (h : i < r.toList.length) :
    r.toList[i] = r ⟨i, by simpa using h⟩ := by
  simp [BitString.toList]

/-- The `i`-th coin block of a seed is its `i`-th block. -/
theorem blk_toList (r : Fin ((A.repeatProtocol K).coins x.length) → Bool) (i : ℕ) (hi : i < K) :
    A.blk x (BitString.toList r) i
      = BitString.toList (blocksEquiv K (A.prot.coins x.length) r ⟨i, hi⟩) := by
  have hKT : i * A.prot.coins x.length + A.prot.coins x.length
      ≤ K * A.prot.coins x.length := by nlinarith
  unfold blk
  refine List.ext_getElem ?_ fun j h1 h2 => ?_
  · rw [List.length_take, List.length_drop, BitString.length_toList, BitString.length_toList,
      repeatProtocol_coins]
    omega
  · rw [List.getElem_take, List.getElem_drop, toList_getElem, toList_getElem, blocksEquiv_apply]
    congr 1
    ext
    rw [finProdFinEquiv_apply_val]
    simp only
    ring

theorem blk_toList_eq_bOf (r : Fin ((A.repeatProtocol K).coins x.length) → Bool) (i : ℕ)
    (hi : i < K) :
    A.blk x (BitString.toList r) i = bOf K (blocksEquiv K (A.prot.coins x.length) r) i := by
  rw [blk_toList A x K r i hi, bOf_of_lt]

/-! ## The run events -/

open Classical in
/-- The event that run `i` is accepted, as a function of the blocks. -/
noncomputable def runEvent (S : ProverStrategy) :
    Fin K → (Fin K → (Fin (A.prot.coins x.length) → Bool)) → Bool :=
  fun i f => decide (A.prot.Accepts (A.runStrategy x S (bOf K f) i) x (BitString.toList (f i)))

theorem runEvent_prefixed (S : ProverStrategy) : Prefixed (A.runEvent x K S) := by
  intro i f g hfg
  simp only [runEvent]
  have hstrat : A.runStrategy x S (bOf K f) i = A.runStrategy x S (bOf K g) i := by
    refine A.runStrategy_congr x S i fun j hj => ?_
    rw [bOf, bOf, dif_pos (by omega), dif_pos (by omega), hfg ⟨j, by omega⟩ (by
      show j ≤ i.val; omega)]
  rw [hstrat, hfg i le_rfl]

open Classical in
/-- **Acceptance of the repetition is a majority of the run events.** -/
theorem accepts_iff_fireCount (S : ProverStrategy)
    (r : Fin ((A.repeatProtocol K).coins x.length) → Bool) :
    (A.repeatProtocol K).Accepts S x (BitString.toList r)
      ↔ K + 1 ≤ 2 * fireCount (A.runEvent x K S) (blocksEquiv K (A.prot.coins x.length) r) := by
  rw [A.accepts_iff x K S]
  set f := blocksEquiv K (A.prot.coins x.length) r with hf
  have hcard : ((Finset.range K).filter fun i =>
      A.prot.Accepts (A.runStrategy x S (A.blk x (BitString.toList r)) i) x
        (A.blk x (BitString.toList r) i)).card
      = fireCount (A.runEvent x K S) f := by
    rw [fireCount, Finset.card_filter, Finset.card_filter]
    set g : ℕ → ℕ := fun n => if h : n < K then
      (if A.runEvent x K S ⟨n, h⟩ f = true then 1 else 0) else 0 with hg
    have h1 : (∑ i : Fin K, if A.runEvent x K S i f = true then 1 else 0)
        = ∑ i : Fin K, g i.val := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hg]
      simp only [dif_pos i.isLt]
    rw [h1, Fin.sum_univ_eq_sum_range g K]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    rw [hg]
    simp only [dif_pos hn, runEvent, decide_eq_true_eq]
    have hb : A.blk x (BitString.toList r) = fun i => A.blk x (BitString.toList r) i := rfl
    have hstrat : A.runStrategy x S (A.blk x (BitString.toList r)) n
        = A.runStrategy x S (bOf K f) n :=
      A.runStrategy_congr x S n fun j hj => A.blk_toList_eq_bOf x K r j (by omega)
    rw [hstrat, A.blk_toList_eq_bOf x K r n hn, bOf_of_lt]
  rw [hcard]

/-! ## Soundness -/

theorem card_acceptEvent_le_of_eventProb_le {prot : Protocol} {S : ProverStrategy}
    {x : List Bool} {s : ℚ} (h : eventProb (prot.acceptEvent S x) ≤ s) :
    ((prot.acceptEvent S x).card : ℚ) ≤ s * 2 ^ prot.coins x.length := by
  rw [eventProb, div_le_iff₀ (by positivity)] at h
  exact h

open Classical in
/-- On a no-instance the run events are conditionally bounded by `1/3`. -/
theorem runEvent_condBounded {S : ProverStrategy} (hS : S.Bounded (A.prot.msgLen x.length))
    (hno : ∀ S' : ProverStrategy, S'.Bounded (A.prot.msgLen x.length) →
      eventProb (A.prot.acceptEvent S' x) ≤ 1 / 3) :
    CondBounded (1 / 3) (A.runEvent x K S) := by
  intro i f
  have hstrat : ∀ y, A.runStrategy x S (bOf K (Function.update f i y)) i
      = A.runStrategy x S (bOf K f) i := by
    intro y
    refine A.runStrategy_congr x S i fun j hj => ?_
    rw [bOf, bOf, dif_pos (by omega), dif_pos (by omega),
      Function.update_of_ne (by intro h; rw [Fin.ext_iff] at h; simp at h; omega)]
  have heq : (Finset.univ.filter fun y : Fin (A.prot.coins x.length) → Bool =>
      A.runEvent x K S i (Function.update f i y) = true)
      = A.prot.acceptEvent (A.runStrategy x S (bOf K f) i) x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, runEvent, hstrat,
      Function.update_self, decide_eq_true_eq, Protocol.acceptEvent]
  rw [heq, card_finArrowBool]
  push_cast
  exact card_acceptEvent_le_of_eventProb_le
    (hno _ (A.runStrategy_bounded x hS (bOf K f) i))

/-- The binomial tail at the majority threshold, reflected into the form of
`binomial_lower_tail_le`. -/
theorem tailProb_third_eq (j : ℕ) :
    tailProb (1 / 3) (2 * j + 1) (j + 1)
      = ∑ i ∈ Finset.range (j + 1),
          ((2 * j + 1).choose i : ℚ) * (2 / 3) ^ i * (1 - 2 / 3) ^ (2 * j + 1 - i) := by
  rw [tailProb_eq_sum, ← Finset.sum_range_reflect]
  have hsplit : ∀ i ∈ Finset.range (2 * j + 1 + 1),
      (if j + 1 ≤ 2 * j + 1 + 1 - 1 - i then
        ((2 * j + 1).choose (2 * j + 1 + 1 - 1 - i) : ℚ) * (1 / 3) ^ (2 * j + 1 + 1 - 1 - i)
          * (1 - 1 / 3) ^ (2 * j + 1 - (2 * j + 1 + 1 - 1 - i)) else 0)
      = if i ≤ j then ((2 * j + 1).choose i : ℚ) * (2 / 3) ^ i * (1 - 2 / 3) ^ (2 * j + 1 - i)
          else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : 2 * j + 1 + 1 - 1 - i = 2 * j + 1 - i := by omega
    rw [h1]
    by_cases hij : i ≤ j
    · rw [if_pos (by omega), if_pos hij, Nat.choose_symm (by omega),
        show 2 * j + 1 - (2 * j + 1 - i) = i by omega]
      norm_num
      ring
    · rw [if_neg (by omega), if_neg hij]
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter,
    show (Finset.range (2 * j + 1 + 1)).filter (fun i => i ≤ j) = Finset.range (j + 1) by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega]

open Classical in
/-- **Soundness of sequential repetition.** If every bounded prover is accepted with probability
at most `1/3`, then after `12 k + 1` runs every bounded prover is accepted with probability at most
`2 ^ (-k)`. -/
theorem eventProb_repeat_le (k : ℕ) {S : ProverStrategy}
    (hS : S.Bounded (A.prot.msgLen x.length))
    (hno : ∀ S' : ProverStrategy, S'.Bounded (A.prot.msgLen x.length) →
      eventProb (A.prot.acceptEvent S' x) ≤ 1 / 3) :
    eventProb ((A.repeatProtocol (12 * k + 1)).acceptEvent S x) ≤ 1 / (2 : ℚ) ^ k := by
  set K := 12 * k + 1 with hK
  have hcard : ((A.repeatProtocol K).acceptEvent S x).card
      = (Finset.univ.filter fun f : Fin K → (Fin (A.prot.coins x.length) → Bool) =>
          6 * k + 1 ≤ fireCount (A.runEvent x K S) f).card := by
    refine Finset.card_equiv (blocksEquiv K (A.prot.coins x.length)) fun r => ?_
    simp only [Protocol.acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [A.accepts_iff_fireCount x K S r]
    omega
  have hbound := card_fireCount_le (X := Fin (A.prot.coins x.length) → Bool) (q := 1 / 3)
    (by norm_num) (by norm_num) K (A.runEvent x K S) (A.runEvent_prefixed x K S)
    (A.runEvent_condBounded x K hS hno) (6 * k + 1)
  rw [card_finArrowBool] at hbound
  have hprob : eventProb ((A.repeatProtocol K).acceptEvent S x)
      ≤ tailProb (1 / 3) K (6 * k + 1) := by
    rw [eventProb, div_le_iff₀ (by positivity), hcard]
    refine le_trans hbound (le_of_eq ?_)
    push_cast
    rw [← pow_mul]
    show _ = _ * (2 : ℚ) ^ (K * A.prot.coins x.length)
    rw [Nat.mul_comm (A.prot.coins x.length) K]
  refine le_trans hprob ?_
  rw [hK, show 12 * k + 1 = 2 * (6 * k) + 1 by ring, tailProb_third_eq]
  exact le_trans (binomial_lower_tail_le (6 * k) (2 / 3) (by norm_num) (by norm_num))
    (amplification_power_le k)

/-! ## Completeness -/

/-- The honest prover of the repetition: replay the honest strategy on the current run. -/
def replayStrategy (S₀ : ProverStrategy) (R : ℕ) : ProverStrategy :=
  fun σ => S₀ (σ.drop (2 * R * (σ.length / (2 * R))))

theorem replayStrategy_bounded {S₀ : ProverStrategy} {m : ℕ} (hS₀ : S₀.Bounded m)
    (R : ℕ) :
    (replayStrategy S₀ R).Bounded m :=
  fun _ => hS₀ _

/-- In every run the replayed prover behaves as the honest one on short transcripts. -/
theorem runStrategy_replay (S₀ : ProverStrategy) (b : ℕ → List Bool) (i : ℕ)
    (σ : Transcript)
    (hσ : σ.length < 2 * A.prot.rounds x.length) :
    A.runStrategy x (replayStrategy S₀ (A.prot.rounds x.length)) b i σ = S₀ σ := by
  set R := A.prot.rounds x.length with hR'
  rw [runStrategy, replayStrategy, List.length_append, prefixB_length]
  have hdiv : (i * (2 * R) + σ.length) / (2 * R) = i :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [hdiv, show 2 * R * i = (A.prefixB x (replayStrategy S₀ R) b i).length by
    rw [prefixB_length]; ring, List.drop_left]

open Classical in
/-- Under the replayed prover every run is the honest interaction on its own block. -/
theorem runEvent_replay (S₀ : ProverStrategy) (i : Fin K)
    (f : Fin K → (Fin (A.prot.coins x.length) → Bool)) :
    A.runEvent x K (replayStrategy S₀ (A.prot.rounds x.length)) i f
      = decide (f i ∈ A.prot.acceptEvent S₀ x) := by
  simp only [runEvent, Protocol.acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  congr 1
  apply propext
  rw [Protocol.Accepts, Protocol.Accepts,
    Protocol.transcript_congr_lt A.prot x _ _ fun σ hσ => A.runStrategy_replay x S₀ _ i σ hσ]

open Classical in
/-- **Completeness of sequential repetition.** If some bounded prover is accepted with probability
at least `2/3`, then after `12 k + 1` runs the replayed prover is accepted with probability at
least `1 - 2 ^ (-k)`. -/
theorem le_eventProb_repeat (k : ℕ) {S₀ : ProverStrategy}
    (hyes : 2 / 3 ≤ eventProb (A.prot.acceptEvent S₀ x)) :
    1 - 1 / (2 : ℚ) ^ k ≤ eventProb ((A.repeatProtocol (12 * k + 1)).acceptEvent
      (replayStrategy S₀ (A.prot.rounds x.length)) x) := by
  set K := 12 * k + 1 with hK
  set E := A.prot.acceptEvent S₀ x with hE
  have hev : (A.repeatProtocol K).acceptEvent (replayStrategy S₀ (A.prot.rounds x.length)) x
      = Finset.univ.filter fun w : Fin ((A.repeatProtocol K).coins x.length) → Bool =>
          blockMajority (k := K) (T := A.prot.coins x.length) E w = true := by
    ext r
    simp only [Protocol.acceptEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [A.accepts_iff_fireCount, blockMajority, decide_eq_true_eq, blockEventCount, fireCount]
    have hfilt : (Finset.univ.filter fun i : Fin K =>
        A.runEvent x K (replayStrategy S₀ (A.prot.rounds x.length)) i
          (blocksEquiv K (A.prot.coins x.length) r) = true)
        = Finset.univ.filter fun i : Fin K => blocksEquiv K (A.prot.coins x.length) r i ∈ E := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, A.runEvent_replay x K S₀,
        decide_eq_true_eq, ← hE]
    rw [hfilt]
    omega
  rw [hev]
  exact eventProb_blockMajority_true_ge_one_sub_two_pow (A.prot.coins x.length) k E hyes

end RepArgs

end Complexity
