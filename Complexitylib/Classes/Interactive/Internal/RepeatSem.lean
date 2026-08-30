/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.RepeatDefs

/-!
# What the repeated protocol's transcripts are

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Interactive.Internal.RepeatDefs` builds the verifier of the `K`-fold
sequential repetition. This file defines the repeated protocol and describes its interaction: the
transcript after `i` full runs and `m` further rounds is the concatenation of the `i` completed
base transcripts with a partial base transcript of `m` rounds, each run played on its own block of
coins against the prover restricted to the current prefix (`Complexity.RepArgs.transcript_eq`),
and the verifier accepts exactly when a strict majority of the runs are accepted by the base
protocol (`Complexity.RepArgs.accepts_iff`).

The prover of the repeated protocol is adaptive: its behaviour in run `i` may depend on the earlier
runs. `Complexity.RepArgs.prefixB` records the completed runs as a function of the coin blocks
they used, and `Complexity.RepArgs.prefixB_congr` says run `i` only depends on blocks before it.

## Main definitions

- `Complexity.RepArgs.repeatProtocol` — the repeated protocol
- `Complexity.RepArgs.blk` — the coin block of a run
- `Complexity.RepArgs.prefixB`, `Complexity.RepArgs.runStrategy` — the completed runs, and the
  prover as the base protocol sees it in run `i`

## Main results

- `Complexity.Protocol.transcript_succ` — one more round of a transcript
- `Complexity.Protocol.transcript_congr_lt` — a transcript only consults the prover on
  transcripts shorter than twice its round count
- `Complexity.RepArgs.transcript_eq` — the repeated transcript, run by run
- `Complexity.RepArgs.accepts_iff` — acceptance is a majority of accepted runs
- `Complexity.RepArgs.prefixB_congr` — a run depends only on the earlier blocks
-/

@[expose] public section

namespace Complexity

/-! ## Transcripts of a protocol -/

namespace Protocol

variable (prot : Protocol) (x : List Bool)

theorem transcript_succ (S : ProverStrategy) (r : List Bool) (n : ℕ) :
    prot.transcript S x r (n + 1)
      = prot.transcript S x r n
        ++ [prot.vmsg (view x r (prot.transcript S x r n)),
          S (prot.transcript S x r n ++ [prot.vmsg (view x r (prot.transcript S x r n))])] := rfl

/-- **Strategy extensionality, sharp form**: a transcript of `n` rounds only consults the prover
on transcripts of odd length below `2 n`. -/
theorem transcript_congr_lt {S S' : ProverStrategy} (r : List Bool) :
    ∀ n, (∀ σ : Transcript, σ.length < 2 * n → S σ = S' σ) →
      prot.transcript S x r n = prot.transcript S' x r n
  | 0, _ => rfl
  | n + 1, h => by
      have ih := transcript_congr_lt r n fun σ hσ => h σ (by omega)
      rw [transcript_succ, transcript_succ, ih, h]
      rw [List.length_append, transcript_length]
      simp only [List.length_cons, List.length_nil]
      omega

end Protocol

namespace RepArgs

variable (A : RepArgs)

/-! ## The repeated protocol -/

/-- The `K`-fold sequential repetition of the base protocol. -/
noncomputable def repeatProtocol (K : ℕ) : Protocol where
  rounds n := K * A.prot.rounds n
  coins n := K * A.prot.coins n
  msgLen n := A.prot.msgLen n
  vmsg := A.repVmsg
  vmsg_mem := A.repVmsg_mem_FP
  vmsg_len := by
    intro x r τ
    obtain ⟨r', τ', h⟩ := A.repVmsg_shape x r τ
    rw [h]
    exact A.prot.vmsg_len x r' τ'
  verdict := A.repVerdict K
  verdict_mem := A.repVerdict_mem_P K

@[simp] theorem repeatProtocol_rounds (K n : ℕ) :
    (A.repeatProtocol K).rounds n = K * A.prot.rounds n := rfl

@[simp] theorem repeatProtocol_coins (K n : ℕ) :
    (A.repeatProtocol K).coins n = K * A.prot.coins n := rfl

@[simp] theorem repeatProtocol_msgLen (K n : ℕ) :
    (A.repeatProtocol K).msgLen n = A.prot.msgLen n := rfl

/-! ## Runs -/

variable (x : List Bool)

/-- The coin block of run `i`. -/
def blk (r : List Bool) (i : ℕ) : List Bool :=
  (r.drop (i * A.prot.coins x.length)).take (A.prot.coins x.length)

/-- The completed runs, as a function of the coin blocks `b` they use: run `i` is the base
protocol played on block `b i` against the prover restricted to the transcript so far. -/
def prefixB (S : ProverStrategy) (b : ℕ → List Bool) : ℕ → Transcript
  | 0 => []
  | i + 1 =>
      prefixB S b i
        ++ A.prot.transcript (fun σ => S (prefixB S b i ++ σ)) x (b i) (A.prot.rounds x.length)

/-- The prover as the base protocol sees it in run `i`. -/
def runStrategy (S : ProverStrategy) (b : ℕ → List Bool) (i : ℕ) : ProverStrategy :=
  fun σ => S (A.prefixB x S b i ++ σ)

theorem prefixB_succ (S : ProverStrategy) (b : ℕ → List Bool) (i : ℕ) :
    A.prefixB x S b (i + 1)
      = A.prefixB x S b i
        ++ A.prot.transcript (A.runStrategy x S b i) x (b i) (A.prot.rounds x.length) := rfl

theorem prefixB_length (S : ProverStrategy) (b : ℕ → List Bool) :
    ∀ i, (A.prefixB x S b i).length = i * (2 * A.prot.rounds x.length)
  | 0 => by simp [prefixB]
  | i + 1 => by
      rw [prefixB_succ, List.length_append, prefixB_length S b i, Protocol.transcript_length]
      ring

/-- **A run depends only on the blocks before it.** -/
theorem prefixB_congr (S : ProverStrategy) {b b' : ℕ → List Bool} :
    ∀ i, (∀ j, j < i → b j = b' j) → A.prefixB x S b i = A.prefixB x S b' i
  | 0, _ => rfl
  | i + 1, h => by
      have ih := prefixB_congr S i fun j hj => h j (by omega)
      rw [prefixB_succ, prefixB_succ]
      unfold runStrategy
      rw [ih, h i (by omega)]

theorem runStrategy_congr (S : ProverStrategy) {b b' : ℕ → List Bool} (i : ℕ)
    (h : ∀ j, j < i → b j = b' j) : A.runStrategy x S b i = A.runStrategy x S b' i := by
  funext σ
  rw [runStrategy, runStrategy, A.prefixB_congr x S i h]

theorem runStrategy_bounded {S : ProverStrategy} (hS : S.Bounded (A.prot.msgLen x.length))
    (b : ℕ → List Bool) (i : ℕ) : (A.runStrategy x S b i).Bounded (A.prot.msgLen x.length) :=
  fun _ => hS _

/-- A later prefix extends an earlier one. -/
theorem prefixB_mono (S : ProverStrategy) (b : ℕ → List Bool) (i : ℕ) :
    ∀ j, i ≤ j → ∃ s : Transcript, A.prefixB x S b j = A.prefixB x S b i ++ s
  | 0, h => ⟨[], by rw [Nat.le_zero.mp h]; simp⟩
  | j + 1, h => by
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · obtain ⟨s, hs⟩ := prefixB_mono S b i j (by omega)
        exact ⟨s ++ A.prot.transcript (A.runStrategy x S b j) x (b j) (A.prot.rounds x.length),
          by rw [prefixB_succ, hs, List.append_assoc]⟩
      · have : i = j + 1 := by omega
        subst this
        exact ⟨[], by simp⟩

/-- Run `i` of a longer prefix, read off by position. -/
theorem prefixB_drop_take (S : ProverStrategy) (b : ℕ → List Bool) {i K : ℕ} (hi : i < K) :
    ((A.prefixB x S b K).drop (i * (A.prot.rounds x.length * 2))).take
        (A.prot.rounds x.length * 2)
      = A.prot.transcript (A.runStrategy x S b i) x (b i) (A.prot.rounds x.length) := by
  obtain ⟨s, hs⟩ := A.prefixB_mono x S b (i + 1) K hi
  rw [hs, prefixB_succ, List.append_assoc,
    show i * (A.prot.rounds x.length * 2) = (A.prefixB x S b i).length by
      rw [prefixB_length]; ring,
    List.drop_left, List.take_left' (by rw [Protocol.transcript_length]; ring)]

/-! ## The repeated transcript, run by run -/

/-- **The repeated transcript, run by run**: after `i` runs and `m` further rounds, the completed
runs followed by a partial base transcript. -/
theorem transcript_eq (K : ℕ) (S : ProverStrategy) (r : List Bool) :
    ∀ (i m : ℕ), m ≤ A.prot.rounds x.length →
      (A.repeatProtocol K).transcript S x r (i * A.prot.rounds x.length + m)
        = A.prefixB x S (A.blk x r) i
          ++ A.prot.transcript (A.runStrategy x S (A.blk x r) i) x (A.blk x r i) m
  | 0, 0, _ => by
      rw [Nat.zero_mul, Nat.add_zero]
      rfl
  | i + 1, 0, _ => by
      rw [Nat.add_zero, Nat.succ_mul, transcript_eq K S r i (A.prot.rounds x.length) le_rfl,
        prefixB_succ, show A.prot.transcript _ x _ 0 = [] from rfl, List.append_nil]
  | i, m + 1, hm => by
      have ih := transcript_eq K S r i m (by omega)
      rw [← Nat.add_assoc, Protocol.transcript_succ, ih, Protocol.transcript_succ]
      set R := A.prot.rounds x.length with hR
      have hRpos : 0 < R := by omega
      set σ := A.prot.transcript (A.runStrategy x S (A.blk x r) i) x (A.blk x r i) m with hσ
      have hlen : (A.prefixB x S (A.blk x r) i ++ σ).length = i * (2 * R) + 2 * m := by
        rw [List.length_append, prefixB_length, Protocol.transcript_length]
      have hdiv : (A.prefixB x S (A.blk x r) i ++ σ).length / (R * 2) = i := by
        rw [hlen]
        exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
      have hv : (A.repeatProtocol K).vmsg (Protocol.view x r (A.prefixB x S (A.blk x r) i ++ σ))
          = A.prot.vmsg (Protocol.view x (A.blk x r i) σ) := by
        show A.repVmsg (protocolView x r _) = _
        rw [A.repVmsg_view x r _ (by rw [← A.rounds_eq]; exact hRpos), ← A.rounds_eq,
          ← A.coins_eq, hdiv]
        congr 2
        rw [show i * (R * 2) = (A.prefixB x S (A.blk x r) i).length by
          rw [prefixB_length]; ring, List.drop_left]
      rw [hv, List.append_assoc]
      simp only [runStrategy, List.append_assoc]

/-- The whole interaction: `K` completed runs. -/
theorem transcript_rounds (K : ℕ) (S : ProverStrategy) (r : List Bool) :
    (A.repeatProtocol K).transcript S x r ((A.repeatProtocol K).rounds x.length)
      = A.prefixB x S (A.blk x r) K := by
  rw [repeatProtocol_rounds, ← Nat.add_zero (K * A.prot.rounds x.length),
    A.transcript_eq x K S r K 0 (Nat.zero_le _), show A.prot.transcript _ x _ 0 = [] from rfl,
    List.append_nil]

open Classical in
/-- **Acceptance is a majority of accepted runs.** -/
theorem accepts_iff (K : ℕ) (S : ProverStrategy) (r : List Bool) :
    (A.repeatProtocol K).Accepts S x r
      ↔ K + 1 ≤ 2 * ((Finset.range K).filter fun i =>
          A.prot.Accepts (A.runStrategy x S (A.blk x r) i) x (A.blk x r i)).card := by
  rw [Protocol.Accepts, transcript_rounds]
  show protocolView x r _ ∈ A.repVerdict K ↔ _
  rw [A.mem_repVerdict_view K x r _ (by
    rw [prefixB_length, ← A.rounds_eq]; ring_nf; exact le_refl _)]
  simp only [← A.rounds_eq, ← A.coins_eq]
  have hfilt : ∀ i ∈ Finset.range K,
      (A.g (protocolView x
          ((r.drop (i * A.prot.coins x.length)).take (A.prot.coins x.length))
          (((A.prefixB x S (A.blk x r) K).drop (i * (A.prot.rounds x.length * 2))).take
            (A.prot.rounds x.length * 2))) = true
        ↔ A.prot.Accepts (A.runStrategy x S (A.blk x r) i) x (A.blk x r i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [A.prefixB_drop_take x S (A.blk x r) hi, ← A.g_spec]
    rfl
  rw [Finset.filter_congr hfilt]

end RepArgs

end Complexity
