/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SuccStepTriple
public import Complexitylib.Models.TuringMachine.Subroutines.GuessCheck

/-!
# A stage that writes any code family

⚠️ Unreviewed by Bolton

A walk's stages write the two code tuples they swap, but an enclosing loop needs to write the
others too — the code it is testing, and the last member it guessed. The layout numbers the
families (`Complexity.WalkLayout.famIdx`), so one stage serves them all: this file repeats the
walk's layout facts for a stage that writes family `f`, and then packages the stage itself as
`Complexity.famStepTM`, parameterized by the check it runs.

## Main definitions

- `stepRegF`, `stepCellsF` — where a family-`f` stage guesses, and what it leaves
- `famStepTM` — guess family `f` and run a scan

## Main results

- `stepRegF_inj`, `head_guessBlocksTapesF_le`, `scanOkF_of_step`, `scanTapeF_of_step_any` — the
  layout obligations of `Complexity.TM.guessCheckTM_hoareTime`
- `stepCellsF_fam` — such a stage leaves every other family alone
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}

/-! ## Running two machines in sequence

The stage contracts are runs from named tapes rather than Hoare triples, because what a stage
leaves depends on the tapes it started from. This is the glue that chains two such runs; it
belongs upstream with `Complexity.TM.seqTM`. -/

/-- **Two contracts of the same machine hold together.** A machine is deterministic, so the two
runs are the same run; this is what lets an invariant be assembled from separately proved parts.
It belongs upstream with `Complexity.TM.HoareTime`. -/
theorem TM.HoareTime.and {n : ℕ} {M : TM n} {p₁ q₁ p₂ q₂ : TM.TapePred n} {b : ℕ}
    (h₁ : M.HoareTime p₁ q₁ b) (h₂ : M.HoareTime p₂ q₂ b) :
    M.HoareTime (fun i w o => p₁ i w o ∧ p₂ i w o) (fun i w o => q₁ i w o ∧ q₂ i w o) b := by
  intro inp work out hpre
  obtain ⟨c₁, t₁, ht₁, hr₁, hh₁, hq₁⟩ := h₁ inp work out hpre.1
  obtain ⟨c₂, t₂, ht₂, hr₂, hh₂, hq₂⟩ := h₂ inp work out hpre.2
  have hc : c₁ = c₂ := TM.reachesIn_halted_unique hr₁ hr₂ hh₁ hh₂
  subst hc
  exact ⟨c₁, t₁, ht₁, hr₁, hh₁, hq₁, hq₂⟩

theorem seqTM_run_of_runs {n : ℕ} (M₁ M₂ : TM n) (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    {c₁ : Cfg n M₁.Q} {t₁ : ℕ} (hreach₁ : M₁.reachesIn t₁ ⟨M₁.qstart, inp₀, W₀, out₀⟩ c₁)
    (hhalt₁ : M₁.halted c₁)
    {c₂ : Cfg n M₂.Q} {t₂ : ℕ}
    (hreach₂ : M₂.reachesIn t₂ ⟨M₂.qstart, TM.transitionInput c₁.input,
      (fun i => TM.transitionTape (c₁.work i)), TM.transitionTape c₁.output⟩ c₂)
    (hhalt₂ : M₂.halted c₂) :
    ∃ c : Cfg n (TM.seqTM M₁ M₂).Q,
      (TM.seqTM M₁ M₂).reachesIn (t₁ + 1 + t₂) ⟨(TM.seqTM M₁ M₂).qstart, inp₀, W₀, out₀⟩ c ∧
      (TM.seqTM M₁ M₂).halted c ∧
      c.input = c₂.input ∧ c.work = c₂.work ∧ c.output = c₂.output := by
  refine ⟨TM.phase2Wrap M₁ M₂ c₂, ?_, ?_, rfl, rfl, rfl⟩
  · convert TM.seqTM_reachesIn_of_reachesIn M₁ M₂ hreach₁ hhalt₁ hreach₂ using 1
  · rw [TM.phase2Wrap_halted_iff]
    exact hhalt₂

/-! ## Where a family stage guesses -/

/-- **The tape a stage writing family `f` puts its `p`-th block on.** -/
def stepRegF (L : WalkWidths kk jj tm nn S wc) (f p : ℕ) : Fin (jj + 2 + r + 1) :=
  walkReg (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF f p))

/-- A walk's own stages are the cases `f = 0` and `f = 1`. -/
theorem stepReg_eq_stepRegF (L : WalkWidths kk jj tm nn S wc) (second : Bool) (p : ℕ) :
    (stepReg (r := r) L second p) = stepRegF L (if second then 0 else 1) p := by
  rw [stepReg, stepRegF, L.toWalkLayout.stepIdx_eq_stepIdxF]

/-- A scratch block keeps its own register. -/
theorem stepRegF_scratch (L : WalkWidths kk jj tm nn S wc) (f p : ℕ)
    (hp : p < L.toWalkLayout.scratch) :
    (stepRegF (r := r) L f p : Fin (jj + 2 + r + 1)) = walkReg (L.toWalkLayout.reg p) := by
  rw [stepRegF, WalkLayout.stepIdxF, if_pos hp]

/-- Past the scratch, it writes the family's own tuple. -/
theorem stepRegF_fam (L : WalkWidths kk jj tm nn S wc) (f p : ℕ) :
    (stepRegF (r := r) L f (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1))
      = walkReg (L.toWalkLayout.reg (L.toWalkLayout.famIdx f p)) := by
  rw [stepRegF, L.toWalkLayout.stepIdxF_fam]

theorem stepRegF_ne_natAdd (L : WalkWidths kk jj tm nn S wc) (f p : ℕ) (c : Fin r) :
    stepRegF (r := r) L f p ≠ (Fin.natAdd (jj + 2) c).castSucc := by
  intro hc
  have hv := congrArg Fin.val hc
  rw [stepRegF, val_walkReg, val_natAdd_castSucc] at hv
  have := (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF f p)).isLt
  omega

theorem stepRegF_ne_last (L : WalkWidths kk jj tm nn S wc) (f p : ℕ) :
    stepRegF (r := r) L f p ≠ Fin.last (jj + 2 + r) :=
  walkReg_ne_last _

theorem stepRegF_inj (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) :
    ∀ p q, p < L.toWalkLayout.stepBlocks → q < L.toWalkLayout.stepBlocks →
      (stepRegF (r := r) L f p : Fin (jj + 2 + r + 1)) = stepRegF L f q → p = q := by
  intro p q hp hq h
  have hidx := walkReg_reg_inj (r := r) L _ _ (L.toWalkLayout.stepIdxF_lt f p hf hp)
    (L.toWalkLayout.stepIdxF_lt f q hf hq) h
  exact L.toWalkLayout.stepIdxF_inj f p q hp hq hidx

/-! ## The obligations of a guess stage -/

theorem head_guessBlocksTapesF_le (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head)
    (hone : ∀ i : Fin (jj + 2), (W₀ (Fin.castAdd r i).castSucc).head = 1)
    (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B) :
    ∀ i ∈ stepTargets jj r,
      (TM.guessBlocksTapes (stepRegF (r := r) L f) (stepWidth L)
        L.toWalkLayout.stepBlocks W₀ i.castSucc).head ≤ B := by
  classical
  intro i hi
  rw [stepTargets, List.mem_map] at hi
  obtain ⟨i, -, rfl⟩ := hi
  obtain ⟨-, -, -, huntouched, hblk⟩ :=
    TM.guessBlocksTapes_spec (stepRegF (r := r) L f) (stepRegF_ne_last L f)
      (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinv hh (stepRegF_inj L f hf)
  by_cases hex : ∃ p, p < L.toWalkLayout.stepBlocks ∧
      stepRegF (r := r) L f p = (Fin.castAdd r i).castSucc
  · obtain ⟨p, hp, hpi⟩ := hex
    have hhead := (hblk p hp).1
    rw [hpi] at hhead
    rw [hhead, hone i]
    have := hB p hp
    omega
  · rw [huntouched (Fin.castAdd r i).castSucc (by
      intro hc
      exact absurd (congrArg Fin.val hc) (by
        have h1 : ((Fin.castAdd r i).castSucc : Fin (jj + 2 + r + 1)).val = i.val := rfl
        have h2 : (Fin.last (jj + 2 + r) : Fin (jj + 2 + r + 1)).val = jj + 2 + r := rfl
        have := i.isLt
        omega))
      (fun p hp hc => hex ⟨p, hp, hc.symm⟩), hone i]
    exact hB1

theorem scanOkF_of_step (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W₀ i).StartInvariant) (hh : ∀ i, 1 ≤ (W₀ i).head) (inp₀ out₀ : Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant) :
    TM.ScanOk (TM.parkTape inp₀)
      (⟨1, (TM.guessBlocksTapes (stepRegF (r := r) L f) (stepWidth L)
        L.toWalkLayout.stepBlocks W₀ (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape)
      (TM.parkTape out₀) where
  inp := read_parkTape_ne_start hinpSI
  res := by
    have hSI := (TM.guessBlocksTapes_spec (stepRegF (r := r) L f) (stepRegF_ne_last L f)
      (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinv hh (stepRegF_inj L f hf)).1
      (Fin.castAdd r (Fin.last (jj + 1))).castSucc
    exact hSI.2 1 le_rfl
  out := read_parkTape_ne_start houtSI

/-! ## What such a stage leaves -/

/-- **The registers a family-`f` stage leaves behind.** -/
noncomputable def stepCellsF (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) : Fin (jj + 1) → ℕ → Γ :=
  fun i q => (TM.guessBlocksTapes (stepRegF L f) (stepWidth L)
    L.toWalkLayout.stepBlocks W (walkReg i)).cells q

theorem stepCells_eq_stepCellsF (L : WalkWidths kk jj tm nn S wc) (second : Bool)
    (W : Fin (jj + 2 + r + 1) → Tape) :
    stepCells L second W = stepCellsF L (if second then 0 else 1) W := by
  funext i q
  show (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
      L.toWalkLayout.stepBlocks W (walkReg i)).cells q = _
  rw [show (stepReg (r := r) L second : ℕ → Fin (jj + 2 + r + 1))
    = stepRegF L (if second then 0 else 1) from funext (stepReg_eq_stepRegF L second)]
  rfl

/-- **A register no block of the stage is guessed into keeps what it held.** -/
theorem stepCellsF_retained (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (i : Fin (jj + 1))
    (hne : ∀ p, p < L.toWalkLayout.stepBlocks →
      (walkReg i : Fin (jj + 2 + r + 1)) ≠ stepRegF L f p) :
    stepCellsF L f W i = (W (walkReg i)).cells := by
  have h := (TM.guessBlocksTapes_spec (stepRegF (r := r) L f)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (stepRegF_inj L f hf)).2.2.2.1 (walkReg i) (walkReg_ne_last i) hne
  funext q
  show (TM.guessBlocksTapes (stepRegF L f) (stepWidth L)
    L.toWalkLayout.stepBlocks W (walkReg i)).cells q = _
  rw [h]

/-- **And so every other family survives the stage.** -/
theorem stepCellsF_fam (L : WalkWidths kk jj tm nn S wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares)
    (hff : f ≠ f') (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (p : ℕ) (hp : p < kk + 3) :
    stepCellsF L f W (L.toWalkLayout.reg (L.toWalkLayout.famIdx f' p))
      = (W (walkReg (L.toWalkLayout.reg (L.toWalkLayout.famIdx f' p)))).cells := by
  refine stepCellsF_retained L f hf W hinv hh _ (fun p' hp' hc => ?_)
  refine L.toWalkLayout.stepIdxF_ne_famIdx f f' p' p hp' hp hff ?_
  refine L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdxF_lt f p' hf hp')
    (?_ : L.toWalkLayout.famIdx f' p < L.toWalkLayout.blocks) (walkReg_inj hc).symm
  have hb : L.toWalkLayout.blocks
      = L.toWalkLayout.scratch + (2 + L.toWalkLayout.spares) * (kk + 3) := by
    have he : (2 + L.toWalkLayout.spares) * (kk + 3)
        = (kk + 3) + (kk + 3) + L.toWalkLayout.spares * (kk + 3) := by ring
    rw [L.toWalkLayout.blocks_eq]
    omega
  have hmul : (f' + 1) * (kk + 3) ≤ (2 + L.toWalkLayout.spares) * (kk + 3) :=
    Nat.mul_le_mul_right _ (by omega)
  have he : (f' + 1) * (kk + 3) = f' * (kk + 3) + (kk + 3) := by ring
  rw [WalkLayout.famIdx, hb]
  omega

/-- **The guess tape has moved on by exactly one stage.** -/
theorem guessFromF_after_step (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (g : ℕ → Bool) (s : ℕ)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    TM.GuessFrom
      (fun q => g ((s + 1) * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (TM.guessBlocksTapes (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks W
        (Fin.last (jj + 2 + r))) := by
  have h := TM.guessFrom_after (stepRegF (r := r) L f) (fun p => walkReg_ne_last _)
    (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh (stepRegF_inj L f hf) _ hgf
  intro q
  have hq := h q
  rw [hq]
  refine congrArg Γ.ofBool (congrArg g ?_)
  rw [Nat.succ_mul]
  omega

/-- **The blocks such a stage guesses hold the certificate's bits.** -/
theorem holdsBits_blockF_of_step (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks b g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepRegF L f p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.stepBlocks) (bits : List Bool)
    (hbits : ∀ q, (hq : q < bits.length) → b s p q = bits[q])
    (hlen : bits.length ≤ stepWidth L p + 1) :
    HoldsBits (fun c i =>
      (TM.guessBlocksTapes (stepRegF L f) (stepWidth L)
        L.toWalkLayout.stepBlocks W i).cells c) 0 (stepRegF L f p) bits := by
  have hbits' := holdsBits_of_guessBlocks (stepRegF (r := r) L f)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (stepRegF_inj L f hf) hr1 (b s) (TM.blocks_of_stageBlocks hs s hgf)
  exact (hbits' p hp).of_isPrefix (isPrefix_ofFn _ hlen hbits)

/-- **And so does every scratch register**, at whatever width the check reads it. -/
theorem exists_bits_scratchF (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepRegF L f p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.scratch) (n : ℕ) (hn : n ≤ stepWidth L p + 1) :
    ∃ bits : List Bool, bits.length = n ∧
      HoldsBits (fun q i => stepCellsF L f W i q) 0 (L.toWalkLayout.reg p) bits := by
  classical
  refine ⟨(List.ofFn fun q : Fin (stepWidth L p + 1) =>
      streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s p q.val).take n, ?_, ?_⟩
  · rw [List.length_take, List.length_ofFn]
    omega
  · have h := holdsBits_blockF_of_step x L f hf
      (streamCert (stepWidth L) L.toWalkLayout.stepBlocks g)
      g (stageBlocks_streamCert _ _ _) s W hinv hh hr1 hgf p
      (by rw [WalkLayout.stepBlocks]; omega)
      (List.ofFn fun q : Fin (stepWidth L p + 1) =>
        streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s p q.val)
      (fun q hq => by rw [List.getElem_ofFn]) (by rw [List.length_ofFn])
    rw [stepRegF_scratch L f p hp] at h
    exact h.of_isPrefix (List.take_prefix _ _)

/-- **The scan is well formed whatever the guess wrote.** -/
theorem scanTapeF_of_step_any (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepRegF L f p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hblank : (W (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank) :
    TM.ScanTape (stepCellsF L f W) (walkScanLen tm x.length S) := by
  classical
  have hlt : L.toWalkLayout.rulerIdx < L.toWalkLayout.stepBlocks := by
    rw [WalkLayout.stepBlocks]
    have := L.toWalkLayout.ruler_scratch
    omega
  obtain ⟨ginv, -, -, -, -⟩ := TM.guessBlocksTapes_spec (stepRegF (r := r) L f)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (stepRegF_inj L f hf)
  obtain ⟨bits, hlen, hbits⟩ := exists_bits_scratchF x L f hf g s W hinv hh hr1 hgf
    L.toWalkLayout.rulerIdx L.toWalkLayout.ruler_scratch (walkScanLen tm x.length S)
    (by rw [stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
        have := one_le_walkScanLen tm x.length S
        omega)
  refine ⟨fun i => (ginv (walkReg i)).1, fun i q hq => (ginv (walkReg i)).2 q hq,
    fun q h1 h2 => ?_, ?_⟩
  · rw [← L.toWalkLayout.ruler_zero]
    have hc := hbits (q - 1) (by rw [hlen]; omega)
    rw [show 0 + (q - 1) + 1 = q by omega] at hc
    have hc' : stepCellsF L f W (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) q
        = Γ.ofBool (bits[q - 1]'(by rw [hlen]; omega)) := hc
    show stepCellsF L f W (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) q ≠ Γ.blank
    rw [hc']
    cases bits[q - 1]'(by rw [hlen]; omega) <;> exact fun hz => Γ.noConfusion hz
  · have hbeyond := TM.guessBlocksTapes_beyond (stepRegF (r := r) L f)
      (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
      (stepRegF_inj L f hf) L.toWalkLayout.rulerIdx hlt (walkScanLen tm x.length S + 1) ?_
    · rw [← L.toWalkLayout.ruler_zero]
      show (TM.guessBlocksTapes (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks W
        (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = _
      rw [← stepRegF_scratch L f _ L.toWalkLayout.ruler_scratch, hbeyond,
        stepRegF_scratch L f _ L.toWalkLayout.ruler_scratch, hblank]
    · rw [hr1 _ hlt, stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
      have := one_le_walkScanLen tm x.length S
      omega

/-- **The third tuple is family two**, the first of the spares. -/
theorem codeT_eq_famIdx (L : WalkWidths kk jj tm nn S wc) (p : ℕ) (hp : p < kk + 3) :
    L.toWalkLayout.codeT p = L.toWalkLayout.reg (L.toWalkLayout.famIdx 2 p) := by
  rw [WalkLayout.codeT, L.toWalkLayout.famIdx_spare 0 p L.toWalkLayout.spares_pos hp]
  rfl

/-- **A stage leaves every spare tuple it does not write where it was.** -/
theorem stepCellsF_spare (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (n : ℕ) (hn : n < L.toWalkLayout.spares)
    (hne : f ≠ 2 + n) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (p : ℕ) (hp : p < kk + 3) :
    stepCellsF L f W (L.toWalkLayout.spareReg n p)
      = (W (walkReg (L.toWalkLayout.spareReg n p))).cells := by
  rw [← L.toWalkLayout.famReg_spare n p hn hp]
  exact stepCellsF_fam L f (2 + n) hf (by omega) hne W hinv hh p hp

/-- **A stage that writes another family leaves the third tuple where it was.** -/
theorem stepCellsF_codeT (L : WalkWidths kk jj tm nn S wc) (f : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf2 : f ≠ 2) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (p : ℕ) (hp : p < kk + 3) :
    stepCellsF L f W (L.toWalkLayout.codeT p)
      = (W (walkReg (L.toWalkLayout.codeT p))).cells := by
  have h2 : (2 : ℕ) < 2 + L.toWalkLayout.spares := by
    have := L.toWalkLayout.spares_pos
    omega
  rw [codeT_eq_famIdx L p hp]
  exact stepCellsF_fam L f 2 hf h2 hf2 W hinv hh p hp

/-- **A stage leaves every other family's blocks where they were.** -/
theorem stepCellsF_famReg (L : WalkWidths kk jj tm nn S wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (p : ℕ) (hp : p < kk + 3) :
    stepCellsF L f W (L.toWalkLayout.famReg f' p)
      = (W (walkReg (L.toWalkLayout.famReg f' p))).cells :=
  stepCellsF_fam L f f' hf hf' hne W hinv hh p hp

/-- **And so a code another family holds survives the stage.** -/
theorem holdsCodeTail_famReg_survives {S' : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S' wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (a : Code tm.Q kk x.length S')
    (ha : HoldsCodeTail tm x S' (fun q i => (W (walkReg i)).cells q)
      (L.toWalkLayout.famReg f') a) :
    HoldsCodeTail tm x S' (fun q i => stepCellsF L f W i q) (L.toWalkLayout.famReg f') a :=
  holdsCodeTail_congr tm x S' _ _ (L.toWalkLayout.famReg f') a ha
    (fun p hp q => congrFun (stepCellsF_famReg L f f' hf hf' hne W hinv hh p hp) q)

/-- **The blocks another family holds survive the stage.** This is the form the scans want; the
family's registers are given by name, so a caller may use whatever name it has for them. -/
theorem holdsBlocks_survives {S' : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S' wc) (f f' : ℕ)
    (hf : f < 2 + L.toWalkLayout.spares) (hf' : f' < 2 + L.toWalkLayout.spares) (hne : f ≠ f')
    (c : ℕ → Fin (jj + 1)) (hc : ∀ p, p < kk + 3 → c p = L.toWalkLayout.famReg f' p)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head) (a : Code tm.Q kk x.length S')
    (ha : ∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0
      (c p) (codeBlockScan tm x S' a p)) :
    ∀ p, p < kk + 3 → HoldsBits (fun q i => stepCellsF L f W i q) 0
      (c p) (codeBlockScan tm x S' a p) := by
  intro p hp q hq
  rw [hc p hp]
  show stepCellsF L f W (L.toWalkLayout.famReg f' p) (0 + q + 1) = _
  rw [congrFun (stepCellsF_famReg L f f' hf hf' hne W hinv hh p hp) (0 + q + 1)]
  have := ha p hp q hq
  rw [hc p hp] at this
  exact this

/-- **The registers a stage guesses into hold blocks of the stream's own bits.** -/
theorem exists_bits_guessedF (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepRegF L f p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∃ bits : ℕ → List Bool,
      (∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p) ∧
      ∀ p, p < kk + 3 → HoldsBits (fun q i => stepCellsF L f W i q) 0
        (L.toWalkLayout.famReg f p) (bits p) := by
  classical
  refine ⟨fun p => (List.ofFn fun q : Fin (stepWidth L (L.toWalkLayout.scratch + p) + 1) =>
      streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s
        (L.toWalkLayout.scratch + p) q.val).take (blockLen tm x.length S p),
    fun p hp => ?_, fun p hp => ?_⟩
  · rw [List.length_take, List.length_ofFn, stepWidth_code L p hp]
    have := blockLen_le_codeWidthScan tm x.length S p
    omega
  · have h := holdsBits_blockF_of_step x L f hf
      (streamCert (stepWidth L) L.toWalkLayout.stepBlocks g)
      g (stageBlocks_streamCert _ _ _) s W hinv hh hr1 hgf (L.toWalkLayout.scratch + p)
      (by rw [WalkLayout.stepBlocks]; omega)
      (List.ofFn fun q : Fin (stepWidth L (L.toWalkLayout.scratch + p) + 1) =>
        streamCert (stepWidth L) L.toWalkLayout.stepBlocks g s
          (L.toWalkLayout.scratch + p) q.val)
      (fun q hq => by rw [List.getElem_ofFn]) (by rw [List.length_ofFn])
    rw [show (stepRegF L f (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1))
      = walkReg (L.toWalkLayout.famReg f p) by rw [stepRegF_fam]; rfl] at h
    exact h.of_isPrefix (List.take_prefix _ _)

/-! ## The stage itself -/

/-- **A stage that guesses code family `f` and runs a check.** -/
noncomputable def famStepTM {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (D : TM (jj + 2))
    (f : ℕ) (cc : Fin rr) : TM (jj + 2 + rr + 1) :=
  TM.guessThenCheckTM rr D (stepRegF (r := rr) L f) (stepWidth L) L.toWalkLayout.stepBlocks
    (stepTargets jj rr) (auxIdx jj cc)

/-- Its advancing states. -/
noncomputable def famStepAdv {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (D : TM (jj + 2))
    (f : ℕ) (cc : Fin rr) : (famStepTM L D f cc).Q → Bool :=
  TM.guessThenCheckAdv rr D (stepRegF (r := rr) L f) (stepWidth L) L.toWalkLayout.stepBlocks
    (stepTargets jj rr) (auxIdx jj cc)

/-- **It respects the guess protocol.** -/
theorem guessProtocol_famStepTM {rr : ℕ} (L : WalkWidths kk jj tm nn S wc) (D : TM (jj + 2))
    (f : ℕ) (cc : Fin rr) : TM.GuessProtocol (famStepTM L D f cc) (famStepAdv L D f cc) :=
  TM.guessProtocol_guessThenCheckTM rr _ _ _ _ _ _ (auxIdx_ne_last cc)

/-- How long such a stage runs. -/
noncomputable def famTime (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (rr B : ℕ) :
    ℕ :=
  TM.guessBlocksTime (stepWidth L) L.toWalkLayout.stepBlocks + 1 +
    (1 + 1 + ((stepTargets jj rr).length * (B + 3) + 1)) + 1 +
    (2 * walkScanLen tm x.length S + 3 + 1 + 1)

/-- **What such a stage does, with the check left open.** Whatever the guess was, the stage runs
and leaves the tapes fit for the next one, with the registers holding what the check left; the
accumulator keeps its bit exactly when the check accepts. -/
theorem famThenStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (D : TM (jj + 2))
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (cells' : Fin (jj + 1) → ℕ → Γ) (v : Bool) (bD : ℕ)
    (hcells' : ∀ i : Fin (jj + 1), (⟨1, cells' i⟩ : Tape).StartInvariant)
    (hruler : cells' (L.toWalkLayout.reg L.toWalkLayout.rulerIdx)
      (walkScanLen tm x.length S + 1) = Γ.blank)
    (hD : D.HoareTime
      (fun inp work out => inp = TM.parkTape inp₀ ∧ out = TM.parkTape out₀ ∧
        work = Fin.snoc (fun i : Fin (jj + 1) => (⟨1, (TM.guessBlocksTapes (stepRegF L f)
            (stepWidth L) L.toWalkLayout.stepBlocks W₀
            (Fin.castAdd r i.castSucc).castSucc).cells⟩ : Tape))
          (⟨1, (TM.guessBlocksTapes (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks W₀
            (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape))
      (fun inp work out => inp = TM.parkTape inp₀ ∧ out = TM.parkTape out₀ ∧
        work = Fin.snoc (fun i : Fin (jj + 1) => (⟨1, cells' i⟩ : Tape))
          ((⟨1, (TM.guessBlocksTapes (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks W₀
            (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool v)))
      bD) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (famStepTM L D f cc).Q) (t : ℕ),
      t ≤ TM.guessBlocksTime (stepWidth L) L.toWalkLayout.stepBlocks + 1 +
        (1 + 1 + ((stepTargets jj r).length * (B + 3) + 1)) + 1 + (bD + 1 + 1) ∧
      (famStepTM L D f cc).reachesIn t
        ⟨(famStepTM L D f cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L D f cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa
        (fun p q => cells' (L.toWalkLayout.codeT p) q)
        c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      (∀ i : Fin (jj + 1), c'.work (walkReg i) = (⟨1, cells' i⟩ : Tape)) ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧ v = true) ∧
      (v = true → ∀ b : Bool, (W₀ (auxIdx jj cc)).read = Γ.ofBool b →
          (c'.work (auxIdx jj cc)).read = Γ.ofBool b) := by
  classical
  obtain ⟨hframe, hinvW, hhW, hone, hblank, hinpCells, hinpHead, houtSI, houth, hgf, -⟩ :=
    htapes
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepRegF L f p)).head = 1 :=
    fun p _ => hone (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF f p)).castSucc
  have hinpSI : inp₀.StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [show inp₀.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from congrFun hinpCells 0]
      exact Tape.init_cells_zero _
    · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from congrFun hinpCells q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  have hinpRead : inp₀.read ≠ Γ.start := hinpSI.read_ne_start hinpHead
  have houtRead : out₀.read ≠ Γ.start := houtSI.2 _ houth
  obtain ⟨c', t, htle, hreach, hhalt, hlast, haux, hinp', hout', hregs, hacc'⟩ :=
    TM.guessThenCheck_hoareTime r D (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks
      (stepTargets jj r) (auxIdx jj cc)
      stepTargets_nodup (fun i => mem_stepTargets i) (fun c => natAdd_notMem_stepTargets c)
      (fun p c _ => stepRegF_ne_natAdd L f p c) (fun i => auxIdx_ne_castAdd cc i)
      (auxIdx_ne_last cc) (fun p => stepRegF_ne_last L f p) B hB1 inp₀ out₀ W₀ hinpSI
      houtSI hinpRead houtRead hinvW hhW (stepRegF_inj L f hf)
      (head_guessBlocksTapesF_le L f hf W₀ hinvW hhW hone B hB1 hB)
      cells' v bD hcells' hD inp₀ W₀ out₀ ⟨rfl, rfl, rfl⟩
  obtain ⟨ginv, ghh, -, -, -⟩ := TM.guessBlocksTapes_spec (stepRegF L f)
    (fun p => stepRegF_ne_last L f p) (stepWidth L) L.toWalkLayout.stepBlocks W₀ hinvW hhW
    (stepRegF_inj L f hf)
  have hread' : (c'.work (auxIdx jj cc)).read
      = (if v = true ∧ (W₀ (auxIdx jj cc)).read = Γ.one then Γ.one else Γ.zero) := by
    rw [hacc']
    show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _
      (W₀ (auxIdx jj cc)).head = _
    rw [Function.update_self]
  have hreg : ∀ i : Fin (jj + 1), c'.work (walkReg i)
      = (⟨1, cells' i⟩ : Tape) := by
    intro i
    have h := hregs i.castSucc
    rw [Fin.snoc_castSucc] at h
    exact h
  have hverdT : c'.work (Fin.castAdd r (Fin.last (jj + 1))).castSucc
      = (⟨1, (TM.guessBlocksTapes (stepRegF L f) (stepWidth L) L.toWalkLayout.stepBlocks W₀
          (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write (Γ.ofBool v) := by
    have h := hregs (Fin.last (jj + 1))
    rw [Fin.snoc_last] at h
    exact h
  have haccSI : (c'.work (auxIdx jj cc)).StartInvariant ∧ 1 ≤ (c'.work (auxIdx jj cc)).head := by
    have hh0 := hhW (auxIdx jj cc)
    rw [hacc']
    refine ⟨⟨?_, ?_⟩, hh0⟩
    · show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ 0 = Γ.start
      rw [Function.update_of_ne (by omega)]
      exact (hinvW (auxIdx jj cc)).1
    · intro q hq
      show Function.update (W₀ (auxIdx jj cc)).cells (W₀ (auxIdx jj cc)).head _ q ≠ Γ.start
      by_cases hqh : q = (W₀ (auxIdx jj cc)).head
      · rw [hqh, Function.update_self]
        split_ifs
        all_goals exact fun hc => Γ.noConfusion hc
      · rw [Function.update_of_ne hqh]
        exact (hinvW (auxIdx jj cc)).2 q hq
  have hallSI : ∀ i : Fin (jj + 2 + r + 1),
      (c'.work i).StartInvariant ∧ 1 ≤ (c'.work i).head := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hlast]
      exact ⟨ginv _, ghh _⟩
    · refine Fin.addCases (fun i' => ?_) (fun c => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) i'
        · have hSI : (⟨1, (TM.guessBlocksTapes (stepRegF L f) (stepWidth L)
                L.toWalkLayout.stepBlocks W₀
                (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).StartInvariant :=
            ginv (Fin.castAdd r (Fin.last (jj + 1))).castSucc
          rw [hverdT]
          refine ⟨?_, ?_⟩
          · rw [← Γw.ofBool_toΓ]
            exact hSI.write (Γw.ofBool v)
          · rw [Tape.write_head]
        · show (c'.work (walkReg j)).StartInvariant ∧ 1 ≤ (c'.work (walkReg j)).head
          rw [hreg j]
          exact ⟨hcells' j, le_rfl⟩
      · by_cases hcc : c = cc
        · subst hcc
          exact haccSI
        · rw [haux c (fun hc => hcc (Fin.ext (by
            have hv := congrArg Fin.val hc
            simp only [auxIdx, val_natAdd_castSucc] at hv
            omega)))]
          exact ⟨hinvW _, hhW _⟩
  refine ⟨c', t, htle, hreach, hhalt,
    ⟨fun c hc => ?_, fun i => (hallSI i).1, fun i => (hallSI i).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩, hinp', hreg, fun hone' => ?_, fun hv b hb => ?_⟩
  · show c'.work (Fin.natAdd (jj + 2) c).castSucc = Wa c
    rw [haux c (fun hcc => hc (Fin.ext (by
      have hv := congrArg Fin.val hcc
      simp only [auxIdx, val_natAdd_castSucc] at hv
      omega)))]
    exact hframe c hc
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hverdT, Tape.write_head]
    · show (c'.work (walkReg j)).head = 1
      rw [hreg j]
  · show (c'.work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = Γ.blank
    rw [hreg]
    exact hruler
  · rw [hinp']
    show (TM.parkTape inp₀).cells = _
    exact hinpCells
  · rw [hinp']
    show 1 ≤ max inp₀.head 1
    omega
  · rw [hout']
    exact houtSI
  · rw [hout']
    show 1 ≤ max out₀.head 1
    omega
  · rw [hlast]
    exact guessFromF_after_step L f hf W₀ hinvW hhW g s hgf
  · intro p hp q
    rw [hreg (L.toWalkLayout.codeT p)]
  · rw [hread'] at hone'
    have hv : v = true ∧ (W₀ (auxIdx jj cc)).read = Γ.one := by
      by_contra hc
      rw [if_neg hc] at hone'
      exact Γ.noConfusion hone'
    exact ⟨hv.2, hv.1⟩
  · rw [hread', hb]
    have hv' : v = true := hv
    cases b with
    | false =>
      rw [if_neg (fun hc => Γ.noConfusion hc.2)]
      rfl
    | true =>
      rw [if_pos ⟨hv', rfl⟩]
      rfl

/-- **What a scanner stage does.** The check is a two-pass scan, so what it leaves on the
registers is what the guess wrote, and the verdict is the scanner's. -/
theorem famStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (Sc : Scanner jj)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (B : ℕ)
    (hB1 : 1 ≤ B) (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (famStepTM L (TM.twoPassTM Sc) f cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM Sc) f cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM Sc) f cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM Sc) f cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa
        (fun p q => stepCellsF L f W₀ (L.toWalkLayout.codeT p) q)
        c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      (∀ i : Fin (jj + 1),
        c'.work (walkReg i) = (⟨1, stepCellsF L f W₀ i⟩ : Tape)) ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        Sc.emit (Sc.run (TM.scanCol (stepCellsF L f W₀)) (walkScanLen tm x.length S)) = true) ∧
      (Sc.emit (Sc.run (TM.scanCol (stepCellsF L f W₀)) (walkScanLen tm x.length S)) = true →
        ∀ b : Bool, (W₀ (auxIdx jj cc)).read = Γ.ofBool b →
          (c'.work (auxIdx jj cc)).read = Γ.ofBool b) := by
  have hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W₀ (stepRegF L f p)).head = 1 :=
    fun p _ => htapes.2.2.2.1 (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF f p)).castSucc
  have hscan := scanTapeF_of_step_any x L f hf g s W₀ htapes.2.1 htapes.2.2.1 hr1
    htapes.2.2.2.2.2.2.2.2.2.1 htapes.2.2.2.2.1
  have hinpSI : inp₀.StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [show inp₀.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
  exact famThenStep_run x L (TM.twoPassTM Sc) f hf g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
    (stepCellsF L f W₀)
    (Sc.emit (Sc.run (TM.scanCol (stepCellsF L f W₀)) (walkScanLen tm x.length S)))
    (2 * walkScanLen tm x.length S + 3)
    (fun i => ⟨hscan.start i, fun q hq => hscan.ne_start i q hq⟩)
    (by rw [L.toWalkLayout.ruler_zero]; exact hscan.blank)
    (TM.twoPassTM_hoareTime Sc (stepCellsF L f W₀) (walkScanLen tm x.length S)
      (TM.parkTape inp₀) (TM.parkTape out₀) _
      (scanOkF_of_step L f hf W₀ htapes.2.1 htapes.2.2.1 inp₀ out₀ hinpSI
        htapes.2.2.2.2.2.2.2.1) hscan)

/-- **A scanner stage carries the frame**, provided it does not write the tuple the frame
records. -/
theorem famStep_tapes (x : List Bool) (L : WalkWidths kk jj tm x.length S wc) (Sc : Scanner jj)
    (f : ℕ) (hf : f < 2 + L.toWalkLayout.spares) (hf2 : f ≠ 2) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) :
    (famStepTM L (TM.twoPassTM Sc) f cc).HoareTime
      (fun inp work out => WalkTapes (r := r) x L g s cc Wa Wt inp work out)
      (fun inp work out => WalkTapes (r := r) x L g (s + 1) cc Wa Wt inp work out)
      (famTime x L r B) := by
  intro inp₀ W₀ out₀ htapes
  obtain ⟨c', t, htle, hreach, hhalt, htapes', -, -, -, -⟩ :=
    famStep_run x L Sc f hf g s cc B hB1 hB Wa Wt inp₀ out₀ W₀ htapes
  refine ⟨c', t, htle, hreach, hhalt, ?_⟩
  refine ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
    htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
    htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => ?_⟩
  refine (htapes'.2.2.2.2.2.2.2.2.2.2 p hp q).trans ?_
  show stepCellsF L f W₀ (L.toWalkLayout.codeT p) q = Wt p q
  rw [congrFun (stepCellsF_codeT L f hf hf2 W₀ htapes.2.1 htapes.2.2.1 p hp) q]
  exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q

end Complexity
