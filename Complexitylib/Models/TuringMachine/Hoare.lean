import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.SeqInternal
import Complexitylib.Models.TuringMachine.Combinators.IfInternal
import Complexitylib.Models.TuringMachine.Combinators.LoopInternal

/-!
# Hoare-style composition rules for TM combinators

## Main results

- `seqTM_hoareTime` — sequential composition of Hoare triples
- `ifTM_rewind_full` — rewind loop for ifTM transition
- `ifTM_check_to_then` / `ifTM_check_to_else` — check step lemmas
-/

set_option linter.unusedSimpArgs false

namespace TM

variable {n : ℕ}

/-- **Sequential composition of Hoare triples**. -/
theorem seqTM_hoareTime (tm₁ tm₂ : TM n)
    {pre mid mid' post : TapePred n} {b₁ b₂ : ℕ}
    (h₁ : tm₁.HoareTime pre mid b₁)
    (h_trans : ∀ inp work out, mid inp work out →
        mid' (seqTransitionInput inp)
             (fun i => seqTransitionTape (work i))
             (seqTransitionTape out))
    (h₂ : tm₂.HoareTime mid' post b₂) :
    (seqTM tm₁ tm₂).HoareTime pre post (b₁ + 1 + b₂) := by
  intro inp work out hpre
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hmid⟩ := h₁ inp work out hpre
  have hmid' := h_trans c₁.input c₁.work c₁.output hmid
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hpost⟩ := h₂ _ _ _ hmid'
  refine ⟨phase2Wrap tm₁ tm₂ c₂, t₁ + 1 + t₂, ?_, ?_, ?_, ?_⟩
  · omega
  · convert seqTM_full_simulation tm₁ tm₂ hreach₁ hhalt₁ hreach₂ using 1
  · rw [phase2Wrap_halted]; exact hhalt₂
  · exact hpost

/-- Well-formedness condition on all tapes: cells 0 = start and cells ≥ 1 ≠ start. -/
def AllTapesWF (inp : Tape) (work : Fin n → Tape) (out : Tape) : Prop :=
  inp.cells 0 = Γ.start ∧ (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧
  (∀ i, (work i).cells 0 = Γ.start) ∧ (∀ i j, j ≥ 1 → (work i).cells j ≠ Γ.start) ∧
  out.cells 0 = Γ.start ∧ (∀ j, j ≥ 1 → out.cells j ≠ Γ.start)

-- ════════════════════════════════════════════════════════════════════════
-- Loop invariant rule
-- ════════════════════════════════════════════════════════════════════════

private theorem loopTM_hoareTime_aux (tmBody tmTest : TM n)
    {inv post : TapePred n} {b_iter : ℕ}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    (h_iter : ∀ inp work out, inv inp work out →
      (∃ c' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output)
      ∨
      (∃ inp' work' out' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        inv inp' work' out' ∧
        variant inp' work' out' < variant inp work out))
    (fuel : ℕ) :
    ∀ inp work out, inv inp work out → variant inp work out ≤ fuel →
      ∃ c' t, t ≤ (fuel + 1) * b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output := by
  induction fuel with
  | zero =>
    intro inp work out hinv hfuel
    cases h_iter inp work out hinv with
    | inl h =>
      obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h
      exact ⟨c', t, le_trans ht (by omega), hreach, hhalt, hpost⟩
    | inr h =>
      obtain ⟨_, _, _, _, _, _, _, hvar_dec⟩ := h
      omega
  | succ fuel ih =>
    intro inp work out hinv hfuel
    cases h_iter inp work out hinv with
    | inl h =>
      obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h
      refine ⟨c', t, le_trans ht ?_, hreach, hhalt, hpost⟩
      calc b_iter = 1 * b_iter := (Nat.one_mul _).symm
        _ ≤ (fuel + 1 + 1) * b_iter := Nat.mul_le_mul_right _ (by omega)
    | inr h =>
      obtain ⟨inp', work', out', t₁, ht₁, hreach₁, hinv', hvar_dec⟩ := h
      have hfuel' : variant inp' work' out' ≤ fuel := by omega
      obtain ⟨c', t₂, ht₂, hreach₂, hhalt, hpost⟩ := ih inp' work' out' hinv' hfuel'
      refine ⟨c', t₁ + t₂, ?_, reachesIn_trans _ hreach₁ hreach₂, hhalt, hpost⟩
      calc t₁ + t₂
          ≤ b_iter + (fuel + 1) * b_iter := Nat.add_le_add ht₁ ht₂
        _ = (fuel + 1) * b_iter + b_iter := Nat.add_comm _ _
        _ = (fuel + 1 + 1) * b_iter := (Nat.succ_mul _ _).symm

/-- **Loop invariant rule**. Each iteration (≤ `b_iter` steps) either halts with
    `post` or returns to the loop start with `inv` preserved and `variant` decreased.
    The `variant` is bounded by `k` under `inv`, giving total time `(k + 1) * b_iter`. -/
theorem loopTM_hoareTime (tmBody tmTest : TM n)
    {inv post : TapePred n} {b_iter k : ℕ}
    {variant : Tape → (Fin n → Tape) → Tape → ℕ}
    (h_variant_bound : ∀ inp work out, inv inp work out → variant inp work out ≤ k)
    (h_iter : ∀ inp work out, inv inp work out →
      (∃ c' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧
        post c'.input c'.work c'.output)
      ∨
      (∃ inp' work' out' t, t ≤ b_iter ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        inv inp' work' out' ∧
        variant inp' work' out' < variant inp work out)) :
    (loopTM tmBody tmTest).HoareTime inv post ((k + 1) * b_iter) := by
  intro inp work out hinv
  exact loopTM_hoareTime_aux tmBody tmTest h_iter k inp work out hinv
    (h_variant_bound inp work out hinv)

end TM
