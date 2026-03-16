import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.SeqInternal
import Complexitylib.Models.TuringMachine.Combinators.IfInternal
import Complexitylib.Models.TuringMachine.Combinators.LoopInternal
import Complexitylib.Models.TuringMachine.Combinators.ComplementInternal

/-!
# Hoare-style composition rules for TM combinators

## Main results

- `seqTM_hoareTime` — sequential composition of Hoare triples
- `complementTM_hoareTime` — complement flips output cell 1
- `ifTM_hoareTime` — if-then-else branching
- `loopTM_hoareTime` — loop invariant rule
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
-- Complement rule
-- ════════════════════════════════════════════════════════════════════════

/-- **Complement Hoare triple**. If `tm` satisfies a Hoare triple whose
    postcondition provides output WF (for rewind), a head bound, and a
    property of output cell 1, then `complementTM tm` satisfies a triple
    where output cell 1 is flipped. Time: `b + p_bound + 4`. -/
theorem complementTM_hoareTime (tm : TM n)
    {pre : TapePred n} {b p_bound : ℕ}
    {cell1_pred : Γ → Prop}
    (h_tm : tm.HoareTime pre
      (fun _ _ out =>
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ p_bound ∧
        cell1_pred (out.cells 1))
      b) :
    tm.complementTM.HoareTime pre
      (fun _ _ out => ∃ g, cell1_pred g ∧ out.cells 1 = (flipBit g).toΓ)
      (b + p_bound + 4) := by
  intro inp work out hpre
  obtain ⟨c', t, ht, hreach, hhalt, hcell0, hnostart, hhead, hcell1⟩ :=
    h_tm inp work out hpre
  have hsim := complementTM_simulation tm hreach
  rw [compCfg_qstart] at hsim
  obtain ⟨c_done, t_rw, hreach_rw, hhalt_done, hflip, hle_rw⟩ :=
    complementTM_rewind_and_flip tm c' hhalt hcell0 hnostart
  exact ⟨c_done, t + t_rw,
    by have : t_rw ≤ p_bound + 4 := le_trans hle_rw (by omega); omega,
    reachesIn_trans _ hsim hreach_rw, hhalt_done,
    c'.output.cells 1, hcell1, hflip⟩

-- ════════════════════════════════════════════════════════════════════════
-- If-then-else rule
-- ════════════════════════════════════════════════════════════════════════

/-- **If-then-else Hoare triple**. The test runs first (via its Hoare triple),
    then the rest of the execution (transition → rewind → check → branch → halt)
    is handled by `h_branch`, which receives the halted test config.

    The user proves `h_branch` using the per-phase simulation lemmas:
    `ifTM_test_to_rewind`, `ifTM_rewind_loop`, `ifTM_check_step_then`/`_else`,
    `ifTM_then_simulation`/`_else_simulation`, `ifTM_then_halt_step`/`_else_halt_step`. -/
theorem ifTM_hoareTime (tmTest tmThen tmElse : TM n)
    {pre mid_test post : TapePred n} {b_test b_branch : ℕ}
    (h_test : tmTest.HoareTime pre mid_test b_test)
    (h_branch : ∀ (c_test : Cfg n tmTest.Q),
      tmTest.halted c_test →
      mid_test c_test.input c_test.work c_test.output →
      ∃ c_done t, t ≤ b_branch ∧
        (ifTM tmTest tmThen tmElse).reachesIn t
          (ifTestWrap tmTest tmThen tmElse c_test) c_done ∧
        (ifTM tmTest tmThen tmElse).halted c_done ∧
        post c_done.input c_done.work c_done.output) :
    (ifTM tmTest tmThen tmElse).HoareTime pre post (b_test + b_branch) := by
  intro inp work out hpre
  obtain ⟨c_test, t₁, ht₁, hreach₁, hhalt₁, hmid⟩ := h_test inp work out hpre
  have hsim := ifTM_test_simulation tmTest tmThen tmElse hreach₁
  obtain ⟨c_done, t₂, ht₂, hreach₂, hhalt₂, hpost⟩ :=
    h_branch c_test hhalt₁ hmid
  exact ⟨c_done, t₁ + t₂, by omega,
    reachesIn_trans _ hsim hreach₂, hhalt₂, hpost⟩

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
