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

end TM
