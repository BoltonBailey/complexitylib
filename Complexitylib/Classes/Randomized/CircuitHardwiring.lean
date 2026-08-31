/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.EventProb
public import Complexitylib.Circuits.Hardwiring

/-!
# Derandomizing multi-output circuits

This module isolates the finite nonuniform randomness-fixing step for a
randomized multi-output circuit. If the circuit fails its pointwise
specification with probability at most `2^-(n + 1)` on every `n`-bit input,
then one seed works simultaneously on all inputs. Hardwiring that seed preserves
the circuit's exact size.

This is the circuit-level union-bound step used when turning a sufficiently
accurate randomized approximate counter into a deterministic nonuniform
multi-output circuit.
-/


public section

namespace Complexity

namespace Circuit

/-- The seeds on which a randomized circuit fails its output specification at
one fixed input. Random bits occupy the circuit's input prefix. -/
def badSeedEvent {seedWidth inputWidth outputWidth internalGates : Nat}
    [NeZero inputWidth] [NeZero outputWidth]
    (circuit : Circuit Basis.andOr2 (seedWidth + inputWidth)
      outputWidth internalGates)
    (IsCorrect : BitString inputWidth -> BitString outputWidth -> Prop)
    [forall input output, Decidable (IsCorrect input output)]
    (input : BitString inputWidth) : Finset (BitString seedWidth) :=
  Finset.univ.filter fun seed =>
    ¬ IsCorrect input (circuit.eval (Fin.append seed input))

/-- Membership in the bad-seed event is exactly failure of the output
specification on the seed-prefixed input. -/
@[simp] theorem mem_badSeedEvent_iff
    {seedWidth inputWidth outputWidth internalGates : Nat}
    [NeZero inputWidth] [NeZero outputWidth]
    (circuit : Circuit Basis.andOr2 (seedWidth + inputWidth)
      outputWidth internalGates)
    (IsCorrect : BitString inputWidth -> BitString outputWidth -> Prop)
    [forall input output, Decidable (IsCorrect input output)]
    (input : BitString inputWidth) (seed : BitString seedWidth) :
    seed ∈ badSeedEvent circuit IsCorrect input ↔
      ¬ IsCorrect input (circuit.eval (Fin.append seed input)) := by
  simp [badSeedEvent]

/-- A pointwise `2^-(n + 1)` failure bound leaves one seed that satisfies a
multi-output specification simultaneously on every `n`-bit input. -/
theorem exists_uniform_correct_seed
    {seedWidth inputWidth outputWidth internalGates : Nat}
    [NeZero inputWidth] [NeZero outputWidth]
    (circuit : Circuit Basis.andOr2 (seedWidth + inputWidth)
      outputWidth internalGates)
    (IsCorrect : BitString inputWidth -> BitString outputWidth -> Prop)
    [forall input output, Decidable (IsCorrect input output)]
    (hfailure : forall input,
      eventProb (badSeedEvent circuit IsCorrect input) <=
        1 / (2 : Rat) ^ (inputWidth + 1)) :
    exists seed : BitString seedWidth, forall input,
      IsCorrect input (circuit.eval (Fin.append seed input)) := by
  obtain ⟨seed, hseed⟩ :=
    exists_good_seed_of_eventProb_le_two_pow_succ inputWidth seedWidth
      (badSeedEvent circuit IsCorrect) hfailure
  refine ⟨seed, fun input => ?_⟩
  simpa only [badSeedEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] using hseed input

/-- The uniformly correct seed can be hardwired without increasing circuit
size, producing a deterministic multi-output circuit with the same pointwise
specification. -/
theorem exists_hardwired_correct_circuit
    {seedWidth inputWidth outputWidth internalGates : Nat}
    [NeZero inputWidth] [NeZero outputWidth]
    (circuit : Circuit Basis.andOr2 (seedWidth + inputWidth)
      outputWidth internalGates)
    (IsCorrect : BitString inputWidth -> BitString outputWidth -> Prop)
    [forall input output, Decidable (IsCorrect input output)]
    (hfailure : forall input,
      eventProb (badSeedEvent circuit IsCorrect input) <=
        1 / (2 : Rat) ^ (inputWidth + 1)) :
    exists fixed : Circuit Basis.andOr2 inputWidth outputWidth internalGates,
      (forall input, IsCorrect input (fixed.eval input)) ∧
        fixed.size = circuit.size := by
  obtain ⟨seed, hseed⟩ :=
    exists_uniform_correct_seed circuit IsCorrect hfailure
  refine ⟨restrictPrefix seed circuit, ?_, restrictPrefix_size seed circuit⟩
  intro input
  rw [restrictPrefix_eval]
  exact hseed input

end Circuit

end Complexity
