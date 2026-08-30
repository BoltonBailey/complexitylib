/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Time-bounded symmetry of information -- proof internals
-/


public section

namespace Complexity

private theorem withTopNat_add_le_add_internal
    {first second third fourth : WithTop ℕ}
    (hfirst : first ≤ third) (hsecond : second ≤ fourth) :
    first + second ≤ third + fourth := by
  induction first using WithTop.recTopCoe with
  | top =>
      have hthird : third = ⊤ := top_unique hfirst
      subst third
      simp [WithTop.top_add]
  | coe firstValue =>
      induction second using WithTop.recTopCoe with
      | top =>
          have hfourth : fourth = ⊤ := top_unique hsecond
          subst fourth
          simp [WithTop.add_top]
      | coe secondValue =>
          induction third using WithTop.recTopCoe with
          | top => simp [WithTop.top_add]
          | coe thirdValue =>
              induction fourth using WithTop.recTopCoe with
              | top => simp [WithTop.add_top]
              | coe fourthValue =>
                  exact WithTop.coe_le_coe.mpr <|
                    Nat.add_le_add (WithTop.coe_le_coe.mp hfirst)
                      (WithTop.coe_le_coe.mp hsecond)

theorem isAdmissibleKolmogorovClock_id_internal :
    IsAdmissibleKolmogorovClock id := by
  constructor
  · intro time
    exact le_rfl
  · refine ⟨1, 1, ?_⟩
    intro time
    simp

theorem TimeBoundedSymmetryOfInformation.conditional_ne_top_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time) :
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      first condition (clock time) ≠ ⊤ := by
  intro htop
  have hchain := hsoi.chain_le first condition time hsize
  have hpair := hsoi.pairFinite first condition time hsize
  obtain ⟨pairValue, hpairValue⟩ := WithTop.ne_top_iff_exists.mp hpair
  rw [htop, WithTop.top_add, ← hpairValue] at hchain
  change (⊤ : WithTop ℕ) ≤ ((pairValue + loss time : ℕ) : WithTop ℕ) at hchain
  exact WithTop.not_top_le_coe _ hchain

theorem TimeBoundedSymmetryOfInformation.condition_ne_top_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time) :
    ordinaryMachine.timeBoundedKolmogorovComplexity
      condition (clock time) ≠ ⊤ := by
  intro htop
  have hchain := hsoi.chain_le first condition time hsize
  have hpair := hsoi.pairFinite first condition time hsize
  obtain ⟨pairValue, hpairValue⟩ := WithTop.ne_top_iff_exists.mp hpair
  rw [htop, WithTop.add_top, ← hpairValue] at hchain
  change (⊤ : WithTop ℕ) ≤ ((pairValue + loss time : ℕ) : WithTop ℕ) at hchain
  exact WithTop.not_top_le_coe _ hchain

theorem TimeBoundedSymmetryOfInformation.weaken_loss_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock firstLoss secondLoss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock firstLoss)
    (hloss : ∀ time, firstLoss time ≤ secondLoss time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock secondLoss := by
  constructor
  · exact hsoi.pairFinite
  · intro first condition time hsize
    exact (hsoi.chain_le first condition time hsize).trans <|
      withTopNat_add_le_add_internal le_rfl
        (WithTop.coe_le_coe.mpr (hloss time))

theorem TimeBoundedSymmetryOfInformation.weaken_clock_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {firstClock secondClock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine firstClock loss)
    (hclock : ∀ time, firstClock time ≤ secondClock time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      secondClock loss := by
  constructor
  · exact hsoi.pairFinite
  · intro first condition time hsize
    calc
      conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
              first condition (secondClock time) +
          ordinaryMachine.timeBoundedKolmogorovComplexity
            condition (secondClock time) ≤
        conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
                first condition (firstClock time) +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              condition (firstClock time) := by
                apply withTopNat_add_le_add_internal
                · exact
                    OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
                      conditionalMachine first condition (hclock time)
                · exact TM.timeBoundedKolmogorovComplexity_mono_internal
                    ordinaryMachine condition (hclock time)
      _ ≤ ordinaryMachine.timeBoundedKolmogorovComplexity
              (pair first condition) time + (loss time : WithTop ℕ) :=
        hsoi.chain_le first condition time hsize

theorem PolynomialTimeBoundedSymmetryOfInformation.enlarge_clock_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hsoi : PolynomialTimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine)
    {largerClock : ℕ → ℕ}
    (hlargerAdmissible : IsAdmissibleKolmogorovClock largerClock)
    (hlarger : ∀ clock additive,
      IsAdmissibleKolmogorovClock clock →
      TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine clock
        (fun time => Nat.log 2 (clock time) + additive) →
      ∀ time, clock time ≤ largerClock time) :
    IsAdmissibleKolmogorovClock largerClock ∧
      ∃ additive,
        TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
          largerClock (fun time => Nat.log 2 (largerClock time) + additive) := by
  obtain ⟨clock, additive, hclock, hfixed⟩ := hsoi
  refine ⟨hlargerAdmissible, additive, ?_⟩
  apply (hfixed.weaken_clock_internal
    (hlarger clock additive hclock hfixed)).weaken_loss_internal
  intro time
  exact Nat.add_le_add_right
    (Nat.log_mono_right (hlarger clock additive hclock hfixed time)) additive

end Complexity
