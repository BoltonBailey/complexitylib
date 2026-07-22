/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.SpaceTime.Internal.Reachability
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Bounded-runtime binary count-up loop segments -- proof internals
-/

namespace Complexity

namespace TM

variable {n : ℕ}

theorem BinaryForSegmentSpec.reachesIn_internal {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue : ℕ}
    (spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue) :
    ∀ count value, startValue ≤ value → value + count = limitValue →
      ∃ time, time ≤ binaryForLoopTime bodyTime limitValue value count ∧
        (binaryForTM body counterIdx limitIdx).reachesIn time
          (spec.scanCfg value) spec.doneCfg := by
  intro count
  induction count with
  | zero =>
      intro value _hstart hlimit
      have hvalue : value = limitValue := by omega
      subst value
      exact ⟨binaryForCompareTime limitValue, le_rfl, spec.doneRun⟩
  | succ count ih =>
      intro value hstart hlimit
      have hvalue : value < limitValue := by omega
      let iterationTime := spec.iterationTime value
      have hiterationTime := spec.iterationTime_le value hstart hvalue
      have hiteration := spec.iterationRun value hstart hvalue
      obtain ⟨tailTime, htailTime, htail⟩ :=
        ih (value + 1) (by omega) (by omega)
      have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
          (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hstart hvalue) .zero
      have hreach := reachesIn_trans (binaryForTM body counterIdx limitIdx)
        (spec.testRun value hstart hvalue)
        (reachesIn_trans (binaryForTM body counterIdx limitIdx) hiteration
          (reachesIn_trans (binaryForTM body counterIdx limitIdx)
            hloopback htail))
      refine ⟨binaryForCompareTime limitValue +
        (iterationTime + (1 + tailTime)), ?_, hreach⟩
      rw [binaryForLoopTime]
      omega

theorem BinaryForSegmentSpaceSpec.prefix_withinAuxSpace_internal
    {body : TM n} {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {startValue limitValue inputLength spaceBound : ℕ}
    {spec : BinaryForSegmentSpec body counterIdx limitIdx bodyTime
      startValue limitValue}
    (spaceSpec : BinaryForSegmentSpaceSpec spec inputLength spaceBound) :
    ∀ count value time (cfg : Cfg n (binaryForTM body counterIdx limitIdx).Q),
      startValue ≤ value → value + count = limitValue →
      (binaryForTM body counterIdx limitIdx).reachesIn time
        (spec.scanCfg value) cfg →
      time ≤ binaryForLoopTime bodyTime limitValue value count →
      cfg.WithinAuxSpace inputLength spaceBound := by
  intro count
  induction count with
  | zero =>
      intro value time cfg hstart hlimit hreach _htime
      have hvalue : value = limitValue := by omega
      subst value
      have hactual : time ≤ binaryForCompareTime limitValue :=
        (binaryForTM body counterIdx limitIdx).reachesIn_le_halt hreach
          spec.doneRun spec.doneHalted
      exact spaceSpec.testPrefixWithin limitValue time cfg hstart le_rfl
        hactual hreach
  | succ count ih =>
      intro value time cfg hstart hlimit hreach _htime
      have hvalue : value < limitValue := by omega
      let iterationTime := spec.iterationTime value
      have hiterationRun := spec.iterationRun value hstart hvalue
      obtain ⟨tailFullTime, htailBound, htailFull⟩ :=
        spec.reachesIn_internal count (value + 1) (by omega) (by omega)
      have hloopback : (binaryForTM body counterIdx limitIdx).reachesIn 1
          (spec.iterationDoneCfg value) (spec.scanCfg (value + 1)) :=
        .step (spec.loopbackStep value hstart hvalue) .zero
      have hfull := reachesIn_trans (binaryForTM body counterIdx limitIdx)
        (spec.testRun value hstart hvalue)
        (reachesIn_trans (binaryForTM body counterIdx limitIdx)
          hiterationRun
          (reachesIn_trans (binaryForTM body counterIdx limitIdx)
            hloopback htailFull))
      have hactual :
          time ≤ binaryForCompareTime limitValue +
            (iterationTime + (1 + tailFullTime)) :=
        (binaryForTM body counterIdx limitIdx).reachesIn_le_halt hreach
          hfull spec.doneHalted
      by_cases htest : time ≤ binaryForCompareTime limitValue
      · exact spaceSpec.testPrefixWithin value time cfg hstart
          (Nat.le_of_lt hvalue) htest hreach
      · let afterTestTime := time - binaryForCompareTime limitValue
        have htimeEq : binaryForCompareTime limitValue + afterTestTime =
            time := by
          dsimp only [afterTestTime]
          exact Nat.add_sub_of_le (by omega)
        by_cases hiteration : afterTestTime ≤ iterationTime
        · obtain ⟨d, hprefix, _hsuffix⟩ :=
            reachesIn_prefix_internal hiterationRun hiteration
          have hcanonical :
              (binaryForTM body counterIdx limitIdx).reachesIn time
                (spec.scanCfg value) d := by
            have hrun := reachesIn_trans
              (binaryForTM body counterIdx limitIdx)
              (spec.testRun value hstart hvalue) hprefix
            simpa [htimeEq] using hrun
          have hcfg :=
            (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
              hreach hcanonical
          rw [hcfg]
          exact spaceSpec.iterationPrefixWithin value afterTestTime d
            hstart hvalue hiteration hprefix
        · let prefixTime := binaryForCompareTime limitValue +
              iterationTime + 1
          have hprefixTime : prefixTime ≤ time := by
            dsimp only [prefixTime, afterTestTime] at ⊢ hiteration
            omega
          let tailTime := time - prefixTime
          have htailEq : prefixTime + tailTime = time := by
            dsimp only [tailTime]
            exact Nat.add_sub_of_le hprefixTime
          have htailActual : tailTime ≤ tailFullTime := by
            dsimp only [prefixTime, tailTime] at ⊢ hactual
            omega
          obtain ⟨d, htail, _hsuffix⟩ :=
            reachesIn_prefix_internal htailFull htailActual
          have hcanonical :
              (binaryForTM body counterIdx limitIdx).reachesIn time
                (spec.scanCfg value) d := by
            have hrun := reachesIn_trans
              (binaryForTM body counterIdx limitIdx)
              (spec.testRun value hstart hvalue)
              (reachesIn_trans (binaryForTM body counterIdx limitIdx)
                hiterationRun
                (reachesIn_trans (binaryForTM body counterIdx limitIdx)
                  hloopback htail))
            convert hrun using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hcfg :=
            (binaryForTM body counterIdx limitIdx).reachesIn_right_unique
              hreach hcanonical
          rw [hcfg]
          exact ih (value + 1) tailTime d (by omega) (by omega) htail
            (le_trans htailActual htailBound)

end TM

end Complexity
