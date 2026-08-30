/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Defs
public import Complexitylib.Metacomplexity.MINKT.Internal

/-!
# Gap MINKT -- proof internals

Proofs of codec exactness, direct program characterizations, widening-based
disjointness, and totality of the finite-complexity search relation.
-/


public section

namespace Complexity

namespace GapMINKT

namespace Instance

variable {tapes : ℕ}

theorem length_unaryThreshold_internal (inst : Instance) :
    inst.unaryThreshold.length = inst.threshold := by
  simp [unaryThreshold]

theorem decode?_encode_internal (inst : Instance) :
    decode? inst.encode = some inst := by
  rcases inst with ⟨output, time, threshold⟩
  rw [encode, decode?, unpair?_pair]
  simp only [base, unaryThreshold]
  change (do
      let baseInst ← MINKT.Instance.decode?
        ({ output := output, time := time } : MINKT.Instance).encode
      if List.replicate threshold true =
          List.replicate (List.replicate threshold true).length true then
        some
          ({ output := baseInst.output
             time := baseInst.time
             threshold := (List.replicate threshold true).length } : Instance)
      else none) = some ({ output, time, threshold } : Instance)
  rw [MINKT.Instance.decode?_encode_internal]
  simp

theorem decode?_eq_some_iff_internal (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode := by
  constructor
  · intro hdecode
    cases hpair : unpair? bits with
    | none => simp [decode?, hpair] at hdecode
    | some components =>
        rcases components with ⟨baseBits, thresholdBits⟩
        cases hbase : MINKT.Instance.decode? baseBits with
        | none => simp [decode?, hpair, hbase] at hdecode
        | some baseInst =>
            by_cases hthreshold :
                thresholdBits = List.replicate thresholdBits.length true
            · have hbits := eq_pair_of_unpair?_eq_some hpair
              rw [decode?, hpair] at hdecode
              change (MINKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [if_pos hthreshold] at hdecode
              cases hdecode
              have hbaseBits :=
                (MINKT.Instance.decode?_eq_some_iff_internal
                  baseBits baseInst).mp hbase
              calc
                bits = pair baseBits thresholdBits := hbits
                _ = pair baseInst.encode thresholdBits := by rw [hbaseBits]
                _ = pair baseInst.encode
                    (List.replicate thresholdBits.length true) :=
                  congrArg (pair baseInst.encode) hthreshold
                _ = encode
                    { output := baseInst.output
                      time := baseInst.time
                      threshold := thresholdBits.length } := rfl
            · rw [decode?, hpair] at hdecode
              change (MINKT.Instance.decode? baseBits).bind (fun base =>
                  if thresholdBits = List.replicate thresholdBits.length true then
                    some
                      { output := base.output
                        time := base.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [hbase] at hdecode
              change (if thresholdBits =
                  List.replicate thresholdBits.length true then
                    some
                      { output := baseInst.output
                        time := baseInst.time
                        threshold := thresholdBits.length }
                  else none) = some inst at hdecode
              rw [if_neg hthreshold] at hdecode
              contradiction
  · rintro rfl
    exact decode?_encode_internal inst

theorem decode?_eq_none_iff_internal (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode := by
  constructor
  · intro hnone ⟨inst, hbits⟩
    rw [hbits, decode?_encode_internal] at hnone
    contradiction
  · intro hnoncanonical
    cases hdecode : decode? bits with
    | none => rfl
    | some inst =>
        exact (hnoncanonical
          ⟨inst, (decode?_eq_some_iff_internal bits inst).mp hdecode⟩).elim

theorem encode_injective_internal : Function.Injective encode := by
  intro first second hencode
  have hfirst := decode?_encode_internal first
  rw [hencode, decode?_encode_internal second] at hfirst
  exact Option.some.inj hfirst.symm

theorem length_encode_internal (inst : Instance) :
    inst.encode.length =
      4 * inst.output.length + 2 * inst.time + inst.threshold + 6 := by
  rw [encode, pair_length, length_unaryThreshold_internal,
    MINKT.Instance.length_encode_internal]
  change 2 * (2 * inst.output.length + 2 + inst.time) + 2 + inst.threshold =
    4 * inst.output.length + 2 * inst.time + inst.threshold + 6
  omega

theorem isYes_iff_exists_program_internal (inst : Instance)
    (machine : TM tapes) :
    inst.IsYes machine ↔
      ∃ program, program.length ≤ inst.threshold ∧
        machine.ProducesInTime program inst.output inst.time :=
  TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine inst.output inst.time inst.threshold

theorem isNo_iff_no_relaxedWitness_internal (inst : Instance)
    (machine : TM tapes) (parameters : Parameters) :
    inst.IsNo machine parameters ↔
      ¬∃ program, inst.IsRelaxedWitness machine parameters program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (TM.timeBoundedKolmogorovComplexity_le_internal hproduce).trans
        (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
        machine inst.output
          (parameters.clock inst.output.length inst.time)
          (parameters.description inst.output.length inst.threshold)).mp
        hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

theorem not_isNo_of_isYes_internal (inst : Instance)
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (hyes : inst.IsYes machine) :
    ¬inst.IsNo machine parameters := by
  intro hno
  have hclock := TM.timeBoundedKolmogorovComplexity_mono_internal
    machine inst.output (hwidening.2 inst.output.length inst.time)
  have hdescription :
      (inst.threshold : WithTop ℕ) ≤
        (parameters.description inst.output.length inst.threshold : WithTop ℕ) :=
    WithTop.coe_le_coe.mpr
      (hwidening.1 inst.output.length inst.threshold)
  exact (not_lt_of_ge (hclock.trans (hyes.trans hdescription))) hno

end Instance

theorem yesLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (inst : Instance) :
    inst.encode ∈ yesLanguage machine ↔ inst.IsYes machine := by
  simp [yesLanguage, Instance.decode?_encode_internal]

theorem noLanguage_mem_encode_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance) :
    inst.encode ∈ noLanguage machine parameters ↔
      inst.IsNo machine parameters := by
  simp [noLanguage, Instance.decode?_encode_internal]

theorem disjoint_yesLanguage_noLanguage_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) :
    Disjoint (yesLanguage machine) (noLanguage machine parameters) := by
  apply Set.disjoint_left.mpr
  intro bits hyes hno
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, hdecode] using hyes
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time ≤
        (inst.threshold : WithTop ℕ) at hisYes
      have hisNo : inst.IsNo machine parameters := by
        simpa [noLanguage, hdecode] using hno
      exact Instance.not_isNo_of_isYes_internal
        inst machine parameters hwidening hisYes hisNo

theorem mem_yesLanguage_iff_exists_program_internal {tapes : ℕ}
    (machine : TM tapes) (bits : List Bool) :
    bits ∈ yesLanguage machine ↔
      ∃ program, YesWitnessRelation machine bits program := by
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, YesWitnessRelation, hdecode]
  | some inst =>
      rw [show bits ∈ yesLanguage machine ↔ inst.IsYes machine by
        simp [yesLanguage, hdecode],
        Instance.isYes_iff_exists_program_internal]
      constructor
      · rintro ⟨program, hlength, hproduce⟩
        exact ⟨program, inst, hdecode, hlength, hproduce⟩
      · rintro ⟨program, decoded, hdecoded, hlength, hproduce⟩
        have : decoded = inst := Option.some.inj (hdecoded.symm.trans hdecode)
        subst decoded
        exact ⟨program, hlength, hproduce⟩

theorem yesWitnessRelation_length_le_input_internal {tapes : ℕ}
    (machine : TM tapes) {bits program : List Bool}
    (hrelation : YesWitnessRelation machine bits program) :
    program.length ≤ bits.length := by
  obtain ⟨inst, hdecode, hlength, _hproduce⟩ := hrelation
  have hcanonical :=
    (Instance.decode?_eq_some_iff_internal bits inst).mp hdecode
  rw [hcanonical, Instance.length_encode_internal]
  omega

theorem yesWitnessRelation_polyBalanced_internal {tapes : ℕ}
    (machine : TM tapes) :
    PolyBalanced (YesWitnessRelation machine) := by
  refine ⟨Polynomial.X, ?_⟩
  intro bits program hrelation
  simpa only [Polynomial.eval_X] using
    yesWitnessRelation_length_le_input_internal machine hrelation

theorem exists_searchRelation_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters)
    (hwidening : parameters.IsWidening) (inst : MINKT.Instance) :
    (∃ program, SearchRelation machine parameters inst program) ↔
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
  constructor
  · rintro ⟨program, optimum, hcomplexity, _hlength, _hproduce⟩ htop
    rw [htop] at hcomplexity
    exact WithTop.coe_ne_top hcomplexity.symm
  · intro hfinite
    obtain ⟨program, hlength, hproduce⟩ :=
      TM.timeBoundedKolmogorovComplexity_witness_internal
        machine inst.output inst.time hfinite
    obtain ⟨optimum, hoptimum⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hcomplexity :
        machine.timeBoundedKolmogorovComplexity inst.output inst.time =
          (optimum : WithTop ℕ) := hoptimum.symm
    have hprogramLength : program.length = optimum := by
      exact WithTop.coe_eq_coe.mp (hlength.trans hcomplexity)
    refine ⟨program, optimum, hcomplexity, ?_, ?_⟩
    · rw [hprogramLength]
      exact hwidening.1 inst.output.length optimum
    · exact hproduce.mono (hwidening.2 inst.output.length inst.time)

theorem verifyRelaxedWitness_eq_true_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = true ↔
      inst.IsRelaxedWitness machine parameters program := by
  simp [verifyRelaxedWitness, Instance.IsRelaxedWitness]

theorem verifyRelaxedWitness_eq_false_iff_internal {tapes : ℕ}
    (machine : TM tapes) (parameters : Parameters) (inst : Instance)
    (program : List Bool) :
    verifyRelaxedWitness machine parameters inst program = false ↔
      ¬inst.IsRelaxedWitness machine parameters program := by
  rw [Bool.eq_false_iff]
  exact not_congr
    (verifyRelaxedWitness_eq_true_iff_internal machine parameters inst program)

theorem decisionOfSearch_eq_true_of_mem_yesLanguage_internal
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    {search : SearchAlgorithm}
    (hdescription : parameters.DescriptionMonotone)
    (hsearch : SolvesSearchOnFinite machine parameters search)
    {bits : List Bool} (hyes : bits ∈ yesLanguage machine) :
    decisionOfSearch machine parameters search bits = true := by
  cases hdecode : Instance.decode? bits with
  | none => simp [yesLanguage, hdecode] at hyes
  | some inst =>
      have hisYes : inst.IsYes machine := by
        simpa [yesLanguage, hdecode] using hyes
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time ≤
        (inst.threshold : WithTop ℕ) at hisYes
      have hfinite :
          machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤ := by
        intro htop
        rw [htop] at hisYes
        exact WithTop.not_top_le_coe inst.threshold hisYes
      obtain ⟨optimum, hcomplexity, hlength, hproduce⟩ :=
        hsearch inst.base hfinite
      change machine.timeBoundedKolmogorovComplexity inst.output inst.time =
        (optimum : WithTop ℕ) at hcomplexity
      change (search inst.base).length ≤
        parameters.description inst.output.length optimum at hlength
      change machine.ProducesInTime (search inst.base) inst.output
        (parameters.clock inst.output.length inst.time) at hproduce
      have hoptimum : optimum ≤ inst.threshold := by
        have hbound := hisYes
        rw [hcomplexity] at hbound
        exact WithTop.coe_le_coe.mp hbound
      have hrelaxed : inst.IsRelaxedWitness machine parameters (search inst.base) := by
        constructor
        · exact hlength.trans (hdescription inst.output.length hoptimum)
        · exact hproduce
      rw [decisionOfSearch, hdecode]
      exact (verifyRelaxedWitness_eq_true_iff_internal
        machine parameters inst (search inst.base)).mpr hrelaxed

theorem decisionOfSearch_eq_false_of_mem_noLanguage_internal
    {tapes : ℕ} {machine : TM tapes} {parameters : Parameters}
    (search : SearchAlgorithm) {bits : List Bool}
    (hno : bits ∈ noLanguage machine parameters) :
    decisionOfSearch machine parameters search bits = false := by
  cases hdecode : Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hisNo : inst.IsNo machine parameters := by
        simpa [noLanguage, hdecode] using hno
      have hnone :=
        (Instance.isNo_iff_no_relaxedWitness_internal
          inst machine parameters).mp hisNo
      rw [decisionOfSearch, hdecode]
      exact (verifyRelaxedWitness_eq_false_iff_internal
        machine parameters inst (search inst.base)).mpr
          (fun hrelaxed => hnone ⟨search inst.base, hrelaxed⟩)

end GapMINKT

end Complexity
