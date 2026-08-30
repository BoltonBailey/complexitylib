/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap
public import Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative.Internal

/-!
# Multiplicative-gap conditional MinKT

This module formalizes Definition 6.5's multiplicative no threshold, its exact
program semantics, factor monotonicity, disjoint promise, and relation to the
additive `GapMINCKT` problem. A larger factor narrows the no side; therefore the
resulting multiplicative promise side-preservingly reduces to the additive
factor-one promise by the identity map.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace Multiplicative

/-- The multiplicative no condition exactly forbids descriptions meeting its
relaxed length and transformed-time bounds. -/
theorem isNo_iff_no_relaxedWitness
    {conditionalTapes : ℕ} (inst : GapMINCKT.Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ) :
    IsNo inst conditionalMachine parameters factor ↔
      ¬∃ program,
        IsRelaxedWitness inst conditionalMachine parameters factor program :=
  isNo_iff_no_relaxedWitness_internal inst conditionalMachine parameters factor

/-- Any multiplicative no-instance with factor at least one is an additive
no-instance. -/
theorem IsNo.implies_additive
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {factor : ℕ → ℕ}
    (hfactor : 1 ≤ factor inst.output.length)
    (hno : IsNo inst conditionalMachine parameters factor) :
    inst.IsNo conditionalMachine parameters :=
  isNo_implies_additive_internal hfactor hno

/-- Increasing the approximation factor can only narrow the no side. -/
theorem IsNo.factor_anti
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {first second : ℕ → ℕ}
    (hfactor : first inst.output.length ≤ second inst.output.length)
    (hno : IsNo inst conditionalMachine parameters second) :
    IsNo inst conditionalMachine parameters first :=
  isNo_factor_anti_internal hfactor hno

/-- Widening and a factor of at least one prevent overlap with the
depth-adjusted yes side. -/
theorem not_isNo_of_isYes
    {ordinaryTapes conditionalTapes : ℕ}
    (inst : GapMINCKT.Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : 1 ≤ factor inst.output.length)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    ¬IsNo inst conditionalMachine parameters factor :=
  not_isNo_of_isYes_internal inst ordinaryMachine conditionalMachine parameters
    factor hwidening hfactor hyes

@[simp] theorem mem_noLanguage_encode_iff
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (inst : GapMINCKT.Instance) :
    inst.encode ∈ noLanguage conditionalMachine parameters factor ↔
      IsNo inst conditionalMachine parameters factor :=
  noLanguage_mem_encode_iff_internal conditionalMachine parameters factor inst

/-- The multiplicative no language is contained in the additive no language
when the factor is at least one. -/
theorem noLanguage_subset_additive
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hfactor : ∀ length, 1 ≤ factor length) :
    noLanguage conditionalMachine parameters factor ⊆
      GapMINCKT.noLanguage conditionalMachine parameters :=
  noLanguage_subset_additive_internal conditionalMachine parameters factor
    hfactor

/-- Pointwise larger factors give pointwise smaller no languages. -/
theorem noLanguage_factor_anti
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) {first second : ℕ → ℕ}
    (hfactor : ∀ length, first length ≤ second length) :
    noLanguage conditionalMachine parameters second ⊆
      noLanguage conditionalMachine parameters first :=
  noLanguage_factor_anti_internal conditionalMachine parameters hfactor

/-- Factor one recovers the additive no language exactly. -/
@[simp] theorem noLanguage_one
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) :
    noLanguage conditionalMachine parameters (fun _length => 1) =
      GapMINCKT.noLanguage conditionalMachine parameters :=
  noLanguage_one_internal conditionalMachine parameters

/-- Definition 6.5's widening-certified multiplicative promise. -/
@[expose] def problem
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) : PromiseProblem where
  yesInstances := yesLanguage ordinaryMachine conditionalMachine parameters
  noInstances := noLanguage conditionalMachine parameters factor
  disjoint := disjoint_yesLanguage_noLanguage_internal ordinaryMachine
    conditionalMachine parameters factor hwidening hfactor

@[simp] theorem problem_yesInstances
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    (problem ordinaryMachine conditionalMachine parameters factor hwidening
      hfactor).yesInstances =
        yesLanguage ordinaryMachine conditionalMachine parameters := rfl

@[simp] theorem problem_noInstances
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    (problem ordinaryMachine conditionalMachine parameters factor hwidening
      hfactor).noInstances =
        noLanguage conditionalMachine parameters factor := rfl

/-- The identity map side-preservingly reduces every factor-at-least-one
multiplicative promise to the additive factor-one promise. -/
theorem mapReducesVia_additive
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    (problem ordinaryMachine conditionalMachine parameters factor hwidening
      hfactor).MapReducesVia
        (Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
          hwidening) id := by
  constructor
  · intro bits hyes
    exact hyes
  · intro bits hno
    exact noLanguage_subset_additive conditionalMachine parameters factor
      hfactor hno

/-- The semantic identity reduction is polynomial time. -/
theorem mapReducesPoly_additive
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    (problem ordinaryMachine conditionalMachine parameters factor hwidening
      hfactor).MapReducesPoly
        (Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
          hwidening) :=
  ⟨id, id_mem_FP,
    mapReducesVia_additive ordinaryMachine conditionalMachine parameters factor
      hwidening hfactor⟩

/-- NP-hardness of a factor-at-least-one multiplicative gap transfers to the
additive factor-one promise. The direction follows the narrowing of the
multiplicative no side. -/
theorem promiseNPHard_additive
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (problem ordinaryMachine conditionalMachine parameters factor hwidening
        hfactor)) :
    PromiseNPHard
      (Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
        hwidening) :=
  hhard.of_reduction
    (mapReducesPoly_additive ordinaryMachine conditionalMachine parameters
      factor hwidening hfactor)

/-- If the multiplicative conditional gap is NP-hard while the corresponding
additive gap has a deterministic polynomial-time completion, then `P = NP`. -/
theorem P_eq_NP_of_hard_of_additive_mem_PromiseP
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (problem ordinaryMachine conditionalMachine parameters factor hwidening
        hfactor))
    (hmembership :
      Complexity.GapMINCKT ordinaryMachine conditionalMachine parameters
          hwidening ∈ PromiseP) :
    P = NP :=
  (promiseNPHard_additive ordinaryMachine conditionalMachine parameters factor
    hwidening hfactor hhard).P_eq_NP_of_mem_PromiseP hmembership

/-- A valid conditional-complexity estimator whose threshold language is in
`P` rules out NP-hardness of the corresponding multiplicative gap unless
`P = NP`. This is the promise-hardness endpoint of the SoI estimator route. -/
theorem P_eq_NP_of_hard_of_estimatorLanguage_mem_P
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (problem ordinaryMachine conditionalMachine parameters factor hwidening
        hfactor))
    {estimate : GapMINCKT.Estimator}
    (hestimate : estimate.SatisfiesBounds ordinaryMachine conditionalMachine
      parameters)
    (hpolynomial : GapMINCKT.estimatorLanguage estimate ∈ P) :
    P = NP :=
  P_eq_NP_of_hard_of_additive_mem_PromiseP ordinaryMachine conditionalMachine
    parameters factor hwidening hfactor hhard
      (GapMINCKT_mem_PromiseP_of_estimatorLanguage_mem_P hwidening hestimate
        hpolynomial)

end Multiplicative

end GapMINCKT

end Complexity
