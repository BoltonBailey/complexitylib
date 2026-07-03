import Complexitylib.SAT.CookLevin.EmitterLoop

/-!
# The clause-family emitters

One emitting machine per `tableauCNFFlat` family, each with a Hoare
specification appending exactly that family's `CNF.encode` image.

The emitter's tape layout is fixed once (`Emit.nT = 20` work tapes, named
indices below), so register-distinctness side conditions are all `decide`.
-/

namespace SAT

open _root_.TM Tableau

-- ════════════════════════════════════════════════════════════════════════
-- Tape layout
-- ════════════════════════════════════════════════════════════════════════

namespace Emit

/-- Number of work tapes of the reduction emitter. -/
abbrev nT : ℕ := 20

abbrev rA : Fin nT := 0        -- radix A = steps + 1
abbrev rB : Fin nT := 1        -- radix B = max Qc 3
abbrev rC : Fin nT := 2        -- radix C = P + 2
abbrev rD : Fin nT := 3        -- radix D = 4
abbrev tmp : Fin nT := 4       -- numeral scratch
abbrev tmp2 : Fin nT := 5      -- numeral scratch
abbrev nReg : Fin nT := 6      -- |x|
abbrev stepsReg : Fin nT := 7  -- steps = p.eval |x|
abbrev pReg : Fin nT := 8      -- P = steps + |x| + 1
abbrev tReg : Fin nT := 9      -- row counter t
abbrev tFuel : Fin nT := 10    -- row-loop fuel
abbrev tPlusReg : Fin nT := 11 -- t + 1
abbrev pos1Reg : Fin nT := 12  -- position counter (pos / pi)
abbrev pos1Fuel : Fin nT := 13 -- position-loop fuel (P + 1)
abbrev pos2Reg : Fin nT := 14  -- second position counter (pos' / pw)
abbrev pos2Fuel : Fin nT := 15 -- second position fuel (P + 1)
abbrev pos3Reg : Fin nT := 16  -- third position counter (po)
abbrev pos3Fuel : Fin nT := 17 -- third position fuel (P + 1)
abbrev auxReg : Fin nT := 18   -- spare
abbrev auxReg2 : Fin nT := 19  -- spare

end Emit

open Emit

-- ════════════════════════════════════════════════════════════════════════
-- Descriptor mirrors of the one-hot builders
-- ════════════════════════════════════════════════════════════════════════

/-- Pointwise `Forall₂` between two maps of the same list. -/
theorem forall₂_map_map {α β γ : Type _} {R : β → γ → Prop} (g : α → β)
    (h : α → γ) {l : List α} (hp : ∀ a ∈ l, R (g a) (h a)) :
    List.Forall₂ R (l.map g) (l.map h) := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    exact .cons (hp a List.mem_cons_self)
      (ih fun a' ha' => hp a' (List.mem_cons_of_mem _ ha'))

theorem forall₂_append {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ u₁ : List α} {l₂ u₂ : List β}, List.Forall₂ R l₁ l₂ →
    List.Forall₂ R u₁ u₂ → List.Forall₂ R (l₁ ++ u₁) (l₂ ++ u₂) := by
  intro l₁ u₁ l₂ u₂ h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | cons hab _ ih => exact .cons hab ih

variable {n : ℕ}

/-- Descriptor mirror of `atMostOne`. -/
def atMostOneD (mk : ℕ → LitDesc n) : List ℕ → List (List (LitDesc n))
  | [] => []
  | q :: qs => qs.map (fun q' => [mk q, mk q']) ++ atMostOneD mk qs

/-- Descriptor mirror of `exactlyOne`. -/
def exactlyOneD (mkPos mkNeg : ℕ → LitDesc n) (qs : List ℕ) :
    List (List (LitDesc n)) :=
  qs.map mkPos :: atMostOneD mkNeg qs

theorem forall₂_atMostOneD {R : LitDesc n → Lit → Prop} (mk : ℕ → LitDesc n)
    (f : ℕ → ℕ) :
    ∀ {qs : List ℕ}, (∀ q ∈ qs, R (mk q) ⟨false, f q⟩) →
    List.Forall₂ (List.Forall₂ R) (atMostOneD mk qs) (atMostOne (qs.map f)) := by
  intro qs
  induction qs with
  | nil => intro _; exact .nil
  | cons q qs ih =>
    intro hp
    rw [atMostOneD, List.map_cons, atMostOne]
    refine forall₂_append ?_
      (ih fun q' hq' => hp q' (List.mem_cons_of_mem _ hq'))
    rw [List.map_map]
    refine forall₂_map_map _ _ fun q' hq' => ?_
    exact .cons (hp q List.mem_cons_self)
      (.cons (hp q' (List.mem_cons_of_mem _ hq')) .nil)

theorem forall₂_exactlyOneD {R : LitDesc n → Lit → Prop}
    (mkPos mkNeg : ℕ → LitDesc n) (f : ℕ → ℕ) {qs : List ℕ}
    (hpos : ∀ q ∈ qs, R (mkPos q) ⟨true, f q⟩)
    (hneg : ∀ q ∈ qs, R (mkNeg q) ⟨false, f q⟩) :
    List.Forall₂ (List.Forall₂ R) (exactlyOneD mkPos mkNeg qs)
      (exactlyOne (qs.map f)) := by
  rw [exactlyOneD, exactlyOne]
  refine .cons ?_ (forall₂_atMostOneD mkNeg f hneg)
  rw [atLeastOne, List.map_map]
  exact forall₂_map_map _ _ fun q hq => hpos q hq

/-- Clause sizes in `atMostOneD` are 2. -/
theorem atMostOneD_length_le (mk : ℕ → LitDesc n) :
    ∀ (qs : List ℕ), ∀ c ∈ atMostOneD mk qs, c.length ≤ 2 := by
  intro qs
  induction qs with
  | nil => intro c hc; cases hc
  | cons q qs ih =>
    intro c hc
    rw [atMostOneD] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨q', _, rfl⟩ := List.mem_map.mp hc
      simp
    · exact ih c hc

/-- `atMostOneD` over `m` indices has at most `m²` clauses. -/
theorem atMostOneD_card_le (mk : ℕ → LitDesc n) :
    ∀ (qs : List ℕ), (atMostOneD mk qs).length ≤ qs.length * qs.length := by
  intro qs
  induction qs with
  | nil => simp [atMostOneD]
  | cons q qs ih =>
    rw [atMostOneD, List.length_append, List.length_map, List.length_cons]
    have := ih
    nlinarith

-- ════════════════════════════════════════════════════════════════════════
-- Family: acceptClausesF
-- ════════════════════════════════════════════════════════════════════════

/-- Descriptors of the two accept clauses. -/
noncomputable def acceptDescs (N : NTM 1) : List (List (LitDesc nT)) :=
  [[⟨true, 0, .inl stepsReg, .inr (stateIdx N N.qhalt), .inr 0, .inr 0⟩],
   [⟨true, 2, .inl stepsReg, .inr 2, .inr 1, .inr (symIdx Γ.one)⟩]]

/-- **The accept-family emitter.** -/
noncomputable def emitAcceptTM (N : NTM 1) : TM nT :=
  emitCNFTM rA rB rC rD tmp tmp2 (acceptDescs N)

/-- **`emitAcceptTM` Hoare specification**: appends the encoded accept
    clauses. -/
theorem emitAcceptTM_hoareTime (N : NTM 1) (steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regT (steps + 1))
    (hrB : work₀ rB = regT (max (Fintype.card N.Q) 3))
    (hrC : work₀ rC = regT (P + 2))
    (hrD : work₀ rD = regT 4)
    (hsteps : work₀ stepsReg = regT steps) :
    (emitAcceptTM N).HoareTime
      (emitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (emitPred inp₀ (scratch work₀ tmp tmp2 0)
        (ys ++ CNF.encode (acceptClausesF N steps P)))
      (cnfBudget 2 1 M) := by
  have hA1 : 1 ≤ steps + 1 := by omega
  have hB1 : 1 ≤ max (Fintype.card N.Q) 3 := by omega
  have hC1 : 1 ≤ P + 2 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 hB1 hC1 (by omega) hM
  have hf : List.Forall₂
      (List.Forall₂ (LitDesc.Spec work₀ tmp tmp2 M (steps + 1)
        (max (Fintype.card N.Q) 3) (P + 2) 4))
      (acceptDescs N) (acceptClausesF N steps P) := by
    rw [acceptDescs, acceptClausesF]
    refine .cons (.cons ?_ .nil) (.cons (.cons ?_ .nil) .nil)
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega)
        (show steps < steps + 1 by omega)
        (lt_of_lt_of_le (stateIdx_lt N N.qhalt) (le_max_left _ 3))
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨steps, stateIdx N N.qhalt, 0, 0,
        ⟨hsteps, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl,
        k0, k1, k2, k3, k4⟩
    · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
        (show steps < steps + 1 by omega)
        (show 1 + 1 < max (Fintype.card N.Q) 3 by omega)
        (show 1 < P + 2 by omega) (symIdx_lt Γ.one) hM
      exact ⟨steps, 1 + 1, 1, symIdx Γ.one,
        ⟨hsteps, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl,
        k0, k1, k2, k3, k4⟩
  have h := emitCNFTM_hoareTime rA rB rC rD tmp tmp2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hAM hBM hCM hDM inp₀ hinp₀ hf
    (L := 1) (by
      intro descs hdescs
      rw [acceptDescs] at hdescs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdescs
      rcases hdescs with rfl | rfl <;> simp)
    ys hwork₀ hrA hrB hrC hrD
  exact h

end SAT
