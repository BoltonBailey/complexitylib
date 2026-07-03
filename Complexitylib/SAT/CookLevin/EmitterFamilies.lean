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

-- ════════════════════════════════════════════════════════════════════════
-- Family: oneHotStatesF
-- ════════════════════════════════════════════════════════════════════════

/-- Leaf descriptors: exactly one state at the row read from `tReg`. -/
def oneHotStatesLeafD (Qc : ℕ) : List (List (LitDesc nT)) :=
  exactlyOneD (fun q => ⟨true, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩)
    (fun q => ⟨false, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩)
    (List.range Qc)

/-- **The state one-hot emitter**: loop the leaf over all rows. -/
def emitOneHotStatesTM (Qc : ℕ) : TM nT :=
  emitLoopTM (emitCNFTM rA rB rC rD tmp tmp2 (oneHotStatesLeafD Qc)) tReg tFuel

/-- **`emitOneHotStatesTM` Hoare specification**: appends the encoded
    state one-hot family, leaving the row counter at `steps + 1`. -/
theorem emitOneHotStatesTM_hoareTime (N : NTM 1) (steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regT (steps + 1))
    (hrB : work₀ rB = regT (max (Fintype.card N.Q) 3))
    (hrC : work₀ rC = regT (P + 2))
    (hrD : work₀ rD = regT 4)
    (htReg : work₀ tReg = regT 0)
    (htFuel : work₀ tFuel = regT (steps + 1)) :
    (emitOneHotStatesTM (Fintype.card N.Q)).HoareTime
      (emitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (emitPred inp₀
        (scratch (Function.update work₀ tReg (regT (steps + 1))) tmp tmp2 0)
        (ys ++ CNF.encode (oneHotStatesF N steps P)))
      (loopBudget M (cnfBudget (1 + M * M) (M + 2) M)) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hQcM : Fintype.card N.Q ≤ M := le_trans (le_max_left _ 3) hBM
  have hbody : ∀ i, i < steps + 1 →
      (emitCNFTM rA rB rC rD tmp tmp2
        (oneHotStatesLeafD (Fintype.card N.Q))).HoareTime
        (emitPred inp₀
          (Function.update
            (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
            ⟨i + 2, regCells (steps + 1)⟩)
          (ys ++ (List.range i).flatMap (fun t =>
            CNF.encode (exactlyOne ((List.range (Fintype.card N.Q)).map
              (vStateF (Fintype.card N.Q) steps P t))))))
        (emitPred inp₀
          (Function.update
            (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
            ⟨i + 2, regCells (steps + 1)⟩)
          (ys ++ (List.range (i + 1)).flatMap (fun t =>
            CNF.encode (exactlyOne ((List.range (Fintype.card N.Q)).map
              (vStateF (Fintype.card N.Q) steps P t))))))
        (cnfBudget (1 + M * M) (M + 2) M) := by
    intro i hi
    set base : Fin nT → Tape :=
      Function.update (Function.update work₀ tReg (regT i)) tFuel
        ⟨i + 2, regCells (steps + 1)⟩ with hbase
    have hstate : Function.update
        (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
        ⟨i + 2, regCells (steps + 1)⟩ = scratch base tmp tmp2 0 := by
      rw [update_scratch (by decide) (by decide),
        update_scratch (by decide) (by decide)]
    have hbaseP : ∀ j, Parked (base j) := by
      intro j
      by_cases hjf : j = tFuel
      · subst hjf; rw [hbase, Function.update_self]
        exact parked_regCells (by omega)
      · rw [hbase, Function.update_of_ne hjf]
        by_cases hjt : j = tReg
        · subst hjt; rw [Function.update_self]; exact regT_parked _
        · rw [Function.update_of_ne hjt]; exact hwork₀ j
    have hbrA : base rA = regT (steps + 1) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hrA
    have hbrB : base rB = regT (max (Fintype.card N.Q) 3) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hrB
    have hbrC : base rC = regT (P + 2) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hrC
    have hbrD : base rD = regT 4 := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hrD
    have hbt : base tReg = regT i := by
      rw [hbase, Function.update_of_ne (by decide), Function.update_self]
    have hlit : ∀ (s : Bool) (q : ℕ), q < Fintype.card N.Q →
        LitDesc.Spec base tmp tmp2 M (steps + 1) (max (Fintype.card N.Q) 3)
          (P + 2) 4
          ⟨s, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩
          ⟨s, vStateF (Fintype.card N.Q) steps P i q⟩ := by
      intro s q hq
      obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega)
        (show i < steps + 1 by omega)
        (lt_of_lt_of_le hq (le_max_left _ 3))
        (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
      exact ⟨i, q, 0, 0, ⟨hbt, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl,
        k0, k1, k2, k3, k4⟩
    have hf := forall₂_exactlyOneD
      (fun q => (⟨true, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩ : LitDesc nT))
      (fun q => (⟨false, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩ : LitDesc nT))
      (vStateF (Fintype.card N.Q) steps P i)
      (qs := List.range (Fintype.card N.Q))
      (fun q hq => hlit true q (List.mem_range.mp hq))
      (fun q hq => hlit false q (List.mem_range.mp hq))
    have hcnf := emitCNFTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM inp₀ hinp₀ hf
      (L := Fintype.card N.Q + 2)
      (by
        intro descs hdescs
        rw [exactlyOneD] at hdescs
        rcases List.mem_cons.mp hdescs with rfl | hmem
        · rw [List.length_map, List.length_range]; omega
        · exact le_trans (atMostOneD_length_le _ _ descs hmem) (by omega))
      (ys ++ (List.range i).flatMap (fun t =>
        CNF.encode (exactlyOne ((List.range (Fintype.card N.Q)).map
          (vStateF (Fintype.card N.Q) steps P t)))))
      hbaseP hbrA hbrB hbrC hbrD
    rw [show oneHotStatesLeafD (Fintype.card N.Q)
      = exactlyOneD
          (fun q => (⟨true, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩ : LitDesc nT))
          (fun q => (⟨false, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩ : LitDesc nT))
          (List.range (Fintype.card N.Q)) from rfl, hstate]
    refine hcnf.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, g2, ?_⟩
      rw [flatMap_range_succ, ← List.append_assoc]
      exact g3
    · refine cnfBudget_mono ?_ (by omega)
      rw [exactlyOneD]
      simp only [List.length_cons]
      have hcard := atMostOneD_card_le
        (fun q => (⟨false, 0, .inl tReg, .inr q, .inr 0, .inr 0⟩ : LitDesc nT))
        (List.range (Fintype.card N.Q))
      rw [List.length_range] at hcard
      have hQ2 : Fintype.card N.Q * Fintype.card N.Q ≤ M * M :=
        Nat.mul_le_mul hQcM hQcM
      omega
  have hloop := emitLoop_hoareTime
    (emitCNFTM rA rB rC rD tmp tmp2 (oneHotStatesLeafD (Fintype.card N.Q)))
    tReg tFuel (by decide) (steps + 1) M
    (cnfBudget (1 + M * M) (M + 2) M) hAM
    (fun t => CNF.encode (exactlyOne ((List.range (Fintype.card N.Q)).map
      (vStateF (Fintype.card N.Q) steps P t))))
    inp₀ (scratch work₀ tmp tmp2 0) ys hinp₀ (scratch_parked 0 hwork₀)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact htFuel)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact htReg)
    hbody
  refine hloop.consequence (fun _ _ _ h => h) ?_ (loop_le_loopBudget hAM)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, ?_⟩
  · rw [g2, update_scratch (by decide) (by decide)]
  · rw [oneHotStatesF, CNF.encode_flatMap]
    exact g3

-- ════════════════════════════════════════════════════════════════════════
-- Family: oneHotCellsF
-- ════════════════════════════════════════════════════════════════════════

/-- Leaf descriptors: exactly one symbol per row/tape/position. -/
def cellLeafD (tp : ℕ) : List (List (LitDesc nT)) :=
  exactlyOneD (fun s => ⟨true, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩)
    (fun s => ⟨false, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩)
    (List.range 4)

/-- Position sweep at one tape index: loop the leaf over positions, then
    return the position counter to zero. -/
def posChunkTM (tp : ℕ) : TM nT :=
  seqTM (emitLoopTM (emitCNFTM rA rB rC rD tmp tmp2 (cellLeafD tp))
      pos1Reg pos1Fuel)
    (setConstTM pos1Reg 0)

/-- The `oneHotCells` row body: position sweeps at the three tape indices. -/
def cellsBodyTM : TM nT :=
  seqTM (posChunkTM 0) (seqTM (posChunkTM 1) (posChunkTM 2))

/-- **The cell one-hot emitter**: loop the row body over all rows. -/
def emitOneHotCellsTM : TM nT := emitLoopTM cellsBodyTM tReg tFuel

/-- Budget of one position sweep. -/
def posChunkBudget (M : ℕ) : ℕ :=
  loopBudget M (cnfBudget 17 6 M) + 1 + opBudget M

/-- **`posChunkTM` Hoare specification** (at row `i`, tape index `tp`). -/
theorem posChunkTM_hoareTime (tp : ℕ) (htp : tp < 3) (Qc steps P M i : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (hi : i ≤ steps)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regT (steps + 1)) (hVrB : V rB = regT (max Qc 3))
    (hVrC : V rC = regT (P + 2)) (hVrD : V rD = regT 4)
    (hVt : V tReg = regT i)
    (hVp1 : V pos1Reg = regT 0) (hVf1 : V pos1Fuel = regT (P + 1)) :
    (posChunkTM tp).HoareTime
      (emitPred inp₀ (scratch V tmp tmp2 0) ys)
      (emitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ (List.range (P + 1)).flatMap (fun pos =>
          CNF.encode (exactlyOne ((List.range 4).map
            (vCellF Qc steps P i tp pos))))))
      (posChunkBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hPM : P + 1 ≤ M := by omega
  have hbody : ∀ j, j < P + 1 →
      (emitCNFTM rA rB rC rD tmp tmp2 (cellLeafD tp)).HoareTime
        (emitPred inp₀
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
            ⟨j + 2, regCells (P + 1)⟩)
          (ys ++ (List.range j).flatMap (fun pos =>
            CNF.encode (exactlyOne ((List.range 4).map
              (vCellF Qc steps P i tp pos))))))
        (emitPred inp₀
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
            ⟨j + 2, regCells (P + 1)⟩)
          (ys ++ (List.range (j + 1)).flatMap (fun pos =>
            CNF.encode (exactlyOne ((List.range 4).map
              (vCellF Qc steps P i tp pos))))))
        (cnfBudget 17 6 M) := by
    intro j hj
    set base : Fin nT → Tape :=
      Function.update (Function.update V pos1Reg (regT j)) pos1Fuel
        ⟨j + 2, regCells (P + 1)⟩ with hbase
    have hstate : Function.update
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
        ⟨j + 2, regCells (P + 1)⟩ = scratch base tmp tmp2 0 := by
      rw [update_scratch (by decide) (by decide),
        update_scratch (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update hV (regT_parked _))
        (parked_regCells (by omega))
    have hbrA : base rA = regT (steps + 1) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVrA
    have hbrB : base rB = regT (max Qc 3) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVrB
    have hbrC : base rC = regT (P + 2) := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVrC
    have hbrD : base rD = regT 4 := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVrD
    have hbt : base tReg = regT i := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVt
    have hbp : base pos1Reg = regT j := by
      rw [hbase, Function.update_of_ne (by decide), Function.update_self]
    have hlit : ∀ (sgn : Bool) (s : ℕ), s < 4 →
        LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
          ⟨sgn, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩
          ⟨sgn, vCellF Qc steps P i tp j s⟩ := by
      intro sgn s hs
      obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
        (show i < steps + 1 by omega)
        (show tp < max Qc 3 by omega)
        (show j < P + 2 by omega) hs hM
      exact ⟨i, tp, j, s, ⟨hbt, by decide, by decide⟩, rfl,
        ⟨hbp, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
    have hf := forall₂_exactlyOneD
      (fun s => (⟨true, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩ :
        LitDesc nT))
      (fun s => (⟨false, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩ :
        LitDesc nT))
      (vCellF Qc steps P i tp j) (qs := List.range 4)
      (fun s hs => hlit true s (List.mem_range.mp hs))
      (fun s hs => hlit false s (List.mem_range.mp hs))
    have hcnf := emitCNFTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM inp₀ hinp₀ hf
      (L := 6)
      (by
        intro descs hdescs
        rw [exactlyOneD] at hdescs
        rcases List.mem_cons.mp hdescs with rfl | hmem
        · rw [List.length_map, List.length_range]; omega
        · exact le_trans (atMostOneD_length_le _ _ descs hmem) (by omega))
      (ys ++ (List.range j).flatMap (fun pos =>
        CNF.encode (exactlyOne ((List.range 4).map
          (vCellF Qc steps P i tp pos)))))
      hbaseP hbrA hbrB hbrC hbrD
    rw [show cellLeafD tp = exactlyOneD
        (fun s => (⟨true, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩ :
          LitDesc nT))
        (fun s => (⟨false, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩ :
          LitDesc nT))
        (List.range 4) from rfl, hstate]
    refine hcnf.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, g2, ?_⟩
      rw [flatMap_range_succ, ← List.append_assoc]
      exact g3
    · refine cnfBudget_mono ?_ (by omega)
      rw [exactlyOneD]
      simp only [List.length_cons]
      have hcard := atMostOneD_card_le
        (fun s => (⟨false, 2, .inl tReg, .inr tp, .inl pos1Reg, .inr s⟩ :
          LitDesc nT))
        (List.range 4)
      rw [List.length_range] at hcard
      omega
  have hloop := emitLoop_hoareTime
    (emitCNFTM rA rB rC rD tmp tmp2 (cellLeafD tp)) pos1Reg pos1Fuel
    (by decide) (P + 1) M (cnfBudget 17 6 M) hPM
    (fun pos => CNF.encode (exactlyOne ((List.range 4).map
      (vCellF Qc steps P i tp pos))))
    inp₀ (scratch V tmp tmp2 0) ys hinp₀ (scratch_parked 0 hV)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVf1)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1)
    hbody
  set ys' : List Bool := ys ++ (List.range (P + 1)).flatMap (fun pos =>
    CNF.encode (exactlyOne ((List.range 4).map
      (vCellF Qc steps P i tp pos)))) with hys'
  have hset : (setConstTM pos1Reg 0).HoareTime
      (emitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1))) ys')
      (emitPred inp₀ (scratch V tmp tmp2 0) ys') (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 0 (P + 1) inp₀
      (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1))) ys'
      hinp₀ (parked_update (scratch_parked 0 hV) (regT_parked _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (setConstBudget (by omega) hPM))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem,
      show regT 0 = scratch V tmp tmp2 0 pos1Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1.symm,
      Function.update_eq_self]
  have hseq := seqTM_hoareTime
    (emitLoopTM (emitCNFTM rA rB rC rD tmp tmp2 (cellLeafD tp))
      pos1Reg pos1Fuel)
    (setConstTM pos1Reg 0)
    (hloop.mono_bound (loop_le_loopBudget hPM))
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hV) (regT_parked _)) _)
    hset
  exact hseq.mono_bound (by rw [posChunkBudget])

/-- Budget of the `oneHotCells` row body. -/
def cellsBodyBudget (M : ℕ) : ℕ := 3 * posChunkBudget M + 2

/-- **`cellsBodyTM` Hoare specification** (at row `i`). -/
theorem cellsBodyTM_hoareTime (Qc steps P M i : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (hi : i ≤ steps)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regT (steps + 1)) (hVrB : V rB = regT (max Qc 3))
    (hVrC : V rC = regT (P + 2)) (hVrD : V rD = regT 4)
    (hVt : V tReg = regT i)
    (hVp1 : V pos1Reg = regT 0) (hVf1 : V pos1Fuel = regT (P + 1)) :
    cellsBodyTM.HoareTime
      (emitPred inp₀ (scratch V tmp tmp2 0) ys)
      (emitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ (List.range 3).flatMap (fun tp =>
          (List.range (P + 1)).flatMap (fun pos =>
            CNF.encode (exactlyOne ((List.range 4).map
              (vCellF Qc steps P i tp pos)))))))
      (cellsBodyBudget M) := by
  have h0 := posChunkTM_hoareTime 0 (by omega) Qc steps P M i hM hi inp₀ V ys
    hinp₀ hV hVrA hVrB hVrC hVrD hVt hVp1 hVf1
  have h1 := posChunkTM_hoareTime 1 (by omega) Qc steps P M i hM hi inp₀ V
    (ys ++ (List.range (P + 1)).flatMap (fun pos =>
      CNF.encode (exactlyOne ((List.range 4).map (vCellF Qc steps P i 0 pos)))))
    hinp₀ hV hVrA hVrB hVrC hVrD hVt hVp1 hVf1
  have h2 := posChunkTM_hoareTime 2 (by omega) Qc steps P M i hM hi inp₀ V
    (ys ++ (List.range (P + 1)).flatMap (fun pos =>
      CNF.encode (exactlyOne ((List.range 4).map (vCellF Qc steps P i 0 pos))))
      ++ (List.range (P + 1)).flatMap (fun pos =>
      CNF.encode (exactlyOne ((List.range 4).map (vCellF Qc steps P i 1 pos)))))
    hinp₀ hV hVrA hVrB hVrC hVrD hVt hVp1 hVf1
  have h12 := seqTM_hoareTime (posChunkTM 1) (posChunkTM 2) h1
    (emitPred_transition hinp₀ (scratch_parked 0 hV) _) h2
  have hseq := seqTM_hoareTime (posChunkTM 0)
    (seqTM (posChunkTM 1) (posChunkTM 2)) h0
    (emitPred_transition hinp₀ (scratch_parked 0 hV) _) h12
  refine hseq.consequence (fun _ _ _ h => h) ?_
    (by rw [cellsBodyBudget]; omega)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [show List.range 3 = [0, 1, 2] from by decide]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ← List.append_assoc]
  exact g3

/-- **`emitOneHotCellsTM` Hoare specification**: appends the encoded cell
    one-hot family, leaving the row counter at `steps + 1`. -/
theorem emitOneHotCellsTM_hoareTime (Qc steps P M : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hrA : work₀ rA = regT (steps + 1))
    (hrB : work₀ rB = regT (max Qc 3))
    (hrC : work₀ rC = regT (P + 2))
    (hrD : work₀ rD = regT 4)
    (htReg : work₀ tReg = regT 0)
    (htFuel : work₀ tFuel = regT (steps + 1))
    (hp1 : work₀ pos1Reg = regT 0)
    (hf1 : work₀ pos1Fuel = regT (P + 1)) :
    emitOneHotCellsTM.HoareTime
      (emitPred inp₀ (scratch work₀ tmp tmp2 0) ys)
      (emitPred inp₀
        (scratch (Function.update work₀ tReg (regT (steps + 1))) tmp tmp2 0)
        (ys ++ CNF.encode (oneHotCellsF Qc steps P)))
      (loopBudget M (cellsBodyBudget M)) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hbody : ∀ i, i < steps + 1 → cellsBodyTM.HoareTime
      (emitPred inp₀
        (Function.update
          (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
          ⟨i + 2, regCells (steps + 1)⟩)
        (ys ++ (List.range i).flatMap (fun t =>
          (List.range 3).flatMap (fun tp =>
            (List.range (P + 1)).flatMap (fun pos =>
              CNF.encode (exactlyOne ((List.range 4).map
                (vCellF Qc steps P t tp pos))))))))
      (emitPred inp₀
        (Function.update
          (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
          ⟨i + 2, regCells (steps + 1)⟩)
        (ys ++ (List.range (i + 1)).flatMap (fun t =>
          (List.range 3).flatMap (fun tp =>
            (List.range (P + 1)).flatMap (fun pos =>
              CNF.encode (exactlyOne ((List.range 4).map
                (vCellF Qc steps P t tp pos))))))))
      (cellsBodyBudget M) := by
    intro i hi
    set base : Fin nT → Tape :=
      Function.update (Function.update work₀ tReg (regT i)) tFuel
        ⟨i + 2, regCells (steps + 1)⟩ with hbase
    have hstate : Function.update
        (Function.update (scratch work₀ tmp tmp2 0) tReg (regT i)) tFuel
        ⟨i + 2, regCells (steps + 1)⟩ = scratch base tmp tmp2 0 := by
      rw [update_scratch (by decide) (by decide),
        update_scratch (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update hwork₀ (regT_parked _))
        (parked_regCells (by omega))
    have hbody' := cellsBodyTM_hoareTime Qc steps P M i hM (by omega) inp₀
      base
      (ys ++ (List.range i).flatMap (fun t =>
        (List.range 3).flatMap (fun tp =>
          (List.range (P + 1)).flatMap (fun pos =>
            CNF.encode (exactlyOne ((List.range 4).map
              (vCellF Qc steps P t tp pos)))))))
      hinp₀ hbaseP
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hrA)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hrB)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hrC)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hrD)
      (by rw [hbase, Function.update_of_ne (by decide), Function.update_self])
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hp1)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hf1)
    rw [hstate]
    refine hbody'.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoop_hoareTime cellsBodyTM tReg tFuel (by decide)
    (steps + 1) M (cellsBodyBudget M) hAM
    (fun t => (List.range 3).flatMap (fun tp =>
      (List.range (P + 1)).flatMap (fun pos =>
        CNF.encode (exactlyOne ((List.range 4).map
          (vCellF Qc steps P t tp pos))))))
    inp₀ (scratch work₀ tmp tmp2 0) ys hinp₀ (scratch_parked 0 hwork₀)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact htFuel)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact htReg)
    hbody
  refine hloop.consequence (fun _ _ _ h => h) ?_ (loop_le_loopBudget hAM)
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, ?_, ?_⟩
  · rw [g2, update_scratch (by decide) (by decide)]
  · simp only [oneHotCellsF, CNF.encode_flatMap]
    exact g3

-- ════════════════════════════════════════════════════════════════════════
-- Family: oneHotHeadsF
-- ════════════════════════════════════════════════════════════════════════

private theorem flatMap_congr {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))]

/-- `atMostOne` over a mapped range as rectangle loops with shrinking inner
    ranges — the shape the head emitter's nested loops produce. -/
theorem atMostOne_map_range : ∀ (m : ℕ) (f : ℕ → ℕ),
    atMostOne ((List.range m).map f)
      = (List.range m).flatMap (fun q =>
          (List.range (m - (q + 1))).map (fun j =>
            ([⟨false, f q⟩, ⟨false, f (q + 1 + j)⟩] : Clause))) := by
  intro m
  induction m with
  | zero => intro f; rfl
  | succ m ih =>
    intro f
    rw [List.range_succ_eq_map, List.map_cons, List.map_map,
      show atMostOne (f 0 :: (List.range m).map (f ∘ Nat.succ))
        = ((List.range m).map (f ∘ Nat.succ)).map
            (fun w => ([⟨false, f 0⟩, ⟨false, w⟩] : Clause))
          ++ atMostOne ((List.range m).map (f ∘ Nat.succ)) from rfl,
      ih (f ∘ Nat.succ), List.flatMap_cons, List.map_map, List.flatMap_map]
    congr 1
    · rw [show m + 1 - (0 + 1) = m from by omega]
      refine List.map_congr_left fun j _ => ?_
      show ([⟨false, f 0⟩, ⟨false, f (j + 1)⟩] : Clause)
        = [⟨false, f 0⟩, ⟨false, f (0 + 1 + j)⟩]
      rw [show 0 + 1 + j = j + 1 from by omega]
    · refine flatMap_congr fun q _ => ?_
      show (List.range (m - (q + 1))).map _
        = (List.range (m + 1 - (q + 1 + 1))).map _
      rw [show m + 1 - (q + 1 + 1) = m - (q + 1) from by omega]
      refine List.map_congr_left fun j _ => ?_
      show ([⟨false, f (q + 1)⟩, ⟨false, f (q + 1 + j + 1)⟩] : Clause)
        = [⟨false, f (q + 1)⟩, ⟨false, f (q + 1 + 1 + j)⟩]
      rw [show q + 1 + 1 + j = q + 1 + j + 1 from by omega]

/-- One head literal: row from `tReg`, tape index hardwired, position from
    `posSrc`. -/
def headLitD (sign : Bool) (tp : ℕ) (posSrc : Fin nT) : LitDesc nT :=
  ⟨sign, 3, .inl tReg, .inr tp, .inl posSrc, .inr 0⟩

/-- The at-least-one head clause: loop the positive literal over all
    positions, close the clause, return the position counter. -/
def headAtLeastTM (tp : ℕ) : TM nT :=
  seqTM
    (emitLoopTM
      (seqTM ((headLitD true tp pos1Reg).tm rA rB rC rD tmp tmp2)
        (resetScratchTM tmp tmp2))
      pos1Reg pos1Fuel)
    (seqTM (emitBitsTM [true, false]) (setConstTM pos1Reg 0))

/-- Budget of the at-least-one head clause. -/
def headAtLeastBudget (M : ℕ) : ℕ :=
  loopBudget M (emitVarBudget M + 1 + (2 * opBudget M + 1)) + 1
    + (2 + 1 + opBudget M)

/-- The head-literal denotation lemma, shared by both head clause shapes. -/
theorem headLitD_spec {tp : ℕ} (htp : tp < 3) {Qc steps P M i pos : ℕ}
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M)
    (hi : i ≤ steps) (hpos : pos ≤ P)
    {posSrc : Fin nT} (hst : posSrc ≠ tmp) (hst2 : posSrc ≠ tmp2)
    {base : Fin nT → Tape} (sgn : Bool)
    (hbt : base tReg = regT i) (hbp : base posSrc = regT pos) :
    LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      (headLitD sgn tp posSrc) ⟨sgn, vHeadF Qc steps P i tp pos⟩ := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega)
    (show i < steps + 1 by omega)
    (show tp < max Qc 3 by omega)
    (show pos < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
  exact ⟨i, tp, pos, 0, ⟨hbt, by decide, by decide⟩, rfl, ⟨hbp, hst, hst2⟩,
    rfl, rfl, rfl, k0, k1, k2, k3, k4⟩

/-- **`headAtLeastTM` Hoare specification** (at row `i`, tape index `tp`). -/
theorem headAtLeastTM_hoareTime (tp : ℕ) (htp : tp < 3) (Qc steps P M i : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M) (hi : i ≤ steps)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regT (steps + 1)) (hVrB : V rB = regT (max Qc 3))
    (hVrC : V rC = regT (P + 2)) (hVrD : V rD = regT 4)
    (hVt : V tReg = regT i)
    (hVp1 : V pos1Reg = regT 0) (hVf1 : V pos1Fuel = regT (P + 1)) :
    (headAtLeastTM tp).HoareTime
      (emitPred inp₀ (scratch V tmp tmp2 0) ys)
      (emitPred inp₀ (scratch V tmp tmp2 0)
        (ys ++ (Clause.encode (atLeastOne ((List.range (P + 1)).map
          (vHeadF Qc steps P i tp))) ++ [true, false])))
      (headAtLeastBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hPM : P + 1 ≤ M := by omega
  have hbody : ∀ j, j < P + 1 →
      (seqTM ((headLitD true tp pos1Reg).tm rA rB rC rD tmp tmp2)
        (resetScratchTM tmp tmp2)).HoareTime
        (emitPred inp₀
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
            ⟨j + 2, regCells (P + 1)⟩)
          (ys ++ (List.range j).flatMap (fun pos =>
            (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word)))
        (emitPred inp₀
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
            ⟨j + 2, regCells (P + 1)⟩)
          (ys ++ (List.range (j + 1)).flatMap (fun pos =>
            (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word)))
        (emitVarBudget M + 1 + (2 * opBudget M + 1)) := by
    intro j hj
    set base : Fin nT → Tape :=
      Function.update (Function.update V pos1Reg (regT j)) pos1Fuel
        ⟨j + 2, regCells (P + 1)⟩ with hbase
    have hstate : Function.update
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT j)) pos1Fuel
        ⟨j + 2, regCells (P + 1)⟩ = scratch base tmp tmp2 0 := by
      rw [update_scratch (by decide) (by decide),
        update_scratch (by decide) (by decide)]
    have hbaseP : ∀ l, Parked (base l) :=
      parked_update (parked_update hV (regT_parked _))
        (parked_regCells (by omega))
    have hbt : base tReg = regT i := by
      rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]
      exact hVt
    have hbp : base pos1Reg = regT j := by
      rw [hbase, Function.update_of_ne (by decide), Function.update_self]
    have hlit := (headLitD_spec htp hM hi (show j ≤ P by omega)
      (by decide) (by decide) true hbt hbp).emit rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hAM hBM hCM hDM 0 (by omega)
      inp₀ (ys ++ (List.range j).flatMap (fun pos =>
        (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word))
      hinp₀ hbaseP
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hVrA)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hVrB)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hVrC)
      (by rw [hbase, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hVrD)
    have hreset := resetScratchTM_hoareTime tmp tmp2 (by decide) M
      (⟨true, vHeadF Qc steps P i tp j⟩ : Lit).var
      (by
        show vHeadF Qc steps P i tp j ≤ M
        obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega)
          (show i < steps + 1 by omega) (show tp < max Qc 3 by omega)
          (show j < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
        exact k4)
      inp₀ base
      (ys ++ (List.range j).flatMap (fun pos =>
        (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word)
        ++ (⟨true, vHeadF Qc steps P i tp j⟩ : Lit).word)
      hinp₀ hbaseP
    have hseq := seqTM_hoareTime _ _ hlit
      (emitPred_transition hinp₀ (scratch_parked _ hbaseP) _) hreset
    rw [hstate]
    refine hseq.consequence (fun _ _ _ h => h) ?_ (by omega)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoop_hoareTime
    (seqTM ((headLitD true tp pos1Reg).tm rA rB rC rD tmp tmp2)
      (resetScratchTM tmp tmp2))
    pos1Reg pos1Fuel (by decide) (P + 1) M
    (emitVarBudget M + 1 + (2 * opBudget M + 1)) hPM
    (fun pos => (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word)
    inp₀ (scratch V tmp tmp2 0) ys hinp₀ (scratch_parked 0 hV)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVf1)
    (by rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1)
    hbody
  set ys' : List Bool := ys ++ (List.range (P + 1)).flatMap (fun pos =>
    (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit).word) with hys'
  have hsep : (emitBitsTM [true, false] : TM nT).HoareTime
      (emitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1))) ys')
      (emitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1)))
        (ys' ++ [true, false]))
      2 :=
    emitBitsTM_hoareTime [true, false] inp₀ _ ys' hinp₀
      (parked_update (scratch_parked 0 hV) (regT_parked _))
  have hset : (setConstTM pos1Reg 0).HoareTime
      (emitPred inp₀
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1)))
        (ys' ++ [true, false]))
      (emitPred inp₀ (scratch V tmp tmp2 0) (ys' ++ [true, false]))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos1Reg 0 (P + 1) inp₀
      (Function.update (scratch V tmp tmp2 0) pos1Reg (regT (P + 1)))
      (ys' ++ [true, false]) hinp₀
      (parked_update (scratch_parked 0 hV) (regT_parked _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (setConstBudget (by omega) hPM))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem,
      show regT 0 = scratch V tmp tmp2 0 pos1Reg from by
        rw [scratch_apply_ne (by decide) (by decide)]; exact hVp1.symm,
      Function.update_eq_self]
  have htail := seqTM_hoareTime (emitBitsTM [true, false])
    (setConstTM pos1Reg 0) hsep
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hV) (regT_parked _)) _) hset
  have hseq := seqTM_hoareTime _ _
    (hloop.mono_bound (loop_le_loopBudget hPM))
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hV) (regT_parked _)) _) htail
  refine hseq.consequence (fun _ _ _ h => h) ?_
    (by rw [headAtLeastBudget])
  rintro inp work out ⟨g1, g2, g3⟩
  refine ⟨g1, g2, ?_⟩
  rw [show atLeastOne ((List.range (P + 1)).map (vHeadF Qc steps P i tp))
      = (List.range (P + 1)).map
          (fun pos => (⟨true, vHeadF Qc steps P i tp pos⟩ : Lit)) from by
    rw [atLeastOne, List.map_map]; rfl,
    Clause.encode_map, ← List.append_assoc]
  exact g3

/-- The pairwise at-most-one clauses: outer loop over the first position;
    per outer step, mirror the counter past it, sweep the (offset,
    shrinking) inner loop, and shrink the fuel. -/
def headPairBodyTM (tp : ℕ) : TM nT :=
  seqTM (copyIntoTM pos1Reg pos2Reg)
    (seqTM (incRegTM pos2Reg)
      (seqTM
        (emitLoopTM
          (emitClauseTM rA rB rC rD tmp tmp2
            [headLitD false tp pos1Reg, headLitD false tp pos2Reg])
          pos2Reg auxReg)
        (seqTM (setConstTM pos2Reg 0) (decRegTM auxReg))))

def headAtMostTM (tp : ℕ) : TM nT :=
  seqTM (emitLoopTM (headPairBodyTM tp) pos1Reg pos1Fuel)
    (setConstTM pos1Reg 0)

/-- Budget of one outer step of the pairwise sweep. -/
def pairBodyBudget (M : ℕ) : ℕ :=
  loopBudget M (clauseBudget 2 M) + 4 * opBudget M + 4

/-- The per-outer-position word of the pairwise sweep. -/
def pairWord (Qc steps P i tp q : ℕ) : List Bool :=
  (List.range (P - q)).flatMap (fun j =>
    Clause.encode
      ([⟨false, vHeadF Qc steps P i tp q⟩,
        ⟨false, vHeadF Qc steps P i tp (q + 1 + j)⟩] : Clause)
      ++ [true, false])

/-- **`headPairBodyTM` Hoare specification** (at row `i`, outer position
    `q`): emits the pair clauses `(q, q')` for all `q' > q`, mirrors the
    counters home, and shrinks the fuel. -/
theorem headPairBodyTM_hoareTime (tp : ℕ) (htp : tp < 3) (Qc steps P M i q : ℕ)
    (hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M) (hi : i ≤ steps)
    (hq : q ≤ P)
    (inp₀ : Tape) (V : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hV : ∀ j, Parked (V j))
    (hVrA : V rA = regT (steps + 1)) (hVrB : V rB = regT (max Qc 3))
    (hVrC : V rC = regT (P + 2)) (hVrD : V rD = regT 4)
    (hVt : V tReg = regT i)
    (hVp2 : V pos2Reg = regT 0) :
    (headPairBodyTM tp).HoareTime
      (emitPred inp₀
        (Function.update
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT q)) auxReg
            (regT (P - q))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩)
        ys)
      (emitPred inp₀
        (Function.update
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT q)) auxReg
            (regT (P - (q + 1)))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩)
        (ys ++ pairWord Qc steps P i tp q))
      (pairBodyBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  set B : Fin nT → Tape :=
    Function.update
      (Function.update (Function.update V pos1Reg (regT q)) auxReg
        (regT (P - q))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩ with hB
  have hstate : Function.update
      (Function.update
        (Function.update (scratch V tmp tmp2 0) pos1Reg (regT q)) auxReg
        (regT (P - q))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩
      = scratch B tmp tmp2 0 := by
    rw [update_scratch (by decide) (by decide),
      update_scratch (by decide) (by decide),
      update_scratch (by decide) (by decide)]
  have hBP : ∀ l, Parked (B l) :=
    parked_update (parked_update (parked_update hV (regT_parked _))
      (regT_parked _)) (parked_regCells (by omega))
  have hBrA : B rA = regT (steps + 1) := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVrA
  have hBrB : B rB = regT (max Qc 3) := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVrB
  have hBrC : B rC = regT (P + 2) := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVrC
  have hBrD : B rD = regT 4 := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVrD
  have hBt : B tReg = regT i := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVt
  have hBp1 : B pos1Reg = regT q := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hBp2 : B pos2Reg = regT 0 := by
    rw [hB, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
    exact hVp2
  have hBaux : B auxReg = regT (P - q) := by
    rw [hB, Function.update_of_ne (by decide), Function.update_self]
  -- Stage 1: pos2 := q.
  have h₁ : (copyIntoTM pos1Reg pos2Reg).HoareTime
      (emitPred inp₀ (scratch B tmp tmp2 0) ys)
      (emitPred inp₀ (scratch (Function.update B pos2Reg (regT q)) tmp tmp2 0)
        ys) (opBudget M) := by
    refine ((copyIntoTM_hoareTime pos1Reg pos2Reg (by decide) q 0 inp₀
      (scratch B tmp tmp2 0) ys hinp₀ (fun l _ => scratch_parked 0 hBP l)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hBp1)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hBp2)
      ).consequence (fun _ _ _ h => h) ?_
      (copyIntoBudget (by omega) (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide)]
  -- Stage 2: pos2 := q + 1.
  have h₂ : (incRegTM pos2Reg).HoareTime
      (emitPred inp₀ (scratch (Function.update B pos2Reg (regT q)) tmp tmp2 0)
        ys)
      (emitPred inp₀
        (scratch (Function.update B pos2Reg (regT (q + 1))) tmp tmp2 0) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime pos2Reg q inp₀
      (scratch (Function.update B pos2Reg (regT q)) tmp tmp2 0) ys hinp₀
      (fun l _ => scratch_parked 0 (parked_update hBP (regT_parked _)) l)
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_ (incBudget (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide), Function.update_idem]
  -- Stage 3: the inner offset sweep.
  set B₂ : Fin nT → Tape := Function.update B pos2Reg (regT (q + 1)) with hB₂
  have hB₂P : ∀ l, Parked (B₂ l) := parked_update hBP (regT_parked _)
  have hinner : ∀ j, j < P - q →
      (emitClauseTM rA rB rC rD tmp tmp2
        [headLitD false tp pos1Reg, headLitD false tp pos2Reg]).HoareTime
        (emitPred inp₀
          (Function.update
            (Function.update (scratch B₂ tmp tmp2 0) pos2Reg
              (regT (q + 1 + j))) auxReg ⟨j + 2, regCells (P - q)⟩)
          (ys ++ (List.range j).flatMap (fun j' =>
            Clause.encode
              ([⟨false, vHeadF Qc steps P i tp q⟩,
                ⟨false, vHeadF Qc steps P i tp (q + 1 + j')⟩] : Clause)
              ++ [true, false])))
        (emitPred inp₀
          (Function.update
            (Function.update (scratch B₂ tmp tmp2 0) pos2Reg
              (regT (q + 1 + j))) auxReg ⟨j + 2, regCells (P - q)⟩)
          (ys ++ (List.range (j + 1)).flatMap (fun j' =>
            Clause.encode
              ([⟨false, vHeadF Qc steps P i tp q⟩,
                ⟨false, vHeadF Qc steps P i tp (q + 1 + j')⟩] : Clause)
              ++ [true, false])))
        (clauseBudget 2 M) := by
    intro j hj
    set C : Fin nT → Tape :=
      Function.update (Function.update B₂ pos2Reg (regT (q + 1 + j))) auxReg
        ⟨j + 2, regCells (P - q)⟩ with hC
    have hstate' : Function.update
        (Function.update (scratch B₂ tmp tmp2 0) pos2Reg (regT (q + 1 + j)))
        auxReg ⟨j + 2, regCells (P - q)⟩ = scratch C tmp tmp2 0 := by
      rw [update_scratch (by decide) (by decide),
        update_scratch (by decide) (by decide)]
    have hCP : ∀ l, Parked (C l) :=
      parked_update (parked_update hB₂P (regT_parked _))
        (parked_regCells (by omega))
    have hCt : C tReg = regT i := by
      rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]
      exact hBt
    have hCp1 : C pos1Reg = regT q := by
      rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]
      exact hBp1
    have hCp2 : C pos2Reg = regT (q + 1 + j) := by
      rw [hC, Function.update_of_ne (by decide), Function.update_self]
    have hf : List.Forall₂
        (LitDesc.Spec C tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
        [headLitD false tp pos1Reg, headLitD false tp pos2Reg]
        ([⟨false, vHeadF Qc steps P i tp q⟩,
          ⟨false, vHeadF Qc steps P i tp (q + 1 + j)⟩] : Clause) :=
      .cons (headLitD_spec htp hM hi (by omega) (by decide) (by decide)
          false hCt hCp1)
        (.cons (headLitD_spec htp hM hi (by omega) (by decide) (by decide)
          false hCt hCp2) .nil)
    have hcl := emitClauseTM_hoareTime rA rB rC rD tmp tmp2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hAM hBM hCM hDM hf (L := 2) (by simp)
      inp₀
      (ys ++ (List.range j).flatMap (fun j' =>
        Clause.encode
          ([⟨false, vHeadF Qc steps P i tp q⟩,
            ⟨false, vHeadF Qc steps P i tp (q + 1 + j')⟩] : Clause)
          ++ [true, false]))
      hinp₀ hCP
      (by rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]; exact hBrA)
      (by rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]; exact hBrB)
      (by rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]; exact hBrC)
      (by rw [hC, Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hB₂,
        Function.update_of_ne (by decide)]; exact hBrD)
    rw [hstate']
    refine hcl.strengthen_post ?_
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [flatMap_range_succ, ← List.append_assoc]
    exact g3
  have hloop := emitLoopFrom_hoareTime
    (emitClauseTM rA rB rC rD tmp tmp2
      [headLitD false tp pos1Reg, headLitD false tp pos2Reg])
    pos2Reg auxReg (by decide) (q + 1) (P - q) M (clauseBudget 2 M)
    (by omega)
    (fun j' => Clause.encode
      ([⟨false, vHeadF Qc steps P i tp q⟩,
        ⟨false, vHeadF Qc steps P i tp (q + 1 + j')⟩] : Clause)
      ++ [true, false])
    inp₀ (scratch B₂ tmp tmp2 0) ys hinp₀ (scratch_parked 0 hB₂P)
    (by rw [scratch_apply_ne (by decide) (by decide), hB₂,
      Function.update_of_ne (by decide)]; exact hBaux)
    (by rw [scratch_apply_ne (by decide) (by decide), hB₂,
      Function.update_self])
    hinner
  -- Stage 4: pos2 := 0.
  have h₄ : (setConstTM pos2Reg 0).HoareTime
      (emitPred inp₀
        (Function.update (scratch B₂ tmp tmp2 0) pos2Reg
          (regT (q + 1 + (P - q))))
        (ys ++ pairWord Qc steps P i tp q))
      (emitPred inp₀ (scratch B tmp tmp2 0)
        (ys ++ pairWord Qc steps P i tp q))
      (opBudget M) := by
    refine ((setConstTM_hoareTime pos2Reg 0 (q + 1 + (P - q)) inp₀
      (Function.update (scratch B₂ tmp tmp2 0) pos2Reg
        (regT (q + 1 + (P - q))))
      (ys ++ pairWord Qc steps P i tp q) hinp₀
      (parked_update (scratch_parked 0 hB₂P) (regT_parked _))
      (by rw [Function.update_self])).consequence
      (fun _ _ _ h => h) ?_ (setConstBudget (by omega) (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, Function.update_idem, update_scratch (by decide) (by decide), hB₂,
      Function.update_idem,
      show regT 0 = B pos2Reg from hBp2.symm, Function.update_eq_self]
  -- Stage 5: shrink the fuel.
  have h₅ : (decRegTM auxReg).HoareTime
      (emitPred inp₀ (scratch B tmp tmp2 0)
        (ys ++ pairWord Qc steps P i tp q))
      (emitPred inp₀
        (Function.update
          (Function.update
            (Function.update (scratch V tmp tmp2 0) pos1Reg (regT q)) auxReg
            (regT (P - (q + 1)))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩)
        (ys ++ pairWord Qc steps P i tp q))
      (opBudget M) := by
    refine ((decRegTM_hoareTime auxReg (P - q) inp₀ (scratch B tmp tmp2 0)
      (ys ++ pairWord Qc steps P i tp q) hinp₀
      (fun l _ => scratch_parked 0 hBP l)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hBaux)
      ).consequence (fun _ _ _ h => h) ?_ (incBudget (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide), hB,
      show P - q - 1 = P - (q + 1) from by omega]
    rw [show Function.update
        (Function.update
          (Function.update (Function.update V pos1Reg (regT q)) auxReg
            (regT (P - q))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩) auxReg
        (regT (P - (q + 1)))
      = Function.update
          (Function.update (Function.update V pos1Reg (regT q)) auxReg
            (regT (P - (q + 1)))) pos1Fuel ⟨q + 2, regCells (P + 1)⟩ from by
      rw [Function.update_comm (show pos1Fuel ≠ auxReg by decide),
        Function.update_idem]]
    rw [update_scratch (by decide) (by decide),
      update_scratch (by decide) (by decide),
      update_scratch (by decide) (by decide)]
  -- Glue.
  have h₄₅ := seqTM_hoareTime (setConstTM pos2Reg 0) (decRegTM auxReg) h₄
    (emitPred_transition hinp₀ (scratch_parked 0 hBP) _) h₅
  have h₃₄₅ := seqTM_hoareTime
    (emitLoopTM
      (emitClauseTM rA rB rC rD tmp tmp2
        [headLitD false tp pos1Reg, headLitD false tp pos2Reg])
      pos2Reg auxReg)
    (seqTM (setConstTM pos2Reg 0) (decRegTM auxReg))
    ((hloop.mono_bound (loop_le_loopBudget (by omega))).strengthen_post
      (by
        rintro inp work out ⟨g1, g2, g3⟩
        exact ⟨g1, g2, g3⟩))
    (emitPred_transition hinp₀
      (parked_update (scratch_parked 0 hB₂P) (regT_parked _)) _) h₄₅
  have h₂₃₄₅ := seqTM_hoareTime (incRegTM pos2Reg) _ h₂
    (emitPred_transition hinp₀ (scratch_parked 0 hB₂P) _) h₃₄₅
  have hall := seqTM_hoareTime (copyIntoTM pos1Reg pos2Reg) _ h₁
    (emitPred_transition hinp₀
      (scratch_parked 0 (parked_update hBP (regT_parked _))) _) h₂₃₄₅
  rw [hstate]
  refine hall.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) ?_
  rw [pairBodyBudget]
  omega

end SAT
