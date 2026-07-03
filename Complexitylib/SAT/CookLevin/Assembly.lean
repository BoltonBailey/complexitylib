import Complexitylib.SAT.CookLevin.EmitterActive

/-!
# The reduction emitter, assembled

`emitTM N p` computes the Cook–Levin reduction: bump the tapes, measure
the input, evaluate the time polynomial, initialize the radix and fuel
registers, and emit the seven encoded clause families of
`tableauCNFFlat N (p.eval |x|) x`.
-/

namespace SAT

open _root_.TM Tableau

open Emit

/-- The register file after initialization (`tf` = the row-loop fuel). -/
def initVals (n steps P Qc tf : ℕ) : Fin nT → ℕ := fun i =>
  if i = tFuel then tf
  else if i = nReg then n
  else if i = stepsReg then steps
  else if i = pReg then P
  else if i = rA then steps + 1
  else if i = rB then max Qc 3
  else if i = rC then P + 2
  else if i = rD then 4
  else if i = pos1Fuel then P + 1
  else if i = pos2Fuel then P
  else if i = pos3Fuel then P
  else 0

/-- The corresponding tape file. -/
def initTapes (n steps P Qc tf : ℕ) : Fin nT → Tape :=
  fun i => regT (initVals n steps P Qc tf i)

theorem initTapes_parked (n steps P Qc tf : ℕ) :
    ∀ i, Parked (initTapes n steps P Qc tf i) :=
  fun _ => regT_parked _

/-- **The register initialization chain**: input length, time polynomial,
    tableau width, radices, and position fuels. -/
noncomputable def emitInitTM (N : NTM 1) (p : Polynomial ℕ) : TM nT :=
  seqTM (inputLenRegTM nReg)
    (seqTM (polyEvalTM nReg stepsReg tmp2 p)
      (seqTM (setConstTM tmp2 0)
        (seqTM (addIntoTM stepsReg pReg)
          (seqTM (addIntoTM nReg pReg)
            (seqTM (incRegTM pReg)
              (seqTM (copyIntoTM stepsReg rA)
                (seqTM (incRegTM rA)
                  (seqTM (setConstTM rB (max (Fintype.card N.Q) 3))
                    (seqTM (copyIntoTM pReg rC)
                      (seqTM (incRegTM rC)
                        (seqTM (incRegTM rC)
                          (seqTM (setConstTM rD 4)
                            (seqTM (copyIntoTM pReg pos1Fuel)
                              (seqTM (incRegTM pos1Fuel)
                                (seqTM (copyIntoTM pReg pos2Fuel)
                                  (copyIntoTM pReg pos3Fuel))))))))))))))))

/-- Budget of the initialization chain: the polynomial evaluation plus
    sixteen register operations. -/
def initBudget (Mp M : ℕ) (p : Polynomial ℕ) : ℕ :=
  opBudget M + 1
    + (opBudget Mp + 1 + ((p.natDegree + 1) * (layerBudget Mp + 1) + 1) + 1
      + (opBudget M + 1
        + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
          + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
            + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
              + (opBudget M + 1 + (opBudget M + 1 + (opBudget M + 1
                + (opBudget M + 1 + opBudget M)))))))))))))))

set_option maxHeartbeats 1600000 in
/-- **`emitInitTM` Hoare specification.** From the bumped all-zero register
    file, reach the initialized file; `Mp` caps the Horner evaluation,
    `M` the tableau values. -/
theorem emitInitTM_hoareTime (N : NTM 1) (p : Polynomial ℕ) (x : List Bool)
    (steps P Mp M : ℕ)
    (hsteps : steps = p.eval x.length) (hP : P = steps + x.length + 1)
    (hMp : ∀ k, k ≤ p.natDegree + 1 →
      hornerFold x.length (List.take k (polyCoeffs p)) 0 ≤ Mp)
    (hnMp : x.length ≤ Mp)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (ys : List Bool) :
    (emitInitTM N p).HoareTime
      (emitPred ⟨1, (initTape (x.map Γ.ofBool)).cells⟩ (fun _ => regT 0) ys)
      (emitPred ⟨1, (initTape (x.map Γ.ofBool)).cells⟩
        (initTapes x.length steps P (Fintype.card N.Q) 0) ys)
      (initBudget Mp M p) := by
  set inp₁ : Tape := ⟨1, (initTape (x.map Γ.ofBool)).cells⟩ with hinp₁
  have hinp₀ : Parked inp₁ := parked_init_input x
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hstepsM : steps ≤ M := by omega
  have hPMle : P + 1 ≤ M := by omega
  have hnM : x.length ≤ M := by omega
  have hstepsMp : steps ≤ Mp := by
    have := hMp (p.natDegree + 1) (le_refl _)
    rw [List.take_of_length_le (by rw [polyCoeffs_length])] at this
    rw [hsteps, ← hornerFold_polyCoeffs]
    exact this
  -- Stage 1: nReg := |x|.
  have h₁ : (inputLenRegTM nReg : TM nT).HoareTime
      (emitPred inp₁ (fun _ => regT 0) ys)
      (emitPred inp₁ (Function.update (fun _ => regT 0) nReg
        (regT x.length)) ys)
      (opBudget M) :=
    (inputLenRegTM_hoareTime nReg x (fun _ => regT 0) ys
      (fun _ _ => regT_parked 0) rfl).mono_bound
      (le_opBudget_of_le (by nlinarith))
  set W₁ : Fin nT → Tape :=
    Function.update (fun _ => regT 0) nReg (regT x.length) with hW₁
  have hW₁P : ∀ i, Parked (W₁ i) :=
    parked_update (fun _ => regT_parked 0) (regT_parked _)
  -- Stage 2: stepsReg := p.eval |x|.
  have h₂ := polyEvalTM_hoareTime nReg stepsReg tmp2 (by decide) (by decide)
    (by decide) p Mp x.length 0 0 hnMp (by omega) (by omega) hMp inp₁ W₁ ys
    hinp₀ hW₁P
    (by rw [hW₁, Function.update_self])
    (by rw [hW₁, Function.update_of_ne (by decide)])
    (by rw [hW₁, Function.update_of_ne (by decide)])
  rw [← hsteps] at h₂
  set W₂ : Fin nT → Tape :=
    Function.update (Function.update W₁ tmp2 (regT steps)) stepsReg
      (regT steps) with hW₂
  have hW₂P : ∀ i, Parked (W₂ i) :=
    parked_update (parked_update hW₁P (regT_parked _)) (regT_parked _)
  -- Stage 3: tmp2 := 0.
  have h₃ : (setConstTM tmp2 0 : TM nT).HoareTime
      (emitPred inp₁ W₂ ys)
      (emitPred inp₁ (Function.update W₂ tmp2 (regT 0)) ys) (opBudget M) := by
    refine ((setConstTM_hoareTime tmp2 0 steps inp₁ W₂ ys hinp₀ hW₂P
      (by show W₂ tmp2 = regT steps; rw [hW₂, hW₁]; rfl)).mono_bound
      (setConstBudget (show (0:ℕ) ≤ M by omega) hstepsM))
  set W₃ : Fin nT → Tape := Function.update W₂ tmp2 (regT 0) with hW₃
  have hW₃P : ∀ i, Parked (W₃ i) := parked_update hW₂P (regT_parked _)
  -- Stage 4: pReg += steps.
  have h₄ : (addIntoTM stepsReg pReg : TM nT).HoareTime
      (emitPred inp₁ W₃ ys)
      (emitPred inp₁ (Function.update W₃ pReg (regT steps)) ys)
      (opBudget M) := by
    refine ((addIntoTM_hoareTime stepsReg pReg (by decide) steps 0 inp₁ W₃ ys
      hinp₀ (fun i _ => hW₃P i)
      (by show W₃ stepsReg = regT steps; rw [hW₃, hW₂, hW₁]; rfl)
      (by show W₃ pReg = regT 0; rw [hW₃, hW₂, hW₁]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (addIntoBudget hstepsM (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, Nat.zero_add], g3⟩
  set W₄ : Fin nT → Tape := Function.update W₃ pReg (regT steps) with hW₄
  have hW₄P : ∀ i, Parked (W₄ i) := parked_update hW₃P (regT_parked _)
  -- Stage 5: pReg += |x|.
  have h₅ : (addIntoTM nReg pReg : TM nT).HoareTime
      (emitPred inp₁ W₄ ys)
      (emitPred inp₁ (Function.update W₄ pReg (regT (steps + x.length))) ys)
      (opBudget M) :=
    ((addIntoTM_hoareTime nReg pReg (by decide) x.length steps inp₁ W₄ ys
      hinp₀ (fun i _ => hW₄P i)
      (by show W₄ nReg = regT x.length; rw [hW₄, hW₃, hW₂, hW₁]; rfl)
      (by show W₄ pReg = regT steps; rw [hW₄]; rfl)).mono_bound
      (addIntoBudget hnM (by omega)))
  set W₅ : Fin nT → Tape :=
    Function.update W₄ pReg (regT (steps + x.length)) with hW₅
  have hW₅P : ∀ i, Parked (W₅ i) := parked_update hW₄P (regT_parked _)
  -- Stage 6: pReg += 1 (pReg = P).
  have h₆ : (incRegTM pReg : TM nT).HoareTime
      (emitPred inp₁ W₅ ys)
      (emitPred inp₁ (Function.update W₅ pReg (regT P)) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime pReg (steps + x.length) inp₁ W₅ ys hinp₀
      (fun i _ => hW₅P i)
      (by show W₅ pReg = regT (steps + x.length); rw [hW₅]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (incBudget (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, show steps + x.length + 1 = P from hP.symm], g3⟩
  set W₆ : Fin nT → Tape := Function.update W₅ pReg (regT P) with hW₆
  have hW₆P : ∀ i, Parked (W₆ i) := parked_update hW₅P (regT_parked _)
  -- Stage 7: rA := steps.
  have h₇ : (copyIntoTM stepsReg rA : TM nT).HoareTime
      (emitPred inp₁ W₆ ys)
      (emitPred inp₁ (Function.update W₆ rA (regT steps)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime stepsReg rA (by decide) steps 0 inp₁ W₆ ys hinp₀
      (fun i _ => hW₆P i)
      (by show W₆ stepsReg = regT steps; rw [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)
      (by show W₆ rA = regT 0; rw [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoBudget hstepsM (by omega)))
  set W₇ : Fin nT → Tape := Function.update W₆ rA (regT steps) with hW₇
  have hW₇P : ∀ i, Parked (W₇ i) := parked_update hW₆P (regT_parked _)
  -- Stage 8: rA += 1.
  have h₈ : (incRegTM rA : TM nT).HoareTime
      (emitPred inp₁ W₇ ys)
      (emitPred inp₁ (Function.update W₇ rA (regT (steps + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime rA steps inp₁ W₇ ys hinp₀ (fun i _ => hW₇P i)
      (by show W₇ rA = regT steps; rw [hW₇]; rfl)).mono_bound
      (incBudget hstepsM))
  set W₈ : Fin nT → Tape := Function.update W₇ rA (regT (steps + 1)) with hW₈
  have hW₈P : ∀ i, Parked (W₈ i) := parked_update hW₇P (regT_parked _)
  -- Stage 9: rB := max Qc 3.
  have h₉ : (setConstTM rB (max (Fintype.card N.Q) 3) : TM nT).HoareTime
      (emitPred inp₁ W₈ ys)
      (emitPred inp₁
        (Function.update W₈ rB (regT (max (Fintype.card N.Q) 3))) ys)
      (opBudget M) :=
    ((setConstTM_hoareTime rB (max (Fintype.card N.Q) 3) 0 inp₁ W₈ ys hinp₀
      hW₈P
      (by show W₈ rB = regT 0; rw [hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (setConstBudget hBM (by omega)))
  set W₉ : Fin nT → Tape :=
    Function.update W₈ rB (regT (max (Fintype.card N.Q) 3)) with hW₉
  have hW₉P : ∀ i, Parked (W₉ i) := parked_update hW₈P (regT_parked _)
  -- Stage 10: rC := P.
  have h₁₀ : (copyIntoTM pReg rC : TM nT).HoareTime
      (emitPred inp₁ W₉ ys)
      (emitPred inp₁ (Function.update W₉ rC (regT P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg rC (by decide) P 0 inp₁ W₉ ys hinp₀
      (fun i _ => hW₉P i)
      (by show W₉ pReg = regT P; rw [hW₉, hW₈, hW₇, hW₆]; rfl)
      (by show W₉ rC = regT 0
          rw [hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoBudget (by omega) (by omega)))
  set W₁₀ : Fin nT → Tape := Function.update W₉ rC (regT P) with hW₁₀
  have hW₁₀P : ∀ i, Parked (W₁₀ i) := parked_update hW₉P (regT_parked _)
  -- Stage 11: rC += 1.
  have h₁₁ : (incRegTM rC : TM nT).HoareTime
      (emitPred inp₁ W₁₀ ys)
      (emitPred inp₁ (Function.update W₁₀ rC (regT (P + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime rC P inp₁ W₁₀ ys hinp₀ (fun i _ => hW₁₀P i)
      (by show W₁₀ rC = regT P; rw [hW₁₀]; rfl)).mono_bound
      (incBudget (by omega)))
  set W₁₁ : Fin nT → Tape := Function.update W₁₀ rC (regT (P + 1)) with hW₁₁
  have hW₁₁P : ∀ i, Parked (W₁₁ i) := parked_update hW₁₀P (regT_parked _)
  -- Stage 12: rC += 1 (rC = P + 2).
  have h₁₂ : (incRegTM rC : TM nT).HoareTime
      (emitPred inp₁ W₁₁ ys)
      (emitPred inp₁ (Function.update W₁₁ rC (regT (P + 2))) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime rC (P + 1) inp₁ W₁₁ ys hinp₀
      (fun i _ => hW₁₁P i)
      (by show W₁₁ rC = regT (P + 1); rw [hW₁₁]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (incBudget hPMle))
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
  set W₁₂ : Fin nT → Tape := Function.update W₁₁ rC (regT (P + 2)) with hW₁₂
  have hW₁₂P : ∀ i, Parked (W₁₂ i) := parked_update hW₁₁P (regT_parked _)
  -- Stage 13: rD := 4.
  have h₁₃ : (setConstTM rD 4 : TM nT).HoareTime
      (emitPred inp₁ W₁₂ ys)
      (emitPred inp₁ (Function.update W₁₂ rD (regT 4)) ys)
      (opBudget M) :=
    ((setConstTM_hoareTime rD 4 0 inp₁ W₁₂ ys hinp₀ hW₁₂P
      (by show W₁₂ rD = regT 0
          rw [hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (setConstBudget hDM (by omega)))
  set W₁₃ : Fin nT → Tape := Function.update W₁₂ rD (regT 4) with hW₁₃
  have hW₁₃P : ∀ i, Parked (W₁₃ i) := parked_update hW₁₂P (regT_parked _)
  -- Stage 14: pos1Fuel := P.
  have h₁₄ : (copyIntoTM pReg pos1Fuel : TM nT).HoareTime
      (emitPred inp₁ W₁₃ ys)
      (emitPred inp₁ (Function.update W₁₃ pos1Fuel (regT P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos1Fuel (by decide) P 0 inp₁ W₁₃ ys hinp₀
      (fun i _ => hW₁₃P i)
      (by show W₁₃ pReg = regT P
          rw [hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₃ pos1Fuel = regT 0
          rw [hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃,
            hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoBudget (by omega) (by omega)))
  set W₁₄ : Fin nT → Tape :=
    Function.update W₁₃ pos1Fuel (regT P) with hW₁₄
  have hW₁₄P : ∀ i, Parked (W₁₄ i) := parked_update hW₁₃P (regT_parked _)
  -- Stage 15: pos1Fuel += 1.
  have h₁₅ : (incRegTM pos1Fuel : TM nT).HoareTime
      (emitPred inp₁ W₁₄ ys)
      (emitPred inp₁ (Function.update W₁₄ pos1Fuel (regT (P + 1))) ys)
      (opBudget M) :=
    ((incRegTM_hoareTime pos1Fuel P inp₁ W₁₄ ys hinp₀ (fun i _ => hW₁₄P i)
      (by show W₁₄ pos1Fuel = regT P; rw [hW₁₄]; rfl)).mono_bound
      (incBudget (by omega)))
  set W₁₅ : Fin nT → Tape :=
    Function.update W₁₄ pos1Fuel (regT (P + 1)) with hW₁₅
  have hW₁₅P : ∀ i, Parked (W₁₅ i) := parked_update hW₁₄P (regT_parked _)
  -- Stage 16: pos2Fuel := P.
  have h₁₆ : (copyIntoTM pReg pos2Fuel : TM nT).HoareTime
      (emitPred inp₁ W₁₅ ys)
      (emitPred inp₁ (Function.update W₁₅ pos2Fuel (regT P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos2Fuel (by decide) P 0 inp₁ W₁₅ ys hinp₀
      (fun i _ => hW₁₅P i)
      (by show W₁₅ pReg = regT P
          rw [hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₅ pos2Fuel = regT 0
          rw [hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅,
            hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoBudget (by omega) (by omega)))
  set W₁₆ : Fin nT → Tape :=
    Function.update W₁₅ pos2Fuel (regT P) with hW₁₆
  have hW₁₆P : ∀ i, Parked (W₁₆ i) := parked_update hW₁₅P (regT_parked _)
  -- Stage 17: pos3Fuel := P.
  have h₁₇ : (copyIntoTM pReg pos3Fuel : TM nT).HoareTime
      (emitPred inp₁ W₁₆ ys)
      (emitPred inp₁ (Function.update W₁₆ pos3Fuel (regT P)) ys)
      (opBudget M) :=
    ((copyIntoTM_hoareTime pReg pos3Fuel (by decide) P 0 inp₁ W₁₆ ys hinp₀
      (fun i _ => hW₁₆P i)
      (by show W₁₆ pReg = regT P
          rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆]
          rfl)
      (by show W₁₆ pos3Fuel = regT 0
          rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆,
            hW₅, hW₄, hW₃, hW₂, hW₁]
          rfl)).mono_bound
      (copyIntoBudget (by omega) (by omega)))
  -- The final file is the initialized one.
  have hfinal : Function.update W₁₆ pos3Fuel (regT P)
      = initTapes x.length steps P (Fintype.card N.Q) 0 := by
    rw [hW₁₆, hW₁₅, hW₁₄, hW₁₃, hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅,
      hW₄, hW₃, hW₂, hW₁]
    funext i
    fin_cases i <;> rfl
  rw [hfinal] at h₁₇
  -- Glue the seventeen stages.
  have c₁₇ := h₁₇
  have c₁₆ := seqTM_hoareTime _ _ h₁₆
    (emitPred_transition hinp₀ hW₁₆P _) c₁₇
  have c₁₅ := seqTM_hoareTime _ _ h₁₅
    (emitPred_transition hinp₀ hW₁₅P _) c₁₆
  have c₁₄ := seqTM_hoareTime _ _ h₁₄
    (emitPred_transition hinp₀ hW₁₄P _) c₁₅
  have c₁₃ := seqTM_hoareTime _ _ h₁₃
    (emitPred_transition hinp₀ hW₁₃P _) c₁₄
  have c₁₂ := seqTM_hoareTime _ _ h₁₂
    (emitPred_transition hinp₀ hW₁₂P _) c₁₃
  have c₁₁ := seqTM_hoareTime _ _ h₁₁
    (emitPred_transition hinp₀ hW₁₁P _) c₁₂
  have c₁₀ := seqTM_hoareTime _ _ h₁₀
    (emitPred_transition hinp₀ hW₁₀P _) c₁₁
  have c₉ := seqTM_hoareTime _ _ h₉
    (emitPred_transition hinp₀ hW₉P _) c₁₀
  have c₈ := seqTM_hoareTime _ _ h₈
    (emitPred_transition hinp₀ hW₈P _) c₉
  have c₇ := seqTM_hoareTime _ _ h₇
    (emitPred_transition hinp₀ hW₇P _) c₈
  have c₆ := seqTM_hoareTime _ _ h₆
    (emitPred_transition hinp₀ hW₆P _) c₇
  have c₅ := seqTM_hoareTime _ _ h₅
    (emitPred_transition hinp₀ hW₅P _) c₆
  have c₄ := seqTM_hoareTime _ _ h₄
    (emitPred_transition hinp₀ hW₄P _) c₅
  have c₃ := seqTM_hoareTime _ _ h₃
    (emitPred_transition hinp₀ hW₃P _) c₄
  have c₂ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hinp₀
      (parked_update (parked_update hW₁P (regT_parked _)) (regT_parked _)) _)
    c₃
  have c₁ := seqTM_hoareTime _ _ h₁
    (emitPred_transition hinp₀ hW₁P _) c₂
  exact c₁.mono_bound (by rw [initBudget])


-- ════════════════════════════════════════════════════════════════════════
-- The family chain
-- ════════════════════════════════════════════════════════════════════════

theorem initTapes_update_tFuel (n steps P Qc tf tf' : ℕ) :
    Function.update (initTapes n steps P Qc tf) tFuel (regT tf')
      = initTapes n steps P Qc tf' := by
  funext i
  by_cases hi : i = tFuel
  · subst hi
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne hi]
    show regT (initVals n steps P Qc tf i) = regT (initVals n steps P Qc tf' i)
    congr 1
    rw [initVals, initVals, if_neg hi, if_neg hi]

theorem scratch_initTapes (n steps P Qc tf : ℕ) :
    scratch (initTapes n steps P Qc tf) tmp tmp2 0
      = initTapes n steps P Qc tf := by
  funext i
  by_cases h1 : i = tmp
  · subst h1
    rw [scratch_apply_tmp]
    rfl
  · by_cases h2 : i = tmp2
    · subst h2
      rw [scratch_apply_tmp2 (by decide)]
      rfl
    · rw [scratch_apply_ne h1 h2]

/-- **The family chain**: fuel setups, the seven families, counter resets. -/
noncomputable def emitBodyTM (N : NTM 1) : TM nT :=
  seqTM (copyIntoTM stepsReg tFuel)
    (seqTM (incRegTM tFuel)
      (seqTM (emitOneHotStatesTM (Fintype.card N.Q))
        (seqTM (setConstTM tReg 0)
          (seqTM emitOneHotCellsTM
            (seqTM (setConstTM tReg 0)
              (seqTM emitOneHotHeadsTM
                (seqTM (emitStartTM N)
                  (seqTM (setConstTM tReg 0)
                    (seqTM (copyIntoTM stepsReg tFuel)
                      (seqTM emitFrameTM
                        (seqTM (setConstTM tReg 0)
                          (seqTM (setConstTM tPlusReg 0)
                            (seqTM (emitActiveTM N)
                              (emitAcceptTM N))))))))))))))

/-- Budget of the family chain. -/
def bodyBudget (N : NTM 1) (M : ℕ) : ℕ :=
  opBudget M + 1 + (opBudget M + 1
    + (loopBudget M (cnfBudget (1 + M * M) (M + 2) M) + 1 + (opBudget M + 1
      + (loopBudget M (cellsBodyBudget M) + 1 + (opBudget M + 1
        + (loopBudget M (headsBodyBudget M) + 1 + (startBudget M + 1
          + (opBudget M + 1 + (opBudget M + 1
            + (loopBudget M (frameRowBudget M) + 1 + (opBudget M + 1
              + (opBudget M + 1 + (loopBudget M (activeRowBudget N M) + 1
                + cnfBudget 2 1 M)))))))))))))

set_option maxHeartbeats 4000000 in
/-- **`emitBodyTM` Hoare specification**: from the initialized register file
    and empty accumulator, emit the encoded flat tableau. -/
theorem emitBodyTM_hoareTime (N : NTM 1) (x : List Bool) (steps P M : ℕ)
    (hP : P = steps + x.length + 1)
    (hM : 4 * (steps + 1) * (max (Fintype.card N.Q) 3) * (P + 2) * 4 ≤ M)
    (ys : List Bool) :
    (emitBodyTM N).HoareTime
      (emitPred ⟨1, (initTape (x.map Γ.ofBool)).cells⟩
        (initTapes x.length steps P (Fintype.card N.Q) 0) ys)
      (fun inp work out => inp = ⟨1, (initTape (x.map Γ.ofBool)).cells⟩ ∧
        outAcc (ys ++ CNF.encode (tableauCNFFlat N steps x)) out)
      (bodyBudget N M) := by
  set n : ℕ := x.length with hn
  set Qc : ℕ := Fintype.card N.Q with hQc
  set inp₁ : Tape := ⟨1, (initTape (x.map Γ.ofBool)).cells⟩ with hinp₁
  have hinp₀ : Parked inp₁ := parked_init_input x
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hM
  have hstepsM : steps ≤ M := by omega
  set W : ℕ → Fin nT → Tape := fun tf => initTapes n steps P Qc tf with hW
  have hWP : ∀ tf i, Parked (W tf i) := fun tf i => regT_parked _
  have hSW : ∀ tf, scratch (W tf) tmp tmp2 0 = W tf := fun tf =>
    scratch_initTapes ..
  -- g1a: tFuel := steps.
  have g1a : (copyIntoTM stepsReg tFuel : TM nT).HoareTime
      (emitPred inp₁ (W 0) ys) (emitPred inp₁ (W steps) ys) (opBudget M) := by
    refine ((copyIntoTM_hoareTime stepsReg tFuel (by decide) steps 0 inp₁
      (W 0) ys hinp₀ (fun i _ => hWP 0 i) rfl rfl).consequence
      (fun _ _ _ h => h) ?_ (copyIntoBudget hstepsM (by omega)))
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hW, initTapes_update_tFuel], u3⟩
  -- g1b: tFuel := steps + 1.
  have g1b : (incRegTM tFuel : TM nT).HoareTime
      (emitPred inp₁ (W steps) ys) (emitPred inp₁ (W (steps + 1)) ys)
      (opBudget M) := by
    refine ((incRegTM_hoareTime tFuel steps inp₁ (W steps) ys hinp₀
      (fun i _ => hWP steps i) rfl).consequence
      (fun _ _ _ h => h) ?_ (incBudget hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hW, initTapes_update_tFuel], u3⟩
  -- f1: the state one-hots.
  have f1 := emitOneHotStatesTM_hoareTime N steps P M hM inp₁ (W (steps + 1))
    ys hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl
  set ys₁ : List Bool := ys ++ CNF.encode (oneHotStatesF N steps P) with hys₁
  -- g2: tReg := 0.
  have g2 : (setConstTM tReg 0 : TM nT).HoareTime
      (emitPred inp₁
        (scratch (Function.update (W (steps + 1)) tReg (regT (steps + 1)))
          tmp tmp2 0) ys₁)
      (emitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₁)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch (Function.update (W (steps + 1)) tReg (regT (steps + 1)))
        tmp tmp2 0) ys₁ hinp₀
      (scratch_parked 0 (parked_update (hWP _) (regT_parked _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), Function.update_idem,
      show regT 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- f2: the cell one-hots.
  have f2 := emitOneHotCellsTM_hoareTime Qc steps P M hM inp₁ (W (steps + 1))
    ys₁ hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₂ : List Bool := ys₁ ++ CNF.encode (oneHotCellsF Qc steps P) with hys₂
  -- g3: tReg := 0.
  have g3 : (setConstTM tReg 0 : TM nT).HoareTime
      (emitPred inp₁
        (scratch (Function.update (W (steps + 1)) tReg (regT (steps + 1)))
          tmp tmp2 0) ys₂)
      (emitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₂)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch (Function.update (W (steps + 1)) tReg (regT (steps + 1)))
        tmp tmp2 0) ys₂ hinp₀
      (scratch_parked 0 (parked_update (hWP _) (regT_parked _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), Function.update_idem,
      show regT 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- f3: the head one-hots.
  have f3 := emitOneHotHeadsTM_hoareTime Qc steps P M hM inp₁ (W (steps + 1))
    ys₂ hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₃ : List Bool := ys₂ ++ CNF.encode (oneHotHeadsF Qc steps P) with hys₃
  -- f4: the start clauses (at the row-counter-dirty state).
  set V3 : Fin nT → Tape :=
    Function.update (W (steps + 1)) tReg (regT (steps + 1)) with hV3
  have hV3P : ∀ i, Parked (V3 i) := parked_update (hWP _) (regT_parked _)
  have f4 := emitStartTM_hoareTime N x steps P M hP hM inp₁ V3 ys₃ hinp₀ rfl
    (by rw [hinp₁]; rfl)
    (fun pos => by
      show (initTape (x.map Γ.ofBool)).cells pos = initCellSym x 0 pos
      rw [initTape, initCellSym]
      simp)
    hV3P
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
    (by rw [hV3, Function.update_of_ne (by decide)]; rfl)
  set ys₄ : List Bool := ys₃ ++ CNF.encode (startClausesF N steps x) with hys₄
  -- g4a: tReg := 0.
  have g4a : (setConstTM tReg 0 : TM nT).HoareTime
      (emitPred inp₁ (scratch V3 tmp tmp2 0) ys₄)
      (emitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 (steps + 1) inp₁
      (scratch V3 tmp tmp2 0) ys₄ hinp₀ (scratch_parked 0 hV3P)
      (by rw [scratch_apply_ne (by decide) (by decide), hV3,
        Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), hV3,
      Function.update_idem,
      show regT 0 = W (steps + 1) tReg from rfl, Function.update_eq_self]
  -- g4b: tFuel := steps.
  have g4b : (copyIntoTM stepsReg tFuel : TM nT).HoareTime
      (emitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄)
      (emitPred inp₁ (scratch (W steps) tmp tmp2 0) ys₄)
      (opBudget M) := by
    refine ((copyIntoTM_hoareTime stepsReg tFuel (by decide) steps (steps + 1)
      inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys₄ hinp₀
      (fun i _ => scratch_parked 0 (hWP _) i)
      (by rw [scratch_apply_ne (by decide) (by decide)]; rfl)
      (by rw [scratch_apply_ne (by decide) (by decide)]; rfl)).consequence
      (fun _ _ _ h => h) ?_ (copyIntoBudget hstepsM hAM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), hW,
      initTapes_update_tFuel]
  -- f5: the frame clauses.
  have f5 := emitFrameTM_hoareTime Qc steps P M hM inp₁ (W steps) ys₄ hinp₀
    (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₅ : List Bool := ys₄ ++ CNF.encode (frameClausesF Qc steps P) with hys₅
  -- g5a: tReg := 0.
  set V5 : Fin nT → Tape :=
    Function.update (Function.update (W steps) tReg (regT steps)) tPlusReg
      (regT steps) with hV5
  have hV5P : ∀ i, Parked (V5 i) :=
    parked_update (parked_update (hWP _) (regT_parked _)) (regT_parked _)
  have g5a : (setConstTM tReg 0 : TM nT).HoareTime
      (emitPred inp₁ (scratch V5 tmp tmp2 0) ys₅)
      (emitPred inp₁
        (scratch (Function.update (W steps) tPlusReg (regT steps)) tmp tmp2 0)
        ys₅)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tReg 0 steps inp₁ (scratch V5 tmp tmp2 0)
      ys₅ hinp₀ (scratch_parked 0 hV5P)
      (by rw [scratch_apply_ne (by decide) (by decide), hV5,
        Function.update_of_ne (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), hV5]
    rw [show Function.update
        (Function.update (Function.update (W steps) tReg (regT steps))
          tPlusReg (regT steps)) tReg (regT 0)
      = Function.update (Function.update (W steps) tPlusReg (regT steps))
          tReg (regT 0) from by
        rw [Function.update_comm (show tReg ≠ tPlusReg by decide),
          Function.update_idem,
          Function.update_comm (show tPlusReg ≠ tReg by decide)]]
    rw [show (regT 0 : Tape)
        = Function.update (W steps) tPlusReg (regT steps) tReg from by
      rw [Function.update_of_ne (by decide)]; rfl]
    rw [Function.update_eq_self]
  -- g5b: tPlusReg := 0.
  have g5b : (setConstTM tPlusReg 0 : TM nT).HoareTime
      (emitPred inp₁
        (scratch (Function.update (W steps) tPlusReg (regT steps)) tmp tmp2 0)
        ys₅)
      (emitPred inp₁ (scratch (W steps) tmp tmp2 0) ys₅)
      (opBudget M) := by
    refine ((setConstTM_hoareTime tPlusReg 0 steps inp₁
      (scratch (Function.update (W steps) tPlusReg (regT steps)) tmp tmp2 0)
      ys₅ hinp₀ (scratch_parked 0 (parked_update (hWP _) (regT_parked _)))
      (by rw [scratch_apply_ne (by decide) (by decide), Function.update_self])
      ).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) hstepsM))
    rintro inp work out ⟨u1, u2, u3⟩
    refine ⟨u1, ?_, u3⟩
    rw [u2, update_scratch (by decide) (by decide), Function.update_idem,
      show regT 0 = W steps tPlusReg from rfl, Function.update_eq_self]
  -- f6: the active transitions.
  have f6 := emitActiveTM_hoareTime N Qc steps P M hQc hM inp₁ (W steps) ys₅
    hinp₀ (hWP _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set ys₆ : List Bool :=
    ys₅ ++ CNF.encode (activeTransitionClausesF N steps P) with hys₆
  -- f7: the accept clauses.
  have f7 := emitAcceptTM_hoareTime N steps P M hM inp₁ V5 ys₆ hinp₀ hV5P
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
    (by rw [hV5, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; rfl)
  -- Chain everything.
  have hpre1 : ∀ inp work out, emitPred inp₁ (W (steps + 1)) ys inp work out →
      emitPred inp₁ (scratch (W (steps + 1)) tmp tmp2 0) ys inp work out := by
    rintro inp work out ⟨u1, u2, u3⟩
    exact ⟨u1, by rw [u2, hSW], u3⟩
  have c7 : (emitAcceptTM N).HoareTime
      (emitPred inp₁ (scratch V5 tmp tmp2 0) ys₆)
      (fun inp work out => inp = inp₁ ∧
        outAcc (ys₆ ++ CNF.encode (acceptClausesF N steps P)) out)
      (cnfBudget 2 1 M) :=
    f7.strengthen_post (fun inp work out h => ⟨h.1, h.2.2⟩)
  have c6 := seqTM_hoareTime _ _ f6
    (emitPred_transition hinp₀ (scratch_parked 0 hV5P) _) c7
  have c5b := seqTM_hoareTime _ _ g5b
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c6
  have c5a := seqTM_hoareTime _ _ g5a
    (emitPred_transition hinp₀
      (scratch_parked 0 (parked_update (hWP _) (regT_parked _))) _) c5b
  have c5 := seqTM_hoareTime _ _ f5
    (emitPred_transition hinp₀ (scratch_parked 0 hV5P) _) c5a
  have c4b := seqTM_hoareTime _ _ g4b
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c5
  have c4a := seqTM_hoareTime _ _ g4a
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c4b
  have c4 := seqTM_hoareTime _ _ f4
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c4a
  have c3 := seqTM_hoareTime _ _ f3
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c4
  have c2' := seqTM_hoareTime _ _ g3
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c3
  have c2 := seqTM_hoareTime _ _ f2
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c2'
  have c1' := seqTM_hoareTime _ _ g2
    (emitPred_transition hinp₀ (scratch_parked 0 (hWP _)) _) c2
  have c1 := seqTM_hoareTime _ _ f1
    (emitPred_transition hinp₀ (scratch_parked 0 hV3P) _) c1'
  have cb := seqTM_hoareTime _ _ g1b
    (emitPred_transition hinp₀ (hWP _) _) (c1.weaken_pre hpre1)
  have ca := seqTM_hoareTime _ _ g1a
    (emitPred_transition hinp₀ (hWP _) _) cb
  refine ca.consequence (fun _ _ _ h => h) ?_ (by rw [bodyBudget])
  rintro inp work out ⟨u1, u2⟩
  refine ⟨u1, ?_⟩
  rw [show tableauCNFFlat N steps x
      = oneHotStatesF N steps P ++ oneHotCellsF Qc steps P
        ++ oneHotHeadsF Qc steps P ++ startClausesF N steps x
        ++ frameClausesF Qc steps P ++ activeTransitionClausesF N steps P
        ++ acceptClausesF N steps P from by
    rw [tableauCNFFlat, ← hP, ← hQc]]
  rw [hys₆, hys₅, hys₄, hys₃, hys₂, hys₁] at u2
  simp only [CNF.encode_append, List.append_assoc] at u2 ⊢
  exact u2

end SAT
