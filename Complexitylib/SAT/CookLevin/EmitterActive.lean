import Complexitylib.SAT.CookLevin.EmitterStart

/-!
# The active-transition family emitter

`activeTransitionClausesF` quantifies over rows, machine states, three head
positions, three read symbols, and the choice bit; per tuple it emits seven
implication clauses (the eight-literal reading condition plus one
consequence each). States, symbols, and the choice bit are finite data
unrolled at definition level (`bigSeqTM` over their lists); rows and
positions are runtime loops.
-/

namespace SAT

open _root_.TM Tableau

open Emit

-- ════════════════════════════════════════════════════════════════════════
-- Generic: a bigSeq of uniform emitters emits the flatMap
-- ════════════════════════════════════════════════════════════════════════

/-- **Unrolled emission**: if every element's machine appends its word from
    any accumulator, the `bigSeqTM` of the mapped list appends the
    `flatMap`. -/
theorem bigSeq_emit_hoareTime {α : Type _} (F : α → TM nT)
    (E : α → List Bool) (b : ℕ) (inp₀ : Tape) (W : Fin nT → Tape)
    (hinp₀ : Parked inp₀) (hWP : ∀ i, Parked (W i)) :
    ∀ (l : List α),
    (∀ a ∈ l, ∀ ys, (F a).HoareTime
      (emitPred inp₀ W ys) (emitPred inp₀ W (ys ++ E a)) b) →
    ∀ ys, (bigSeqTM (l.map F)).HoareTime
      (emitPred inp₀ W ys) (emitPred inp₀ W (ys ++ l.flatMap E))
      (l.length * (b + 1) + 1) := by
  intro l
  induction l with
  | nil =>
    intro _ ys
    have hskip := skipTM_hoareTime inp₀ W ys hinp₀ hWP
    refine hskip.consequence (fun _ _ _ h => h) ?_ (by simp)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, g2, by simpa using g3⟩
  | cons a l ih =>
    intro hspec ys
    have hhead := hspec a List.mem_cons_self ys
    have hrest := ih (fun a' ha' ys' => hspec a' (List.mem_cons_of_mem _ ha')
      ys') (ys ++ E a)
    have hseq := seqTM_hoareTime (F a) (bigSeqTM (l.map F)) hhead
      (emitPred_transition hinp₀ hWP _) hrest
    refine hseq.consequence (fun _ _ _ h => h) ?_ ?_
    · rintro inp work out ⟨g1, g2, g3⟩
      refine ⟨g1, g2, ?_⟩
      rw [List.flatMap_cons, ← List.append_assoc]
      exact g3
    · simp only [List.length_cons]
      have : (l.length + 1) * (b + 1) = l.length * (b + 1) + (b + 1) :=
        Nat.succ_mul ..
      omega

-- ════════════════════════════════════════════════════════════════════════
-- Consequence head positions
-- ════════════════════════════════════════════════════════════════════════

/-- Load `posMove`-of-a-position into the scratch position register: copy,
    then adjust by the (definition-level) move. `none` means the halting
    state's frozen head. -/
def setupPosTM (p : Fin nT) : Option Dir3 → TM nT
  | none => copyIntoTM p auxReg2
  | some .stay => copyIntoTM p auxReg2
  | some .left => seqTM (copyIntoTM p auxReg2) (decRegTM auxReg2)
  | some .right => seqTM (copyIntoTM p auxReg2) (incRegTM auxReg2)

/-- The value `setupPosTM` leaves in `auxReg2`. -/
def posMoveOpt (v : ℕ) : Option Dir3 → ℕ
  | none => v
  | some d => posMove v d

theorem posMoveOpt_le (v P : ℕ) (mv : Option Dir3) (hv : v ≤ P) :
    posMoveOpt v mv ≤ P + 1 := by
  cases mv with
  | none => show v ≤ P + 1; omega
  | some d =>
    cases d with
    | left => show v - 1 ≤ P + 1; omega
    | stay => show v ≤ P + 1; omega
    | right => show v + 1 ≤ P + 1; omega

/-- **`setupPosTM` Hoare specification**: `auxReg2 := posMoveOpt` of the
    position register's value. -/
theorem setupPosTM_hoareTime (p : Fin nT) (hp : p ≠ auxReg2)
    (mv : Option Dir3) (M v a : ℕ)
    (hv : v + 1 ≤ M) (ha : a ≤ M)
    (inp₀ : Tape) (work₀ : Fin nT → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i))
    (hpv : work₀ p = regT v) (haux : work₀ auxReg2 = regT a) :
    (setupPosTM p mv).HoareTime
      (emitPred inp₀ work₀ ys)
      (emitPred inp₀
        (Function.update work₀ auxReg2 (regT (posMoveOpt v mv))) ys)
      (2 * opBudget M + 1) := by
  have hcopy : (copyIntoTM p auxReg2).HoareTime
      (emitPred inp₀ work₀ ys)
      (emitPred inp₀ (Function.update work₀ auxReg2 (regT v)) ys)
      (opBudget M) :=
    (copyIntoTM_hoareTime p auxReg2 hp v a inp₀ work₀ ys hinp₀
      (fun i _ => hwork₀ i) hpv haux).mono_bound
      (copyIntoBudget (by omega) ha)
  have hmidP : ∀ i, Parked (Function.update work₀ auxReg2 (regT v) i) :=
    parked_update hwork₀ (regT_parked _)
  cases mv with
  | none => exact hcopy.mono_bound (by omega)
  | some d =>
    cases d with
    | stay => exact hcopy.mono_bound (by omega)
    | left =>
      have hdec : (decRegTM auxReg2).HoareTime
          (emitPred inp₀ (Function.update work₀ auxReg2 (regT v)) ys)
          (emitPred inp₀
            (Function.update work₀ auxReg2 (regT (v - 1))) ys)
          (opBudget M) := by
        refine ((decRegTM_hoareTime auxReg2 v inp₀
          (Function.update work₀ auxReg2 (regT v)) ys hinp₀
          (fun i _ => hmidP i)
          (by rw [Function.update_self])).consequence
          (fun _ _ _ h => h) ?_ (incBudget (by omega)))
        rintro inp work out ⟨g1, g2, g3⟩
        exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
      exact (seqTM_hoareTime (copyIntoTM p auxReg2) (decRegTM auxReg2) hcopy
        (emitPred_transition hinp₀ hmidP _) hdec).mono_bound (by omega)
    | right =>
      have hinc : (incRegTM auxReg2).HoareTime
          (emitPred inp₀ (Function.update work₀ auxReg2 (regT v)) ys)
          (emitPred inp₀
            (Function.update work₀ auxReg2 (regT (v + 1))) ys)
          (opBudget M) := by
        refine ((incRegTM_hoareTime auxReg2 v inp₀
          (Function.update work₀ auxReg2 (regT v)) ys hinp₀
          (fun i _ => hmidP i)
          (by rw [Function.update_self])).consequence
          (fun _ _ _ h => h) ?_ (incBudget (by omega)))
        rintro inp work out ⟨g1, g2, g3⟩
        exact ⟨g1, by rw [g2, Function.update_idem], g3⟩
      exact (seqTM_hoareTime (copyIntoTM p auxReg2) (incRegTM auxReg2) hcopy
        (emitPred_transition hinp₀ hmidP _) hinc).mono_bound (by omega)


-- ════════════════════════════════════════════════════════════════════════
-- The reading condition
-- ════════════════════════════════════════════════════════════════════════

/-- Descriptors of the eight-literal reading condition. -/
noncomputable def activeCondD (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) : List (LitDesc nT) :=
  [⟨false, 0, .inl tReg, .inr (stateIdx N q), .inr 0, .inr 0⟩,
   ⟨false, 3, .inl tReg, .inr 0, .inl pos1Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩,
   ⟨false, 3, .inl tReg, .inr 1, .inl pos2Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 1, .inl pos2Reg, .inr (symIdx sw)⟩,
   ⟨false, 3, .inl tReg, .inr 2, .inl pos3Reg, .inr 0⟩,
   ⟨false, 2, .inl tReg, .inr 2, .inl pos3Reg, .inr (symIdx so)⟩,
   ⟨!b, 1, .inl tReg, .inr 0, .inr 0, .inr 0⟩]

section ActiveContext

variable (N : NTM 1)

/-- The standing register facts of the active family's leaves. -/
structure ActiveBase (Qc steps P M t pi pw po : ℕ)
    (base : Fin nT → Tape) : Prop where
  hM : 4 * (steps + 1) * (max Qc 3) * (P + 2) * 4 ≤ M
  ht : t < steps
  hpi : pi ≤ P
  hpw : pw ≤ P
  hpo : po ≤ P
  parked : ∀ l, Parked (base l)
  hrA : base rA = regT (steps + 1)
  hrB : base rB = regT (max Qc 3)
  hrC : base rC = regT (P + 2)
  hrD : base rD = regT 4
  htReg : base tReg = regT t
  htPlus : base tPlusReg = regT (t + 1)
  hp1 : base pos1Reg = regT pi
  hp2 : base pos2Reg = regT pw
  hp3 : base pos3Reg = regT po

/-- The base facts survive scratch-position updates. -/
theorem ActiveBase.update_aux {Qc steps P M t pi pw po : ℕ}
    {base : Fin nT → Tape}
    (hB : ActiveBase Qc steps P M t pi pw po base) (z : ℕ) :
    ActiveBase Qc steps P M t pi pw po
      (Function.update base auxReg2 (regT z)) :=
  ⟨hB.hM, hB.ht, hB.hpi, hB.hpw, hB.hpo,
   parked_update hB.parked (regT_parked _),
   by rw [Function.update_of_ne (by decide)]; exact hB.hrA,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrB,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrC,
   by rw [Function.update_of_ne (by decide)]; exact hB.hrD,
   by rw [Function.update_of_ne (by decide)]; exact hB.htReg,
   by rw [Function.update_of_ne (by decide)]; exact hB.htPlus,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp1,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp2,
   by rw [Function.update_of_ne (by decide)]; exact hB.hp3⟩

/-- The reading condition denotes `activeCondF`. -/
theorem activeCondD_spec (q : N.Q) (si sw so : Γ) (b : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base) :
    List.Forall₂
      (LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
      (activeCondD N q si sw so b)
      (activeCondF N steps P t q pi si pw sw po so b) := by
  subst hQc
  obtain ⟨hM, ht, hpi, hpw, hpo, hparked, hrA', hrB', hrC', hrD', htR,
    htPlus', hp1', hp2', hp3'⟩ := hB
  rw [activeCondD, activeCondF]
  have hcapS : stateIdx N q < max (Fintype.card N.Q) 3 :=
    lt_of_lt_of_le (stateIdx_lt N q) (le_max_left _ 3)
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
    (.cons ?_ (.cons ?_ .nil)))))))
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega)
      (show t < steps + 1 by omega) hcapS
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
    exact ⟨t, stateIdx N q, 0, 0, ⟨htR, by decide, by decide⟩, rfl, rfl,
      rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpi (by decide)
      (by decide) false htR hp1'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 0 < max (Fintype.card N.Q) 3
        by omega)
      (show pi < P + 2 by omega) (symIdx_lt si) hM
    exact ⟨t, 0, pi, symIdx si, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp1', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpw (by decide)
      (by decide) false htR hp2'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 1 < max (Fintype.card N.Q) 3
        by omega)
      (show pw < P + 2 by omega) (symIdx_lt sw) hM
    exact ⟨t, 1, pw, symIdx sw, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp2', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · exact headLitD_spec (by omega) hM (by omega) hpo (by decide)
      (by decide) false htR hp3'
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega)
      (show t < steps + 1 by omega) (show 2 < max (Fintype.card N.Q) 3
        by omega)
      (show po < P + 2 by omega) (symIdx_lt so) hM
    exact ⟨t, 2, po, symIdx so, ⟨htR, by decide, by decide⟩, rfl,
      ⟨hp3', by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  · obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 1) (by omega)
      (show t < steps + 1 by omega) (show 0 < max (Fintype.card N.Q) 3
        by omega)
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hM
    exact ⟨t, 0, 0, 0, ⟨htR, by decide, by decide⟩, rfl, rfl, rfl, rfl,
      rfl, k0, k1, k2, k3, k4⟩


-- ════════════════════════════════════════════════════════════════════════
-- The per-tuple leaf: seven implication clauses
-- ════════════════════════════════════════════════════════════════════════

/-- One conseq clause emission: the condition plus one consequence literal. -/
noncomputable def activeClauseTM (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) (d9 : LitDesc nT) : TM nT :=
  emitClauseTM rA rB rC rD tmp tmp2 (activeCondD N q si sw so b ++ [d9])

/-- **The per-tuple leaf**: the seven implication clauses, with the write
    symbols and head moves resolved at definition level. -/
noncomputable def activeLeafTM (N : NTM 1) (q : N.Q) (si sw so : Γ)
    (b : Bool) (wSymVal oSymVal : Γ) (mvI mvW mvO : Option Dir3) : TM nT :=
  seqTM (activeClauseTM N q si sw so b
      ⟨true, 0, .inl tPlusReg,
        .inr (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1)), .inr 0, .inr 0⟩)
    (seqTM (activeClauseTM N q si sw so b
        ⟨true, 2, .inl tPlusReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩)
      (seqTM (activeClauseTM N q si sw so b
          ⟨true, 2, .inl tPlusReg, .inr 1, .inl pos2Reg,
            .inr (symIdx wSymVal)⟩)
        (seqTM (activeClauseTM N q si sw so b
            ⟨true, 2, .inl tPlusReg, .inr 2, .inl pos3Reg,
              .inr (symIdx oSymVal)⟩)
          (seqTM (setupPosTM pos1Reg mvI)
            (seqTM (activeClauseTM N q si sw so b
                ⟨true, 3, .inl tPlusReg, .inr 0, .inl auxReg2, .inr 0⟩)
              (seqTM (setupPosTM pos2Reg mvW)
                (seqTM (activeClauseTM N q si sw so b
                    ⟨true, 3, .inl tPlusReg, .inr 1, .inl auxReg2, .inr 0⟩)
                  (seqTM (setupPosTM pos3Reg mvO)
                    (seqTM (activeClauseTM N q si sw so b
                        ⟨true, 3, .inl tPlusReg, .inr 2, .inl auxReg2,
                          .inr 0⟩)
                      (setConstTM auxReg2 0))))))))))

/-- Budget of the leaf. -/
def activeLeafBudget (M : ℕ) : ℕ :=
  7 * clauseBudget 9 M + 7 * opBudget M + 13

/-- One conseq-clause emission from an `ActiveBase` state. -/
theorem activeClauseTM_hoareTime (q : N.Q) (si sw so : Γ) (b : Bool)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    {d9 : LitDesc nT} {ℓ9 : Lit}
    (h9 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4 d9 ℓ9)
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeClauseTM N q si sw so b d9).HoareTime
      (emitPred inp₀ (scratch base tmp tmp2 0) ys)
      (emitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ (Clause.encode
          (activeCondF N steps P t q pi si pw sw po so b ++ [ℓ9])
          ++ [true, false])))
      (clauseBudget 9 M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hB.hM
  have hf : List.Forall₂
      (LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4)
      (activeCondD N q si sw so b ++ [d9])
      (activeCondF N steps P t q pi si pw sw po so b ++ [ℓ9]) :=
    forall₂_append (activeCondD_spec N q si sw so b hQc hB)
      (.cons h9 .nil)
  exact emitClauseTM_hoareTime rA rB rC rD tmp tmp2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    hAM hBM hCM hDM hf
    (L := 9) (by simp [activeCondD])
    inp₀ ys hinp₀ hB.parked hB.hrA hB.hrB hB.hrC hB.hrD

/-- **`activeLeafTM` Hoare specification**: appends the encoded
    `activeClausesAtF` for the tuple. -/
theorem activeLeafTM_hoareTime (q : N.Q) (si sw so : Γ) (b : Bool)
    (wSymVal oSymVal : Γ) (mvI mvW mvO : Option Dir3)
    {Qc steps P M t pi pw po : ℕ} {base : Fin nT → Tape}
    (hQc : Qc = Fintype.card N.Q)
    (hB : ActiveBase Qc steps P M t pi pw po base)
    (haux2 : base auxReg2 = regT 0)
    (hwSym : wSymVal = (if q = N.qhalt then sw else if pw = 0 then sw
      else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))
    (hoSym : oSymVal = (if q = N.qhalt then so else if po = 0 then so
      else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))
    (hmvI : posMoveOpt pi mvI = (if q = N.qhalt then pi
      else posMove pi (N.δ b q si (fun _ => sw) so).2.2.2.1))
    (hmvW : posMoveOpt pw mvW = (if q = N.qhalt then pw
      else posMove pw ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0)))
    (hmvO : posMoveOpt po mvO = (if q = N.qhalt then po
      else posMove po (N.δ b q si (fun _ => sw) so).2.2.2.2.2))
    (inp₀ : Tape) (ys : List Bool) (hinp₀ : Parked inp₀) :
    (activeLeafTM N q si sw so b wSymVal oSymVal mvI mvW mvO).HoareTime
      (emitPred inp₀ (scratch base tmp tmp2 0) ys)
      (emitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ CNF.encode
          (activeClausesAtF N steps P t q pi si pw sw po so b)))
      (activeLeafBudget M) := by
  have hA1 : (1:ℕ) ≤ steps + 1 := by omega
  obtain ⟨hAM, hBM, hCM, hDM⟩ := radix_caps hA1 (by omega) (by omega)
    (by omega) hB.hM
  have htM : t + 1 < steps + 1 := by
    have := hB.ht
    omega
  -- The seven consequence literals.
  have hlit1 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 0, .inl tPlusReg,
        .inr (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1)), .inr 0, .inr 0⟩
      ⟨true, vStateF Qc steps P (t + 1)
        (stateIdx N (if q = N.qhalt then q
          else (N.δ b q si (fun _ => sw) so).1))⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 0) (by omega) htM
      (lt_of_lt_of_le (stateIdx_lt N _) (le_max_left _ 3))
      (show 0 < P + 2 by omega) (show (0:ℕ) < 4 by omega) hB.hM
    exact ⟨t + 1, stateIdx N _, 0, 0, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, rfl, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit2 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 0, .inl pos1Reg, .inr (symIdx si)⟩
      ⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 0 < max (Fintype.card N.Q) 3 by omega)
      (show pi < P + 2 from by have := hB.hpi; omega) (symIdx_lt si) hB.hM
    exact ⟨t + 1, 0, pi, symIdx si, ⟨hB.htPlus, by decide, by decide⟩, rfl,
      ⟨hB.hp1, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit3 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 1, .inl pos2Reg, .inr (symIdx wSymVal)⟩
      ⟨true, vCellF Qc steps P (t + 1) 1 pw (symIdx wSymVal)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 1 < max (Fintype.card N.Q) 3 by omega)
      (show pw < P + 2 from by have := hB.hpw; omega) (symIdx_lt wSymVal)
      hB.hM
    exact ⟨t + 1, 1, pw, symIdx wSymVal, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, ⟨hB.hp2, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  have hlit4 : LitDesc.Spec base tmp tmp2 M (steps + 1) (max Qc 3) (P + 2) 4
      ⟨true, 2, .inl tPlusReg, .inr 2, .inl pos3Reg, .inr (symIdx oSymVal)⟩
      ⟨true, vCellF Qc steps P (t + 1) 2 po (symIdx oSymVal)⟩ := by
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 2) (by omega) htM
      (show 2 < max (Fintype.card N.Q) 3 by omega)
      (show po < P + 2 from by have := hB.hpo; omega) (symIdx_lt oSymVal)
      hB.hM
    exact ⟨t + 1, 2, po, symIdx oSymVal, ⟨hB.htPlus, by decide, by decide⟩,
      rfl, ⟨hB.hp3, by decide, by decide⟩, rfl, rfl, rfl, k0, k1, k2, k3, k4⟩
  -- Head consequence literals (at the aux-updated bases).
  have hhead : ∀ (tp z : ℕ), tp < 3 → z ≤ P + 1 →
      LitDesc.Spec (Function.update base auxReg2 (regT z)) tmp tmp2 M
        (steps + 1) (max Qc 3) (P + 2) 4
        ⟨true, 3, .inl tPlusReg, .inr tp, .inl auxReg2, .inr 0⟩
        ⟨true, vHeadF Qc steps P (t + 1) tp z⟩ := by
    intro tp z htp hz
    subst hQc
    obtain ⟨k0, k1, k2, k3, k4⟩ := flatCaps (tag := 3) (by omega) htM
      (show tp < max (Fintype.card N.Q) 3 by omega)
      (show z < P + 2 by omega) (show (0:ℕ) < 4 by omega) hB.hM
    refine ⟨t + 1, tp, z, 0,
      ⟨by rw [Function.update_of_ne (by decide)]; exact hB.htPlus,
        by decide, by decide⟩,
      rfl, ⟨by rw [Function.update_self], by decide, by decide⟩, rfl, rfl,
      rfl, k0, k1, k2, k3, k4⟩
  subst hwSym hoSym
  -- Abbreviations for the emitted clause words.
  set cond : Clause := activeCondF N steps P t q pi si pw sw po so b
    with hcond
  set iH : ℕ := posMoveOpt pi mvI with hiH
  set wH : ℕ := posMoveOpt pw mvW with hwH
  set oH : ℕ := posMoveOpt po mvO with hoH
  have hiHle : iH ≤ P + 1 := posMoveOpt_le pi P mvI hB.hpi
  have hwHle : wH ≤ P + 1 := posMoveOpt_le pw P mvW hB.hpw
  have hoHle : oH ≤ P + 1 := posMoveOpt_le po P mvO hB.hpo
  have hPM : P + 2 ≤ M := by
    have hA1 : (1:ℕ) ≤ steps + 1 := by omega
    obtain ⟨_, _, hCM, _⟩ := radix_caps hA1 (by omega) (by omega)
      (by omega) hB.hM
    omega
  set base₅ : Fin nT → Tape := Function.update base auxReg2 (regT iH)
    with hbase₅
  set base₇ : Fin nT → Tape := Function.update base auxReg2 (regT wH)
    with hbase₇
  set base₉ : Fin nT → Tape := Function.update base auxReg2 (regT oH)
    with hbase₉
  -- The emitted words.
  set w1 : List Bool := Clause.encode (cond ++
    [⟨true, vStateF Qc steps P (t + 1) (stateIdx N (if q = N.qhalt then q
      else (N.δ b q si (fun _ => sw) so).1))⟩]) ++ [true, false] with hw1
  set w2 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩]) ++ [true, false]
    with hw2
  set w3 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 1 pw
      (symIdx (if q = N.qhalt then sw else if pw = 0 then sw
        else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))⟩]) ++ [true, false]
    with hw3
  set w4 : List Bool := Clause.encode (cond ++
    [⟨true, vCellF Qc steps P (t + 1) 2 po
      (symIdx (if q = N.qhalt then so else if po = 0 then so
        else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))⟩]) ++ [true, false]
    with hw4
  set w5 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 0 iH⟩]) ++ [true, false] with hw5
  set w6 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 1 wH⟩]) ++ [true, false] with hw6
  set w7 : List Bool := Clause.encode (cond ++
    [⟨true, vHeadF Qc steps P (t + 1) 2 oH⟩]) ++ [true, false] with hw7
  -- The four leading clauses.
  have h₁ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit1 inp₀ ys
    hinp₀
  have h₂ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit2 inp₀
    (ys ++ w1) hinp₀
  have h₃ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit3 inp₀
    (ys ++ w1 ++ w2) hinp₀
  have h₄ := activeClauseTM_hoareTime N q si sw so b hQc hB hlit4 inp₀
    (ys ++ w1 ++ w2 ++ w3) hinp₀
  -- Stage 5: aux := iH.
  have h₅ : (setupPosTM pos1Reg mvI).HoareTime
      (emitPred inp₀ (scratch base tmp tmp2 0) (ys ++ w1 ++ w2 ++ w3 ++ w4))
      (emitPred inp₀ (scratch base₅ tmp tmp2 0) (ys ++ w1 ++ w2 ++ w3 ++ w4))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos1Reg (by decide) mvI M pi 0
      (by have := hB.hpi; omega) (by omega) inp₀ (scratch base tmp tmp2 0) _
      hinp₀ (scratch_parked 0 hB.parked)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact hB.hp1)
      (by rw [scratch_apply_ne (by decide) (by decide)]; exact haux2)
      ).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    exact ⟨g1, by rw [g2, update_scratch (by decide) (by decide)], g3⟩
  -- Stage 6: the input-head clause.
  have h₆ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux iH)
    (hhead 0 iH (by omega) hiHle) inp₀ (ys ++ w1 ++ w2 ++ w3 ++ w4) hinp₀
  -- Stage 7: aux := wH.
  have h₇ : (setupPosTM pos2Reg mvW).HoareTime
      (emitPred inp₀ (scratch base₅ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5))
      (emitPred inp₀ (scratch base₇ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos2Reg (by decide) mvW M pw iH
      (by have := hB.hpw; omega) (by omega) inp₀ (scratch base₅ tmp tmp2 0) _
      hinp₀ (scratch_parked 0 (hB.update_aux iH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₅,
        Function.update_of_ne (by decide)]; exact hB.hp2)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₅,
        Function.update_self])).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide), hbase₅,
      Function.update_idem]
  -- Stage 8: the work-head clause.
  have h₈ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux wH)
    (hhead 1 wH (by omega) hwHle) inp₀ (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5)
    hinp₀
  -- Stage 9: aux := oH.
  have h₉ : (setupPosTM pos3Reg mvO).HoareTime
      (emitPred inp₀ (scratch base₇ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6))
      (emitPred inp₀ (scratch base₉ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6))
      (2 * opBudget M + 1) := by
    refine ((setupPosTM_hoareTime pos3Reg (by decide) mvO M po wH
      (by have := hB.hpo; omega) (by omega) inp₀ (scratch base₇ tmp tmp2 0) _
      hinp₀ (scratch_parked 0 (hB.update_aux wH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₇,
        Function.update_of_ne (by decide)]; exact hB.hp3)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₇,
        Function.update_self])).strengthen_post ?_)
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide), hbase₇,
      Function.update_idem]
  -- Stage 10: the output-head clause.
  have h₁₀ := activeClauseTM_hoareTime N q si sw so b hQc (hB.update_aux oH)
    (hhead 2 oH (by omega) hoHle) inp₀
    (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6) hinp₀
  -- Stage 11: aux := 0.
  have h₁₁ : (setConstTM auxReg2 0).HoareTime
      (emitPred inp₀ (scratch base₉ tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7))
      (emitPred inp₀ (scratch base tmp tmp2 0)
        (ys ++ w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7))
      (opBudget M) := by
    refine ((setConstTM_hoareTime auxReg2 0 oH inp₀
      (scratch base₉ tmp tmp2 0) _ hinp₀
      (scratch_parked 0 (hB.update_aux oH).parked)
      (by rw [scratch_apply_ne (by decide) (by decide), hbase₉,
        Function.update_self])).consequence (fun _ _ _ h => h) ?_
      (setConstBudget (show (0:ℕ) ≤ M by omega) (by omega)))
    rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, ?_, g3⟩
    rw [g2, update_scratch (by decide) (by decide), hbase₉,
      Function.update_idem,
      show regT 0 = base auxReg2 from haux2.symm, Function.update_eq_self]
  -- Glue the eleven stages.
  have c₁₀₁₁ := seqTM_hoareTime _ _ h₁₀
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux oH).parked) _)
    h₁₁
  have c₉ := seqTM_hoareTime _ _ h₉
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux oH).parked) _)
    c₁₀₁₁
  have c₈ := seqTM_hoareTime _ _ h₈
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux wH).parked) _)
    c₉
  have c₇ := seqTM_hoareTime _ _ h₇
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux wH).parked) _)
    c₈
  have c₆ := seqTM_hoareTime _ _ h₆
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux iH).parked) _)
    c₇
  have c₅ := seqTM_hoareTime _ _ h₅
    (emitPred_transition hinp₀ (scratch_parked 0 (hB.update_aux iH).parked) _)
    c₆
  have c₄ := seqTM_hoareTime _ _ h₄
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₅
  have c₃ := seqTM_hoareTime _ _ h₃
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₄
  have c₂ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₃
  have call := seqTM_hoareTime _ _ h₁
    (emitPred_transition hinp₀ (scratch_parked 0 hB.parked) _) c₂
  refine call.consequence (fun _ _ _ h => h) ?_ ?_
  · rintro inp work out ⟨g1, g2, g3⟩
    refine ⟨g1, g2, ?_⟩
    rw [show activeClausesAtF N steps P t q pi si pw sw po so b
        = [cond ++ [⟨true, vStateF Qc steps P (t + 1)
            (stateIdx N (if q = N.qhalt then q
              else (N.δ b q si (fun _ => sw) so).1))⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 0 pi (symIdx si)⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 1 pw
            (symIdx (if q = N.qhalt then sw else if pw = 0 then sw
              else ((N.δ b q si (fun _ => sw) so).2.1 0).toΓ))⟩],
           cond ++ [⟨true, vCellF Qc steps P (t + 1) 2 po
            (symIdx (if q = N.qhalt then so else if po = 0 then so
              else (N.δ b q si (fun _ => sw) so).2.2.1.toΓ))⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 0
            (if q = N.qhalt then pi
              else posMove pi (N.δ b q si (fun _ => sw) so).2.2.2.1)⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 1
            (if q = N.qhalt then pw
              else posMove pw ((N.δ b q si (fun _ => sw) so).2.2.2.2.1 0))⟩],
           cond ++ [⟨true, vHeadF Qc steps P (t + 1) 2
            (if q = N.qhalt then po
              else posMove po (N.δ b q si (fun _ => sw) so).2.2.2.2.2)⟩]]
      from by
        subst hQc
        rw [hcond]
        rfl]
    rw [← hmvI, ← hmvW, ← hmvO]
    rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7] at g3
    simp only [CNF.encode_cons, CNF.encode_nil, List.append_nil,
      List.append_assoc] at g3 ⊢
    exact g3
  · rw [activeLeafBudget]
    omega

end ActiveContext

end SAT
