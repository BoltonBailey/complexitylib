import Complexitylib.Classes.P
import Complexitylib.Classes.NP
import Complexitylib.Classes.Randomized
import Complexitylib.Classes.L
import Complexitylib.Classes.Exponential
import Complexitylib.Models.TuringMachine.Internal
import Complexitylib.Models.TuringMachine.Combinators.ComplementInternal

/-!
# Containment relations between complexity classes

This file collects the standard containment results between complexity classes.

## Theorems

- `DTIME_sub_NTIME` — `DTIME(T) ⊆ NTIME(T)`
- `P_sub_NP` — `P ⊆ NP`
- `DTIME_mono` — `T₁ =O T₂ → DTIME(T₁) ⊆ DTIME(T₂)`
- `NTIME_mono` — `T₁ =O T₂ → NTIME(T₁) ⊆ NTIME(T₂)`
- `DSPACE_mono` — `S₁ =O S₂ → DSPACE(S₁) ⊆ DSPACE(S₂)`
- `P_sub_EXP` — `P ⊆ EXP`
- `DTIME_sub_DSPACE` — `DTIME(T) ⊆ DSPACE(T)` (time bounds space)
- `P_sub_PSPACE` — `P ⊆ PSPACE`
- `RTIME_sub_NTIME` — `RTIME(T) ⊆ NTIME(T)` (one-sided error → nondeterministic)
- `RP_sub_NP` — `RP ⊆ NP`
- `DTIME_sub_BPTIME` — `DTIME(T) ⊆ BPTIME(T)` (deterministic → zero-error probabilistic)
- `P_sub_BPP` — `P ⊆ BPP`
- `NP_sub_NEXP` — `NP ⊆ NEXP`
- `EXP_sub_NEXP` — `EXP ⊆ NEXP`
- `BPTIME_sub_PPTIME` — `BPTIME(T) ⊆ PPTIME(T)` (bounded error → unbounded error)
- `BPP_sub_PP` — `BPP ⊆ PP`
- `P_compl` — `L ∈ P → Lᶜ ∈ P` (P closed under complement)
-/

open Complexity

/-- **DTIME ⊆ NTIME**: every language decidable by a DTM in time `O(T)` is also
    decidable by an NTM in time `O(T)`, via the `TM.toNTM` embedding. -/
theorem DTIME_sub_NTIME (T : ℕ → ℕ) : DTIME T ⊆ NTIME T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm.toNTM, f, tm.toNTM_decidesInTime hdec, hbig⟩

/-- **P ⊆ NP** -/
theorem P_sub_NP : P ⊆ NP :=
  Set.iUnion_mono fun _ => DTIME_sub_NTIME _

/-- DTIME is monotone with respect to `=O`: if `T₁ =O T₂`, then `DTIME T₁ ⊆ DTIME T₂`. -/
theorem DTIME_mono {T₁ T₂ : ℕ → ℕ} (h : T₁ =O T₂) : DTIME T₁ ⊆ DTIME T₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- **P ⊆ EXP**: every polynomial-time language is also exponential-time. -/
theorem P_sub_EXP : P ⊆ EXP :=
  Set.iUnion_mono fun _ => DTIME_mono (BigO.of_le (fun _ => Nat.lt_two_pow_self.le))

/-- **DTIME ⊆ DSPACE**: a DTM running in time `T` uses at most
    `O(T)` space, since the tape heads can move at most one cell per step. -/
theorem DTIME_sub_DSPACE (T : ℕ → ℕ) : DTIME T ⊆ DSPACE T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  refine ⟨k, tm, f, ⟨?_, ?_⟩, hbig⟩
  · -- Space bound: all reachable configs have work tape heads ≤ f(|x|)
    intro x c' hreach i
    obtain ⟨c_halt, t_halt, hle, hreachIn_halt, hhalt, _, _⟩ := hdec x
    obtain ⟨t, hreachIn⟩ := TM.reaches_to_reachesIn tm hreach
    have ht_le := TM.reachesIn_le_halt tm hreachIn hreachIn_halt hhalt
    have hbound := TM.work_head_reachesIn_bound tm hreachIn i
    have := TM.initCfg_work_head_zero tm x i
    omega
  · -- Decision: reachesIn implies reaches, same output
    intro x
    obtain ⟨c', t, hle, hreachIn, hhalt, hyes, hno⟩ := hdec x
    refine ⟨c', ?_, hhalt, hyes, hno⟩
    exact TM.reachesIn.rec Relation.ReflTransGen.refl
      (fun hs _ ih => Relation.ReflTransGen.head hs ih) hreachIn

/-- **P ⊆ PSPACE**: every polynomial-time language uses polynomial space. -/
theorem P_sub_PSPACE : P ⊆ PSPACE :=
  Set.iUnion_mono fun _ => DTIME_sub_DSPACE _

/-- **RTIME ⊆ NTIME**: one-sided error implies nondeterministic.
    The same NTM works: `RejectsWithProb 0` means no accepting paths for `x ∉ L`,
    and `AcceptsWithProb (1/2)` means some accepting path exists for `x ∈ L`. -/
theorem RTIME_sub_NTIME (T : ℕ → ℕ) : RTIME T ⊆ NTIME T := by
  intro L ⟨k, tm, f, hhalt, hacc, hrej, hbig⟩
  refine ⟨k, tm, f, ⟨hhalt, fun x => ?_⟩, hbig⟩
  constructor
  · -- x ∈ L → AcceptsInTime: acceptProb ≥ 1/2 > 0 implies ∃ accepting path
    intro hx
    have hprob := hacc x hx
    -- If acceptCount = 0 then acceptProb = 0, contradicting ≥ 1/2
    by_contra hno
    simp only [NTM.AcceptsInTime] at hno
    push_neg at hno
    have hempty : ∀ ch : Fin (f x.length) → Bool,
        ¬((tm.trace (f x.length) ch (tm.initCfg x)).state = tm.qhalt ∧
          (tm.trace (f x.length) ch (tm.initCfg x)).output.cells 1 = Γ.one) := by
      intro ch ⟨h1, h2⟩; exact hno ch h1 h2
    have hcount : tm.acceptCount x (f x.length) = 0 := by
      simp only [NTM.acceptCount]
      rw [Finset.filter_eq_empty_iff.mpr (fun ch _ => hempty ch)]
      exact Finset.card_empty
    simp [NTM.acceptProb, hcount] at hprob
    norm_num at hprob
  · -- AcceptsInTime → x ∈ L (contrapositive: x ∉ L → ¬AcceptsInTime)
    intro ⟨choices, hhalt_ch, hout_ch⟩
    by_contra hx
    have hprob := hrej x hx
    -- acceptProb ≤ 0 and ≥ 0 so = 0, meaning acceptCount = 0
    have hnn : tm.acceptProb x (f x.length) ≥ 0 := by
      unfold NTM.acceptProb; positivity
    have hzero : tm.acceptProb x (f x.length) = 0 := le_antisymm hprob hnn
    -- acceptCount = 0
    have hcount : tm.acceptCount x (f x.length) = 0 := by
      unfold NTM.acceptProb at hzero
      have h2T : (0:ℚ) < 2 ^ f x.length := by positivity
      rw [div_eq_zero_iff] at hzero
      cases hzero with
      | inl h => exact_mod_cast h
      | inr h => linarith
    -- But choices is an accepting path, so acceptCount > 0 — contradiction
    have hpos : 0 < tm.acceptCount x (f x.length) := by
      unfold NTM.acceptCount
      apply Finset.card_pos.mpr
      exact ⟨choices, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhalt_ch, hout_ch⟩⟩
    omega

/-- **RP ⊆ NP**. -/
theorem RP_sub_NP : RP ⊆ NP :=
  Set.iUnion_mono fun _ => RTIME_sub_NTIME _

/-- **DTIME ⊆ BPTIME**: every deterministic TM can be viewed as a PTM with
    zero error. When the DTM accepts, all paths accept (prob = 1 ≥ 2/3).
    When it rejects, no path accepts (prob = 0 ≤ 1/3). -/
theorem DTIME_sub_BPTIME (T : ℕ → ℕ) : DTIME T ⊆ BPTIME T := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  refine ⟨k, tm.toNTM, f, ?_, ?_, ?_, hbig⟩
  · -- AllPathsHaltIn: from toNTM_decidesInTime
    exact (tm.toNTM_decidesInTime hdec).1
  · -- AcceptsWithProb L f (2/3): acceptProb ≥ 2/3 for x ∈ L
    intro x hx
    have ⟨c', t, hle, hreach, hhalt, hyes, _⟩ := hdec x
    have htrace : ∀ ch, tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x) = c' :=
      fun ch => tm.toNTM_trace_of_reachesIn hreach hhalt hle ch
    -- acceptCount = 2^(f x.length) since all paths accept
    have hcount : tm.toNTM.acceptCount x (f x.length) = 2 ^ f x.length := by
      simp only [NTM.acceptCount]
      have : (Finset.univ.filter fun (choices : Fin (f x.length) → Bool) =>
          let c' := tm.toNTM.trace (f x.length) choices (tm.toNTM.initCfg x)
          c'.state = tm.toNTM.qhalt ∧ c'.output.cells 1 = Γ.one) = Finset.univ := by
        ext ch; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show (tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x)) = c' from htrace ch]
        exact ⟨fun _ => trivial, fun _ => ⟨hhalt, hyes hx⟩⟩
      rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    -- acceptProb = 1
    have hprob : tm.toNTM.acceptProb x (f x.length) = 1 := by
      simp [NTM.acceptProb, hcount]
    linarith
  · -- RejectsWithProb L f (1/3): acceptProb ≤ 1/3 for x ∉ L
    intro x hx
    have ⟨c', t, hle, hreach, hhalt, _, hno⟩ := hdec x
    have htrace : ∀ ch, tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x) = c' :=
      fun ch => tm.toNTM_trace_of_reachesIn hreach hhalt hle ch
    -- acceptCount = 0 since no path accepts
    have hcount : tm.toNTM.acceptCount x (f x.length) = 0 := by
      simp only [NTM.acceptCount]
      rw [Finset.filter_eq_empty_iff.mpr]
      · exact Finset.card_empty
      · intro ch _
        rw [show (tm.toNTM.trace (f x.length) ch (tm.toNTM.initCfg x)) = c' from htrace ch]
        intro ⟨_, h2⟩
        have := hno hx; simp_all
    simp [NTM.acceptProb, hcount]

/-- **P ⊆ BPP**: every polynomial-time language is also in BPP. -/
theorem P_sub_BPP : P ⊆ BPP :=
  Set.iUnion_mono fun _ => DTIME_sub_BPTIME _

/-- NTIME is monotone: if `T₁ =O T₂`, then `NTIME T₁ ⊆ NTIME T₂`. -/
theorem NTIME_mono {T₁ T₂ : ℕ → ℕ} (h : T₁ =O T₂) : NTIME T₁ ⊆ NTIME T₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- DSPACE is monotone: if `S₁ =O S₂`, then `DSPACE S₁ ⊆ DSPACE S₂`. -/
theorem DSPACE_mono {S₁ S₂ : ℕ → ℕ} (h : S₁ =O S₂) : DSPACE S₁ ⊆ DSPACE S₂ := by
  intro L ⟨k, tm, f, hdec, hbig⟩
  exact ⟨k, tm, f, hdec, hbig.trans h⟩

/-- **NP ⊆ NEXP**: every nondeterministic polynomial-time language is also
    nondeterministic exponential-time. -/
theorem NP_sub_NEXP : NP ⊆ NEXP :=
  Set.iUnion_mono fun _ => NTIME_mono (BigO.of_le (fun _ => Nat.lt_two_pow_self.le))

/-- **EXP ⊆ NEXP**: every deterministic exponential-time language is also
    nondeterministic exponential-time. -/
theorem EXP_sub_NEXP : EXP ⊆ NEXP :=
  Set.iUnion_mono fun _ => DTIME_sub_NTIME _

/-- **BPTIME ⊆ PPTIME**: two-sided bounded error implies unbounded error,
    since 2/3 > 1/2 and 1/3 < 1/2. -/
theorem BPTIME_sub_PPTIME (T : ℕ → ℕ) : BPTIME T ⊆ PPTIME T := by
  intro L ⟨k, tm, f, hhalt, hacc, hrej, hbig⟩
  refine ⟨k, tm, f, hhalt, fun x => ⟨fun hx => ?_, fun hprob => ?_⟩, hbig⟩
  · -- x ∈ L → acceptProb > 1/2: acceptProb ≥ 2/3 > 1/2
    have := hacc x hx; linarith
  · -- acceptProb > 1/2 → x ∈ L: contrapositive
    by_contra hx
    have := hrej x hx; linarith

/-- **BPP ⊆ PP**. -/
theorem BPP_sub_PP : BPP ⊆ PP :=
  Set.iUnion_mono fun _ => BPTIME_sub_PPTIME _

/-- **P is closed under complement**: if `L ∈ P` then `Lᶜ ∈ P`. -/
theorem P_compl {L : Language} (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨k, n_tapes, tm, f, hdec, hbig⟩ := Set.mem_iUnion.mp h
  refine Set.mem_iUnion.mpr ⟨k + 1, n_tapes, tm.complementTM, fun n => 2 * f n + 4,
    tm.complementTM_decidesInTime hdec, ?_⟩
  -- (fun n => 2 * f n + 4) =O (· ^ (k + 1))
  open Asymptotics Filter in
  have hpow : (· ^ k) =O (· ^ (k + 1)) := by
    apply IsBigO.of_bound 1
    filter_upwards [Ioi_mem_atTop 0] with n hn
    simp only [one_mul, Real.norm_natCast]
    exact_mod_cast Nat.pow_le_pow_right hn (Nat.le_succ k)
  open Asymptotics Filter in
  exact BigO.add (BigO.const_mul_left 2 (hbig.trans hpow)) (by
    apply IsBigO.of_bound 4
    filter_upwards [Ioi_mem_atTop 0] with n hn
    simp only [Real.norm_natCast]
    exact_mod_cast le_mul_of_one_le_right (by omega) (Nat.one_le_pow _ _ hn))

