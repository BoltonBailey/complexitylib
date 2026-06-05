import Complexitylib.SAT.Headline
import Complexitylib.Classes.NP.Reduction
import Complexitylib.Models.TuringMachine.SingleTape

/-!
# Cook–Levin: SAT is NP-complete

This file assembles the **Cook–Levin theorem**, `SAT.NPComplete_L_SAT`:
`L_SAT` is NP-complete. Membership `L_SAT ∈ NP` is `SAT.L_SAT_mem_NP`
(`SAT/Headline.lean`); NP-hardness is the content here.

## Architecture (full skeleton; leaves = `sorry`)

```
NPComplete_L_SAT                       (= ⟨L_SAT_mem_NP, NPHard_L_SAT⟩)
└ NPHard_L_SAT                         (unpack any L ∈ NP → its NTM)
  └ cookLevin_reduction               (multi-tape → single-tape, then ↓)
    ├ NTM.exists_singleTape_decider   (SingleTape.lean)
    └ cookLevin_reduction_singleTape
        ├ reductionFn                 (def: x ↦ (tableauCNF …).encode)
        ├ reductionFn_mem_FP          ⬜ leaf (C): poly-time emitter TM
        └ tableauCNF_correct          (= encode_mem_LSAT_iff ∘ B ∘ hdec)
            ├ tableauCNF              ⬜ leaf (def): the tableau formula
            ├ tableauCNF_satisfiable_iff  ⬜ leaf (B): sat ↔ accepting computation
            └ encode_mem_LSAT_iff     ✓ (CNF.encode injective)
```

The remaining proof obligations are: the single-tape simulation
(`SingleTape.lean`), the `tableauCNF` definition, its satisfiability
characterization, and its `FP`-computable encoding.
-/

open Complexity

namespace SAT

/-! ## Tableau variable encoding

The computation-tableau formula's Boolean variables are indexed by `ℕ`. Each
"atom" of the tableau — a state bit, a nondeterministic choice bit, a tape-cell
bit, or a head-position bit, all indexed by a time-step — is injected into `ℕ`
by iterated `Nat.pair`, so distinct atoms receive distinct SAT variables. -/

namespace Tableau

/-- Inject a tagged 4-tuple of naturals into one natural by iterated `Nat.pair`. -/
def enc (tag a b c d : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair a (Nat.pair b (Nat.pair c d)))

/-- `enc` is injective on each component (it is a composition of bijective pairings). -/
theorem enc_inj {tag a b c d tag' a' b' c' d' : ℕ}
    (h : enc tag a b c d = enc tag' a' b' c' d') :
    tag = tag' ∧ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  simp only [enc, Nat.pair_eq_pair] at h
  tauto

/-- Variable: at time `t` the machine is in the state with index `q` (one-hot). -/
def vState (t q : ℕ) : ℕ := enc 0 t q 0 0
/-- Variable: at time `t` the nondeterministic choice bit is `true`. -/
def vChoice (t : ℕ) : ℕ := enc 1 t 0 0 0
/-- Variable: at time `t`, cell `pos` of tape `tp` holds the symbol with index `s`. -/
def vCell (t tp pos s : ℕ) : ℕ := enc 2 t tp (Nat.pair pos s) 0
/-- Variable: at time `t`, the head of tape `tp` is at cell `pos`. -/
def vHead (t tp pos : ℕ) : ℕ := enc 3 t tp pos 0

/-- The symbol index of a tape symbol: `0,1,2,3` for `0,1,□,▷`. Injective, so a
    one-hot encoding over `{0,1,2,3}` faithfully names the four tape symbols. -/
def symIdx : Γ → ℕ
  | Γ.zero => 0
  | Γ.one => 1
  | Γ.blank => 2
  | Γ.start => 3

theorem symIdx_inj : Function.Injective symIdx := by
  intro a b h; cases a <;> cases b <;> simp_all [symIdx]

/-- "At least one of `vars` is true": the single disjunction of positive literals. -/
def atLeastOne (vars : List ℕ) : Clause := vars.map (fun v => ⟨true, v⟩)

/-- "At most one of `vars` is true": for every ordered pair `(vᵢ, vⱼ)` the binary
    clause `¬vᵢ ∨ ¬vⱼ`. -/
def atMostOne : List ℕ → List Clause
  | [] => []
  | v :: vs => vs.map (fun w => ([⟨false, v⟩, ⟨false, w⟩] : Clause)) ++ atMostOne vs

/-- "Exactly one of `vars` is true" as a list of clauses (at-least-one and the
    pairwise at-most-one constraints). -/
def exactlyOne (vars : List ℕ) : List Clause := atLeastOne vars :: atMostOne vars

/-- The at-least-one clause is satisfied iff some variable in the list is true. -/
theorem atLeastOne_eval (α : Assignment) (vars : List ℕ) :
    Clause.eval α (atLeastOne vars) = vars.any (fun v => α.get v) := by
  simp only [atLeastOne, Clause.eval, List.any_map]
  congr 1
  funext v
  simp [Lit.eval]

/-- `CNF.eval` distributes over clause-list concatenation. -/
theorem eval_append (α : Assignment) (φ ψ : CNF) :
    CNF.eval α (φ ++ ψ) = (CNF.eval α φ && CNF.eval α ψ) := by
  simp [CNF.eval, List.all_append]

/-- The at-least-one clause is satisfied iff some listed variable is true (Prop form). -/
theorem atLeastOne_sat (α : Assignment) (vars : List ℕ) :
    Clause.eval α (atLeastOne vars) = true ↔ ∃ v ∈ vars, α.get v = true := by
  rw [atLeastOne_eval]; simp [List.any_eq_true]

/-- The at-most-one clauses are satisfied iff no two listed variables are both true. -/
theorem atMostOne_sat (α : Assignment) (vars : List ℕ) :
    CNF.eval α (atMostOne vars) = true ↔
      vars.Pairwise (fun v w => ¬(α.get v = true ∧ α.get w = true)) := by
  induction vars with
  | nil => simp [atMostOne]
  | cons v vs ih =>
    rw [atMostOne, eval_append, Bool.and_eq_true, ih, List.pairwise_cons]
    refine and_congr ?_ Iff.rfl
    simp only [CNF.eval, List.all_map, List.all_eq_true]
    refine forall_congr' fun w => imp_congr Iff.rfl ?_
    simp only [Function.comp_apply, Clause.eval, List.any_cons, List.any_nil,
      Bool.or_false, Lit.eval]
    generalize α.get v = a
    generalize α.get w = b
    cases a <;> cases b <;> simp

/-- The exactly-one clauses are satisfied iff exactly one listed variable is true
    (some variable is true, and no two are). The decoder for one-hot slots. -/
theorem exactlyOne_sat (α : Assignment) (vars : List ℕ) :
    CNF.eval α (exactlyOne vars) = true ↔
      (∃ v ∈ vars, α.get v = true) ∧
      vars.Pairwise (fun v w => ¬(α.get v = true ∧ α.get w = true)) := by
  rw [exactlyOne, CNF.eval_cons, Bool.and_eq_true, atLeastOne_sat, atMostOne_sat]

/-- A positive unit clause `[v]` is satisfied iff its variable is true. -/
@[simp] theorem unit_eval (α : Assignment) (v : ℕ) :
    Clause.eval α [(⟨true, v⟩ : Lit)] = α.get v := by
  simp [Clause.eval, Lit.eval]

/-- A list of positive unit clauses is satisfied iff every listed variable is true. -/
theorem allUnit_eval (α : Assignment) (vs : List ℕ) :
    CNF.eval α (vs.map (fun v => ([⟨true, v⟩] : Clause))) = true ↔ ∀ v ∈ vs, α.get v = true := by
  simp only [CNF.eval, List.all_map, List.all_eq_true, Function.comp_apply, unit_eval]

/-- Index of a machine state as a natural, via the canonical `Fintype` enumeration
    of `N.Q`; injective, so a one-hot encoding over `Fin (card Q)` names the states. -/
noncomputable def stateIdx {k : ℕ} (N : NTM k) (q : N.Q) : ℕ := (Fintype.equivFin N.Q q).val

theorem stateIdx_inj {k : ℕ} (N : NTM k) : Function.Injective (stateIdx N) := by
  intro a b h
  exact (Fintype.equivFin N.Q).injective (Fin.val_injective h)

/-- The symbol at position `pos` of tape `tp` in the start configuration on input
    `x`: cell `0` is always `▷`; tape `0` (the input) carries `x` at cells `1…|x|`;
    every other cell is blank. Mirrors `initTape` applied to each tape. -/
def initCellSym (x : List Bool) (tp pos : ℕ) : Γ :=
  if pos = 0 then Γ.start
  else if tp = 0 then ((x.map Γ.ofBool)[pos - 1]?).getD Γ.blank
  else Γ.blank

/-- One-hot constraint that every time-step `0…steps` is in exactly one state. -/
noncomputable def oneHotStates {k : ℕ} (N : NTM k) (steps : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    exactlyOne ((List.range (Fintype.card N.Q)).map (vState t))

/-- One-hot constraint that every cell (each tape `0…k+1`, position `0…P`, time
    `0…steps`) holds exactly one of the four symbols. -/
def oneHotCells (k steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        exactlyOne ((List.range 4).map (vCell t tp pos))

/-- One-hot constraint that every tape head (each tape `0…k+1`, time `0…steps`) is
    at exactly one position in `0…P`. -/
def oneHotHeads (k steps P : ℕ) : List Clause :=
  (List.range (steps + 1)).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      exactlyOne ((List.range (P + 1)).map (vHead t tp))

/-- Unit clauses fixing the start configuration at time `0`: state `qstart`, every
    head at cell `0`, and every cell holding its `initCellSym` value. -/
noncomputable def startClauses {k : ℕ} (N : NTM k) (steps : ℕ) (x : List Bool) :
    List Clause :=
  let P := steps + x.length + 1
  ([⟨true, vState 0 (stateIdx N N.qstart)⟩] : Clause) ::
    ((List.range (k + 2)).map (fun tp => ([⟨true, vHead 0 tp 0⟩] : Clause)) ++
     (List.range (k + 2)).flatMap (fun tp =>
       (List.range (P + 1)).map (fun pos =>
         ([⟨true, vCell 0 tp pos (symIdx (initCellSym x tp pos))⟩] : Clause))))

/-- Unit clauses fixing acceptance at time `steps`: the state is `qhalt` and cell
    `1` of the output tape (index `k+1`) holds `1`. -/
noncomputable def acceptClauses {k : ℕ} (N : NTM k) (steps : ℕ) : List Clause :=
  [[⟨true, vState steps (stateIdx N N.qhalt)⟩],
   [⟨true, vCell steps (k + 1) 1 (symIdx Γ.one)⟩]]

/-- **Transition frame.** A cell not under its tape's head keeps its symbol from
    time `t` to `t+1`. For each tape/position/symbol, the two clauses encode
    `¬(head at pos) → (cellₜ = cellₜ₊₁)` (a head literal disjoined with each
    direction of the `↔`). The complementary "active" clauses (cell under the head
    updated per `N.δ`) are supplied separately. -/
def frameClauses (k steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (List.range (k + 2)).flatMap fun tp =>
      (List.range (P + 1)).flatMap fun pos =>
        (List.range 4).flatMap fun s =>
          [([⟨true, vHead t tp pos⟩, ⟨false, vCell t tp pos s⟩,
              ⟨true, vCell (t + 1) tp pos s⟩] : Clause),
           ([⟨true, vHead t tp pos⟩, ⟨true, vCell t tp pos s⟩,
              ⟨false, vCell (t + 1) tp pos s⟩] : Clause)]

/-- New head position after a move (mirrors `Tape.move`): `left` decrements
    (clamped at `0` by `Nat` subtraction), `right` increments, `stay` keeps. -/
def posMove (pos : ℕ) (d : Dir3) : ℕ :=
  match d with
  | Dir3.left => pos - 1
  | Dir3.right => pos + 1
  | Dir3.stay => pos

/-- The four tape symbols, enumerated. -/
def allSyms : List Γ := [Γ.zero, Γ.one, Γ.blank, Γ.start]

/-- **Active transition clauses** (single work tape; tapes `0`=input, `1`=work,
    `2`=output). For every time `t`, state `q`, head positions/symbols on the three
    tapes, and choice bit `b`, let `(q', wW, oW, iD, wD, oD) = N.δ b q …` be the
    induced step. Each emitted clause is `¬(read-config ∧ choice=b) ∨ consequence`,
    one consequence per fact: the next state is `q'`, the input cell is unchanged
    (read-only), the work/output cells under their heads become `wW`/`oW`, and the
    three heads move per `iD`/`wD`/`oD` (via `posMove`). -/
noncomputable def activeTransitionClauses (N : NTM 1) (steps P : ℕ) : List Clause :=
  (List.range steps).flatMap fun t =>
    (Finset.univ : Finset N.Q).toList.flatMap fun q =>
      (List.range (P + 1)).flatMap fun pi =>
        allSyms.flatMap fun si =>
          (List.range (P + 1)).flatMap fun pw =>
            allSyms.flatMap fun sw =>
              (List.range (P + 1)).flatMap fun po =>
                allSyms.flatMap fun so =>
                  [true, false].flatMap fun b =>
                    let out := N.δ b q si (fun _ => sw) so
                    let cond : Clause :=
                      [⟨false, vState t (stateIdx N q)⟩,
                       ⟨false, vHead t 0 pi⟩, ⟨false, vCell t 0 pi (symIdx si)⟩,
                       ⟨false, vHead t 1 pw⟩, ⟨false, vCell t 1 pw (symIdx sw)⟩,
                       ⟨false, vHead t 2 po⟩, ⟨false, vCell t 2 po (symIdx so)⟩,
                       ⟨!b, vChoice t⟩]
                    [cond ++ [⟨true, vState (t + 1) (stateIdx N out.1)⟩],
                     cond ++ [⟨true, vCell (t + 1) 0 pi (symIdx si)⟩],
                     cond ++ [⟨true, vCell (t + 1) 1 pw (symIdx (out.2.1 0).toΓ)⟩],
                     cond ++ [⟨true, vCell (t + 1) 2 po (symIdx out.2.2.1.toΓ)⟩],
                     cond ++ [⟨true, vHead (t + 1) 0 (posMove pi out.2.2.2.1)⟩],
                     cond ++ [⟨true, vHead (t + 1) 1 (posMove pw (out.2.2.2.2.1 0))⟩],
                     cond ++ [⟨true, vHead (t + 1) 2 (posMove po out.2.2.2.2.2)⟩]]

/-- The acceptance clauses hold iff the final state is `qhalt` and output cell `1`
    holds `1` (the two facts witnessing an accepting halt). -/
theorem acceptClauses_sat (N : NTM 1) (steps : ℕ) (α : Assignment) :
    CNF.eval α (acceptClauses N steps) = true ↔
      α.get (vState steps (stateIdx N N.qhalt)) = true ∧
      α.get (vCell steps 2 1 (symIdx Γ.one)) = true := by
  simp [acceptClauses, CNF.eval, Clause.eval, Lit.eval]

end Tableau

/-- **Computation-tableau formula.** `tableauCNF N steps x` is the CNF that is
    satisfiable exactly when the (single-work-tape) machine `N` has an accepting
    computation on input `x` within `steps` steps — variables encode the tape /
    head / state contents at each time-step together with the nondeterministic
    choice bits, and clauses enforce the start configuration, per-step transition
    validity, and acceptance. **Definition to be supplied.** -/
noncomputable def tableauCNF (N : NTM 1) (steps : ℕ) (x : List Bool) : CNF :=
  let P := steps + x.length + 1
  Tableau.oneHotStates N steps ++ Tableau.oneHotCells 1 steps P ++
    Tableau.oneHotHeads 1 steps P ++ Tableau.startClauses N steps x ++
    Tableau.frameClauses 1 steps P ++ Tableau.activeTransitionClauses N steps P ++
    Tableau.acceptClauses N steps

/-- **Tableau correctness (core).** The tableau formula is satisfiable iff `N`
    accepts `x` within `steps` steps. -/
theorem tableauCNF_satisfiable_iff (N : NTM 1) (steps : ℕ) (x : List Bool) :
    (tableauCNF N steps x).Satisfiable ↔ N.AcceptsInTime x steps := by
  sorry

/-- An encoded CNF is in `L_SAT` iff it is satisfiable (`CNF.encode` is injective,
    via `CNF.decode?_encode`). -/
theorem encode_mem_LSAT_iff (φ : CNF) : φ.encode ∈ L_SAT ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨φ', hφ', hsat⟩
    have hφ : φ = φ' := by
      have h := CNF.decode?_encode φ
      rw [hφ'] at h
      exact Option.some.inj (h.symm.trans (CNF.decode?_encode φ'))
    rw [hφ]; exact hsat
  · exact fun hsat => ⟨φ, rfl, hsat⟩

/-- The Cook–Levin reduction function: map each input to the encoding of its
    computation-tableau formula. -/
noncomputable def reductionFn (N : NTM 1) (T : ℕ → ℕ) : List Bool → List Bool :=
  fun x => (tableauCNF N (T x.length) x).encode

/-- **The reduction is polynomial-time computable.** The tableau has size
    polynomial in `T |x|` (hence in `|x|`), and a deterministic machine emits its
    encoding in polynomial time. **Proof obligation (dominant cost).** -/
theorem reductionFn_mem_FP (N : NTM 1) (T : ℕ → ℕ) (c : ℕ) (hTO : T =O (· ^ c)) :
    reductionFn N T ∈ FP := by
  sorry

/-- **The reduction is correct.** `x ∈ L` iff the reduction output is in `L_SAT`,
    combining the tableau characterization with `N` deciding `L`. -/
theorem tableauCNF_correct {L : Language} (N : NTM 1) (T : ℕ → ℕ)
    (hdec : N.DecidesInTime L T) (x : List Bool) :
    x ∈ L ↔ reductionFn N T x ∈ L_SAT := by
  unfold reductionFn
  rw [encode_mem_LSAT_iff, tableauCNF_satisfiable_iff]
  exact hdec.2 x

/-- **Single-tape Cook–Levin reduction.** A single-work-tape machine deciding `L`
    in polynomial time yields a polynomial-time many-one reduction to `L_SAT`. -/
theorem cookLevin_reduction_singleTape {L : Language} (N : NTM 1) (T : ℕ → ℕ) (c : ℕ)
    (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    L ≤ₚ L_SAT :=
  ⟨reductionFn N T, reductionFn_mem_FP N T c hTO, tableauCNF_correct N T hdec⟩

/-- **Per-machine Cook–Levin reduction.** If a nondeterministic machine `N`
    decides `L` within a polynomial time bound, then `L` polynomial-time many-one
    reduces to `L_SAT`. Reduces to the single-work-tape case
    (`NTM.exists_singleTape_decider`) and then builds the tableau formula. -/
theorem cookLevin_reduction {k : ℕ} {L : Language} (N : NTM k) (T : ℕ → ℕ) (c : ℕ)
    (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    L ≤ₚ L_SAT := by
  obtain ⟨N', T', c', hdec', hTO'⟩ := N.exists_singleTape_decider hdec hTO
  exact cookLevin_reduction_singleTape N' T' c' hdec' hTO'

/-- **NP-hardness of SAT.** Every language in `NP` polynomial-time reduces to
    `L_SAT`. -/
theorem NPHard_L_SAT : NPHard L_SAT := by
  intro L hL
  obtain ⟨d, hLd⟩ := Set.mem_iUnion.mp hL
  obtain ⟨k, N, f, hdec, hfO⟩ := hLd
  exact cookLevin_reduction N f d hdec hfO

/-- **Cook–Levin theorem: SAT is NP-complete.** -/
theorem NPComplete_L_SAT : NPComplete L_SAT :=
  ⟨L_SAT_mem_NP, NPHard_L_SAT⟩

end SAT
