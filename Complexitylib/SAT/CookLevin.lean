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

end Tableau

/-- **Computation-tableau formula.** `tableauCNF N steps x` is the CNF that is
    satisfiable exactly when the (single-work-tape) machine `N` has an accepting
    computation on input `x` within `steps` steps — variables encode the tape /
    head / state contents at each time-step together with the nondeterministic
    choice bits, and clauses enforce the start configuration, per-step transition
    validity, and acceptance. **Definition to be supplied.** -/
noncomputable def tableauCNF {k : ℕ} (N : NTM k) (steps : ℕ) (x : List Bool) : CNF := sorry

/-- **Tableau correctness (core).** The tableau formula is satisfiable iff `N`
    accepts `x` within `steps` steps. -/
theorem tableauCNF_satisfiable_iff {k : ℕ} (N : NTM k) (steps : ℕ) (x : List Bool) :
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
noncomputable def reductionFn {k : ℕ} (N : NTM k) (T : ℕ → ℕ) : List Bool → List Bool :=
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
