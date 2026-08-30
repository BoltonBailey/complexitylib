/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph
public import Complexitylib.SAT.ThreeCNF

/-!
# From 3CNF-SAT to binary constraint graphs

The standard reduction turning a 3CNF formula into a constraint graph over the
alphabet `Fin 3 → Bool`, together with its correctness proof. This is the entry
point of Dinur's proof of the PCP theorem: it produces the constraint graph
whose unsatisfiability value the amplification step then boosts.

## The construction

Given `φ : CNF`, the graph `toGraph φ` has

* one **variable vertex** for each variable index `0 … φ.maxVar`, and
* one **clause vertex** for each clause of `φ`, numbered `(φ.maxVar + 1) + j`;
* one edge for each (clause, position) pair, so `3 * φ.length` edges in all.

A variable vertex is meant to carry the value of its variable in bit `0` of its
label; a clause vertex is meant to carry the values of the three variables its
clause mentions, one per coordinate. The edge for clause `j` and position `p`
checks both that the clause vertex's triple satisfies clause `j` and that its
`p`-th coordinate agrees with the `p`-th variable vertex — the usual
consistency-plus-satisfaction pair of constraints.

## Main definitions

- `litOf` — a total lookup of the literal at a given clause and position
- `numVerts`, `numEdges`, `varVertex`, `clauseVertex`, `edgeClause`, `edgePos`
- `clauseSat` — whether a triple of bits satisfies a clause
- `toGraph` — the constraint graph produced by the reduction
- `vertexLabel`, `mkAssign` — the two translations between assignments

## Main results

- `numVerts_toGraph`, `numEdges_toGraph` — the size of the produced graph
- `satisfiable_toGraph_iff` — correctness of the reduction on 3CNF inputs
-/

@[expose] public section

namespace Complexity

namespace ThreeSATCSP

open SAT

/-! ### Indexing helpers -/

/-- The literal at position `p` of clause `j` of `φ`, defaulting to the positive
literal on variable `0` when either index is out of range. Totality keeps the
reduction free of dependent-index bookkeeping. -/
def litOf (φ : CNF) (j : ℕ) (p : Fin 3) : Lit :=
  ((φ[j]?).getD []).getD p.val ⟨false, 0⟩

/-- The number of vertices of the constraint graph of `φ`: one per variable
index `0 … φ.maxVar`, then one per clause. -/
def numVerts (φ : CNF) : ℕ := (φ.maxVar + 1) + φ.length

/-- The number of edges of the constraint graph of `φ`: three per clause. -/
def numEdges (φ : CNF) : ℕ := 3 * φ.length

/-- The constraint graph of `φ` always has at least one vertex, namely the
variable vertex `0`. -/
theorem numVerts_pos (φ : CNF) : 0 < numVerts φ := by
  unfold numVerts; omega

/-- The vertex carrying the value of variable `v`; out-of-range indices are
folded onto vertex `0`. -/
def varVertex (φ : CNF) (v : ℕ) : Fin (numVerts φ) :=
  if h : v < numVerts φ then ⟨v, h⟩ else ⟨0, numVerts_pos φ⟩

/-- The vertex carrying the claimed values of the variables of clause `j`;
out-of-range indices are folded onto vertex `0`. -/
def clauseVertex (φ : CNF) (j : ℕ) : Fin (numVerts φ) :=
  if h : (φ.maxVar + 1) + j < numVerts φ then ⟨(φ.maxVar + 1) + j, h⟩
  else ⟨0, numVerts_pos φ⟩

/-- The clause that edge number `e` belongs to. -/
def edgeClause (e : ℕ) : ℕ := e / 3

/-- The position inside its clause that edge number `e` checks. -/
def edgePos (e : ℕ) : Fin 3 := ⟨e % 3, Nat.mod_lt _ (by omega)⟩

/-- Whether the triple `cl` of claimed variable values satisfies clause `j`:
some position's claimed value matches that literal's sign. -/
def clauseSat (φ : CNF) (j : ℕ) (cl : Fin 3 → Bool) : Bool :=
  decide (∃ q : Fin 3, cl q = (litOf φ j q).sign)

/-- `clauseSat` reflects the existential it decides. -/
theorem clauseSat_eq_true_iff {φ : CNF} {j : ℕ} {cl : Fin 3 → Bool} :
    clauseSat φ j cl = true ↔ ∃ q : Fin 3, cl q = (litOf φ j q).sign := by
  simp [clauseSat]

/-! ### The reduction -/

/-- The constraint graph of a 3CNF formula `φ`. Variable vertices come first,
clause vertices after them; edge `e` links clause vertex `edgeClause e` to the
variable vertex of the literal at position `edgePos e` of that clause, and its
constraint demands both that the clause vertex's triple satisfies the clause and
that it agrees with the variable vertex on bit `0`. -/
def toGraph (φ : CNF) : ConstraintGraph (Fin 3 → Bool) where
  numVerts := numVerts φ
  numEdges := numEdges φ
  tail e := clauseVertex φ (edgeClause e.val)
  head e := varVertex φ (litOf φ (edgeClause e.val) (edgePos e.val)).var
  rel e cl va := clauseSat φ (edgeClause e.val) cl && (cl (edgePos e.val) == va 0)

/-- The reduction produces `3 * φ.length` edges. -/
theorem numEdges_toGraph (φ : CNF) : (toGraph φ).numEdges = 3 * φ.length := rfl

/-- The reduction produces `(φ.maxVar + 1) + φ.length` vertices. -/
theorem numVerts_toGraph (φ : CNF) :
    (toGraph φ).numVerts = (φ.maxVar + 1) + φ.length := rfl

/-! ### Basic facts about the indexing helpers -/

/-- A variable vertex within range keeps its index. -/
theorem varVertex_val {φ : CNF} {v : ℕ} (hv : v ≤ φ.maxVar) :
    (varVertex φ v).val = v := by
  have h : v < numVerts φ := by unfold numVerts; omega
  simp [varVertex, h]

/-- A clause vertex of an existing clause sits at index `(φ.maxVar + 1) + j`. -/
theorem clauseVertex_val {φ : CNF} {j : ℕ} (hj : j < φ.length) :
    (clauseVertex φ j).val = (φ.maxVar + 1) + j := by
  have h : (φ.maxVar + 1) + j < numVerts φ := by unfold numVerts; omega
  simp [clauseVertex, h]

/-- `litOf` really reads the list entry it is meant to read. -/
theorem litOf_eq {φ : CNF} {j : ℕ} {c : Clause} (hc : φ[j]? = some c) {p : Fin 3}
    (hp : p.val < c.length) : litOf φ j p = c[p.val] := by
  rw [litOf, hc, Option.getD_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hp, Option.getD_some]

/-- Every literal produced by `litOf` at an existing clause really occurs in
that clause, provided the clause has three literals. -/
theorem litOf_mem {φ : CNF} {j : ℕ} {c : Clause} (hc : φ[j]? = some c)
    (hlen : c.length = 3) (p : Fin 3) : litOf φ j p ∈ c := by
  have hp : p.val < c.length := by omega
  rw [litOf_eq hc hp]
  exact List.getElem_mem hp

/-- Every edge belongs to a clause that exists. -/
theorem edgeClause_lt {φ : CNF} (e : Fin (toGraph φ).numEdges) :
    edgeClause e.val < φ.length := by
  have h : e.val < 3 * φ.length := e.isLt
  unfold edgeClause
  omega

/-- Every (clause, position) pair is realized by an edge. -/
theorem exists_edge {φ : CNF} {j : ℕ} (hj : j < φ.length) (q : Fin 3) :
    ∃ e : Fin (toGraph φ).numEdges, edgeClause e.val = j ∧ edgePos e.val = q := by
  refine ⟨⟨3 * j + q.val, ?_⟩, ?_, ?_⟩
  · show 3 * j + q.val < 3 * φ.length; omega
  · show (3 * j + q.val) / 3 = j; omega
  · apply Fin.ext; show (3 * j + q.val) % 3 = q.val; omega

/-- The edge constraint of `toGraph`, spelled out. -/
theorem satisfies_iff {φ : CNF} {a : (toGraph φ).Assignment}
    (e : Fin (toGraph φ).numEdges) :
    (toGraph φ).Satisfies a e ↔
      (clauseSat φ (edgeClause e.val) (a (clauseVertex φ (edgeClause e.val))) = true ∧
        a (clauseVertex φ (edgeClause e.val)) (edgePos e.val)
          = a (varVertex φ (litOf φ (edgeClause e.val) (edgePos e.val)).var) 0) := by
  simp [ConstraintGraph.Satisfies, ConstraintGraph.satisfies, toGraph]

/-- Every literal of a 3CNF formula mentions a variable at most `φ.maxVar`. -/
theorem var_litOf_le_maxVar {φ : CNF} (h3 : φ.Is3CNF) {j : ℕ} (hj : j < φ.length)
    (p : Fin 3) : (litOf φ j p).var ≤ φ.maxVar := by
  have hmem : φ[j] ∈ φ := List.getElem_mem hj
  have hc : φ[j]? = some φ[j] := List.getElem?_eq_getElem hj
  have hlen : (φ[j]).length = 3 := h3 _ hmem
  calc (litOf φ j p).var ≤ (φ[j]).maxVar :=
        Clause.var_le_maxVar (litOf_mem hc hlen p)
    _ ≤ φ.maxVar := CNF.clause_maxVar_le_maxVar hmem

/-! ### Translating assignments -/

/-- The label the graph assignment induced by a CNF assignment `α` puts on
vertex number `w`: a variable vertex gets the constant value of its variable, a
clause vertex gets the values of the three variables its clause mentions. -/
def vertexLabel (φ : CNF) (α : SAT.Assignment) (w : ℕ) : Fin 3 → Bool :=
  if w < φ.maxVar + 1 then (fun _ => Assignment.get α w)
  else (fun q => Assignment.get α (litOf φ (w - (φ.maxVar + 1)) q).var)

/-- The label of a variable vertex. -/
theorem vertexLabel_var {φ : CNF} {α : SAT.Assignment} {v : ℕ} (hv : v ≤ φ.maxVar) :
    vertexLabel φ α v = fun _ => Assignment.get α v := by
  have h : v < φ.maxVar + 1 := by omega
  simp [vertexLabel, h]

/-- The label of a clause vertex. -/
theorem vertexLabel_clause {φ : CNF} {α : SAT.Assignment} {j : ℕ} :
    vertexLabel φ α ((φ.maxVar + 1) + j)
      = fun q => Assignment.get α (litOf φ j q).var := by
  have h : ¬ ((φ.maxVar + 1) + j < φ.maxVar + 1) := by omega
  simp [vertexLabel, h]

/-- The CNF assignment read off from a graph assignment: variable `v` takes the
value of bit `0` of the label of its variable vertex. -/
def mkAssign (φ : CNF) (a : (toGraph φ).Assignment) : SAT.Assignment :=
  (List.range (φ.maxVar + 1)).map (fun v => a (varVertex φ v) 0)

/-- `mkAssign` reads back the label bit it was built from. -/
theorem get_mkAssign {φ : CNF} {a : (toGraph φ).Assignment} {v : ℕ}
    (hv : v ≤ φ.maxVar) : Assignment.get (mkAssign φ a) v = a (varVertex φ v) 0 := by
  have hr : v < (List.range (φ.maxVar + 1)).length := by simp; omega
  simp [Assignment.get, mkAssign, List.getElem?_map,
    List.getElem?_eq_getElem hr]

/-! ### Correctness -/

/-- **Correctness of the reduction.** For a 3CNF formula, the constraint graph
produced by `toGraph` is satisfiable exactly when the formula is. -/
theorem satisfiable_toGraph_iff {φ : CNF} (h3 : φ.Is3CNF) :
    (toGraph φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨mkAssign φ a, ?_⟩
    rw [CNF.eval, List.all_eq_true]
    intro c hcmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcmem
    obtain ⟨e0, hc0, -⟩ := exists_edge (φ := φ) hj 0
    have h0 := (satisfies_iff e0).mp (ha e0)
    rw [hc0] at h0
    obtain ⟨q, hq⟩ := clauseSat_eq_true_iff.mp h0.1
    obtain ⟨e1, hc1, hp1⟩ := exists_edge (φ := φ) hj q
    have h1 := (satisfies_iff e1).mp (ha e1)
    rw [hc1, hp1] at h1
    have hvar : (litOf φ j q).var ≤ φ.maxVar := var_litOf_le_maxVar h3 hj q
    have hval : Assignment.get (mkAssign φ a) (litOf φ j q).var = (litOf φ j q).sign := by
      rw [get_mkAssign hvar, ← h1.2, hq]
    rw [Clause.eval, List.any_eq_true]
    refine ⟨litOf φ j q, litOf_mem (List.getElem?_eq_getElem hj) (h3 _ hcmem) q, ?_⟩
    simp [Lit.eval, hval]
  · rintro ⟨α, hα⟩
    refine ⟨fun w => vertexLabel φ α w.val, ?_⟩
    intro e
    have hj : edgeClause e.val < φ.length := edgeClause_lt e
    rw [satisfies_iff]
    set j := edgeClause e.val with hjd
    set p := edgePos e.val with hpd
    have hvar : (litOf φ j p).var ≤ φ.maxVar := var_litOf_le_maxVar h3 hj p
    have hcl : vertexLabel φ α (clauseVertex φ j).val
        = fun q => Assignment.get α (litOf φ j q).var := by
      rw [clauseVertex_val hj]; exact vertexLabel_clause
    have hhead : vertexLabel φ α (varVertex φ (litOf φ j p).var).val
        = fun _ => Assignment.get α (litOf φ j p).var := by
      rw [varVertex_val hvar]; exact vertexLabel_var hvar
    simp only [hcl, hhead]
    refine ⟨clauseSat_eq_true_iff.mpr ?_, trivial⟩
    have hlen : (φ[j]).length = 3 := h3 _ (List.getElem_mem hj)
    have hcls : Clause.eval α φ[j] = true := by
      rw [CNF.eval, List.all_eq_true] at hα
      exact hα _ (List.getElem_mem hj)
    rw [Clause.eval, List.any_eq_true] at hcls
    obtain ⟨ℓ, hℓmem, hℓ⟩ := hcls
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hℓmem
    refine ⟨⟨i, by omega⟩, ?_⟩
    rw [litOf_eq (p := ⟨i, by omega⟩) (List.getElem?_eq_getElem hj) hi]
    simpa [Lit.eval] using hℓ

end ThreeSATCSP

end Complexity
