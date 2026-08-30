/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.SubsetNP
public import Complexitylib.SAT.Semantics
public import Complexitylib.SAT.Language
public import Complexitylib.SAT.Verifier

/-!
# A PCP verifier as a CNF formula

`SubsetNP` reduces "some proof is accepted on every coin string" to "some
bitstring is a witness": a table, laid out one block of `Q` answers per coin
string, that is consistent and accepted everywhere. Both conditions are
predicates on individual bits of that bitstring, so both are CNF clauses.

That is what this module builds. The formula's variables *are* the positions of
the witness — a SAT assignment and a witness are the same object, since both
read out of range as `false` — so the encoding needs no translation of models.

* Consistency contributes, for each pair of query slots that read the same proof
  position, the two clauses saying their variables agree.
* Acceptance contributes, for each coin string and each answer vector the
  verdict rejects, the clause blocking that vector.

With `r` coins and `q` queries the formula has `2^r q` variables and
`O(4^r q^2 + 2^r 2^q)` clauses — polynomial when `r` is logarithmic and `q`
constant.

## Main definitions

- `Complexity.allVecs` — the bit vectors of a given length
- `Complexity.PCPVerifier.varIdx` — the variable holding one answer
- `Complexity.PCPVerifier.toCNF` — the formula

## Main results

- `Complexity.mem_allVecs_iff` — `allVecs n` is exactly the vectors of length `n`
-/

@[expose] public section

namespace Complexity

open SAT

/-! ### Enumerating bit vectors -/

/-- Every bit vector of a given length. -/
def allVecs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).flatMap fun v => [false :: v, true :: v]

theorem mem_allVecs_iff : ∀ (n : ℕ) (b : List Bool), b ∈ allVecs n ↔ b.length = n := by
  intro n
  induction n with
  | zero =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_singleton] at hb
        rw [hb]
        rfl
      · intro hb
        have : b = [] := List.length_eq_zero_iff.1 hb
        rw [this]
        simp [allVecs]
  | succ m ih =>
      intro b
      constructor
      · intro hb
        simp only [allVecs, List.mem_flatMap] at hb
        obtain ⟨v, hv, hbv⟩ := hb
        have hlen : v.length = m := (ih v).1 hv
        simp only [List.mem_cons] at hbv
        rcases hbv with h | h | h
        · rw [h, List.length_cons, hlen]
        · rw [h, List.length_cons, hlen]
        · exact absurd h (by simp)
      · intro hb
        match b with
        | [] => exact absurd hb (by simp)
        | c :: v =>
            have hlen : v.length = m := by
              rw [List.length_cons] at hb
              omega
            simp only [allVecs, List.mem_flatMap]
            refine ⟨v, (ih v).2 hlen, ?_⟩
            cases c <;> simp

namespace PCPVerifier

variable (V : PCPVerifier)

/-! ### Variables -/

/-- The variable holding the answer to query `i` on coin string `ρ`. The blocks
sit a stride `Q` apart, exactly as `SubsetNP.tableOf` reads them. -/
def varIdx (t Q : ℕ) (ρ : Fin t → Bool) (i : ℕ) : ℕ := coinIndex ρ * Q + i

/-! ### The clauses -/

/-- The coin strings, listed by index. Computable, unlike an enumeration drawn
from `Finset.univ`, because the reduction has to be carried out by a machine. -/
def coinList (t : ℕ) : List (Fin t → Bool) :=
  (List.finRange (2 ^ t)).map coinOfIndex

/-- Two query slots reading the same proof position must get the same answer. -/
def consClauses (t Q : ℕ) (x : List Bool) : List Clause :=
  (coinList t).flatMap fun ρ =>
    (coinList t).flatMap fun ρ' =>
      (List.range (V.positions x (BitString.toList ρ)).length).flatMap fun i =>
        (List.range (V.positions x (BitString.toList ρ')).length).flatMap fun i' =>
          if (V.positions x (BitString.toList ρ))[i]?
              = (V.positions x (BitString.toList ρ'))[i']? then
            [[⟨false, varIdx t Q ρ i⟩, ⟨true, varIdx t Q ρ' i'⟩],
              [⟨true, varIdx t Q ρ i⟩, ⟨false, varIdx t Q ρ' i'⟩]]
          else []

/-- For each coin string, a clause blocking every answer vector the verdict
rejects. The verdict arrives as a Boolean function, which is the form a
polynomial-time decision procedure takes. -/
def acceptClauses (g : List Bool → Bool) (t Q : ℕ) (x : List Bool) : List Clause :=
  (coinList t).flatMap fun ρ =>
    ((allVecs (V.positions x (BitString.toList ρ)).length).filter fun b =>
        !g (pair (pair x (BitString.toList ρ)) b)).map fun b =>
      (List.range (V.positions x (BitString.toList ρ)).length).map fun i =>
        (⟨!(b.getD i false), varIdx t Q ρ i⟩ : Lit)

/-- **The formula of a verifier on an input.** -/
def toCNF (g : List Bool → Bool) (t Q : ℕ) (x : List Bool) : CNF :=
  V.consClauses t Q x ++ V.acceptClauses g t Q x

/-! ### The reduction, at the level of membership -/

/-- The query budget used for a given input: one more than the bound, so that
the stride is positive even when the verifier makes no queries. -/
def budget (q : ℕ → ℕ) (x : List Bool) : ℕ := q x.length + 1

end PCPVerifier

end Complexity
