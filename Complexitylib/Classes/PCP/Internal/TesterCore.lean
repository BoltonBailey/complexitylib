/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.TesterChecks

/-!
# The assignment tester, assembled

The six checks of the Hadamard assignment tester, run on one bundled random
string, on raw tables, with a universal soundness constant.

The tester is handed two **input tables** `Tt Th : Cube B → ZMod 2` — in the
composition, the Hadamard encodings of the labels at the two ends of an outer
edge — and a **proof** consisting of a linear table `F` over `n` variables and
a quadratic table `G` over `n * n`, where the `n` variables are the `2 · 2^B`
input coordinates followed by the selectors of a one-hot system. Its random
string has six blocks, one per check:

1. linearity of `F`; 2. linearity of `G`; 3. consistency of `G` with `F`;
4. the one-hot system, by a random linear combination; 5. and 6. the two
input tables, one coordinate each.

Every check reads a constant number of positions — never a whole table — so
the total query count is a constant independent of `B`, and the soundness
constant `1/32` is universal. That independence is the point of the tester:
the outer alphabet may be enormous, and neither the query count nor the
soundness loss may notice.

## Main definitions

- `Complexity.Tester.AllChecks` — the tester's verdict on a random string

## Main results

- `Complexity.Tester.sound` — passing with probability above `31/32` yields an
  assignment satisfying the system whose input parts are within `3/32` of the
  input tables
- `Complexity.Tester.complete` — the honest proof of a satisfying assignment
  passes on every random string
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

namespace Tester

/-! ### Layout -/

/-- The number of input variables: two tables of `2^B` coordinates. -/
abbrev kOf (B : ℕ) : ℕ := 2 ^ B + 2 ^ B

/-- The number of variables: input coordinates and one-hot selectors. -/
abbrev nOf (B : ℕ) : ℕ := kOf B + 2 ^ kOf B

/-- The number of constraints in the one-hot system. -/
abbrev JOf (B : ℕ) : ℕ := Fintype.card (OneHotIdx (kOf B))

/-- The variable holding coordinate `r` of the first input table. -/
noncomputable def inTail (B : ℕ) (r : Cube B) : Fin (nOf B) :=
  Fin.castAdd (2 ^ kOf B) (Fin.castAdd (2 ^ B) (candIdx B r))

/-- The variable holding coordinate `r` of the second input table. -/
noncomputable def inHead (B : ℕ) (r : Cube B) : Fin (nOf B) :=
  Fin.castAdd (2 ^ kOf B) (Fin.natAdd (2 ^ B) (candIdx B r))

/-- The first input table an assignment of the variables carries. -/
noncomputable def tailPart {B : ℕ} (a : Cube (nOf B)) : Cube B → ZMod 2 :=
  fun r => a (inTail B r)

/-- The second input table an assignment of the variables carries. -/
noncomputable def headPart {B : ℕ} (a : Cube (nOf B)) : Cube B → ZMod 2 :=
  fun r => a (inHead B r)

/-- The random bits of the linearity check on `F`. -/
abbrev R1 (B : ℕ) : ℕ := nOf B + nOf B
/-- The random bits of the linearity check on `G`. -/
abbrev R2 (B : ℕ) : ℕ := nOf B * nOf B + nOf B * nOf B
/-- The random bits of the consistency check. -/
abbrev R3 (B : ℕ) : ℕ := (nOf B + nOf B) + (nOf B + (nOf B + nOf B * nOf B))
/-- The random bits of the constraint check. -/
abbrev R4 (B : ℕ) : ℕ := JOf B + (nOf B + nOf B * nOf B)
/-- The random bits of one input check. -/
abbrev R5 (B : ℕ) : ℕ := B + nOf B

/-- The random bits of the last two blocks. -/
abbrev Rest5 (B : ℕ) : ℕ := R5 B + R5 B
/-- The random bits of the last three blocks. -/
abbrev Rest4 (B : ℕ) : ℕ := R4 B + Rest5 B
/-- The random bits of the last four blocks. -/
abbrev Rest3 (B : ℕ) : ℕ := R3 B + Rest4 B
/-- The random bits after the first block. -/
abbrev Rest2 (B : ℕ) : ℕ := R2 B + Rest3 B

/-- The total number of random bits. -/
abbrev ROf (B : ℕ) : ℕ := R1 B + Rest2 B

variable {B : ℕ}

/-- The first block of the random string: linearity of `F`. -/
def blk1 (z : Cube (ROf B)) : Cube (R1 B) := leftBlock z
/-- The second block: linearity of `G`. -/
def blk2 (z : Cube (ROf B)) : Cube (R2 B) := leftBlock (rightBlock z)
/-- The third block: consistency. -/
def blk3 (z : Cube (ROf B)) : Cube (R3 B) := leftBlock (rightBlock (rightBlock z))
/-- The fourth block: the constraint system. -/
def blk4 (z : Cube (ROf B)) : Cube (R4 B) := leftBlock (rightBlock (rightBlock (rightBlock z)))
/-- The fifth block: the first input table. -/
def blk5 (z : Cube (ROf B)) : Cube (R5 B) :=
  leftBlock (rightBlock (rightBlock (rightBlock (rightBlock z))))
/-- The sixth block: the second input table. -/
def blk6 (z : Cube (ROf B)) : Cube (R5 B) :=
  rightBlock (rightBlock (rightBlock (rightBlock (rightBlock z))))

/-! ### Each block is uniform -/

theorem prob_blk1 (P : Cube (R1 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk1 z)] = Pr[P] :=
  prob_leftBlock P

theorem prob_blk2 (P : Cube (R2 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk2 z)] = Pr[P] := by
  have h1 := prob_rightBlock (a := R1 B) (fun w : Cube (Rest2 B) => P (leftBlock w))
  rw [show (fun z : Cube (ROf B) => P (blk2 z)) = fun z => P (leftBlock (rightBlock z)) from rfl,
    h1]
  exact prob_leftBlock P

theorem prob_blk3 (P : Cube (R3 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk3 z)] = Pr[P] := by
  have h1 := prob_rightBlock (a := R1 B)
    (fun w : Cube (Rest2 B) => P (leftBlock (rightBlock w)))
  have h2 := prob_rightBlock (a := R2 B) (fun w : Cube (Rest3 B) => P (leftBlock w))
  rw [show (fun z : Cube (ROf B) => P (blk3 z))
    = fun z => P (leftBlock (rightBlock (rightBlock z))) from rfl, h1, h2]
  exact prob_leftBlock P

theorem prob_blk4 (P : Cube (R4 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk4 z)] = Pr[P] := by
  have h1 := prob_rightBlock (a := R1 B)
    (fun w : Cube (Rest2 B) => P (leftBlock (rightBlock (rightBlock w))))
  have h2 := prob_rightBlock (a := R2 B)
    (fun w : Cube (Rest3 B) => P (leftBlock (rightBlock w)))
  have h3 := prob_rightBlock (a := R3 B) (fun w : Cube (Rest4 B) => P (leftBlock w))
  rw [show (fun z : Cube (ROf B) => P (blk4 z))
    = fun z => P (leftBlock (rightBlock (rightBlock (rightBlock z)))) from rfl, h1, h2, h3]
  exact prob_leftBlock P

theorem prob_blk5 (P : Cube (R5 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk5 z)] = Pr[P] := by
  have h1 := prob_rightBlock (a := R1 B)
    (fun w : Cube (Rest2 B) => P (leftBlock (rightBlock (rightBlock (rightBlock w)))))
  have h2 := prob_rightBlock (a := R2 B)
    (fun w : Cube (Rest3 B) => P (leftBlock (rightBlock (rightBlock w))))
  have h3 := prob_rightBlock (a := R3 B)
    (fun w : Cube (Rest4 B) => P (leftBlock (rightBlock w)))
  have h4 := prob_rightBlock (a := R4 B) (fun w : Cube (Rest5 B) => P (leftBlock w))
  rw [show (fun z : Cube (ROf B) => P (blk5 z))
    = fun z => P (leftBlock (rightBlock (rightBlock (rightBlock (rightBlock z))))) from rfl,
    h1, h2, h3, h4]
  exact prob_leftBlock P

theorem prob_blk6 (P : Cube (R5 B) → Prop) : Pr[fun z : Cube (ROf B) => P (blk6 z)] = Pr[P] := by
  have h1 := prob_rightBlock (a := R1 B)
    (fun w : Cube (Rest2 B) => P (rightBlock (rightBlock (rightBlock (rightBlock w)))))
  have h2 := prob_rightBlock (a := R2 B)
    (fun w : Cube (Rest3 B) => P (rightBlock (rightBlock (rightBlock w))))
  have h3 := prob_rightBlock (a := R3 B)
    (fun w : Cube (Rest4 B) => P (rightBlock (rightBlock w)))
  have h4 := prob_rightBlock (a := R4 B) (fun w : Cube (Rest5 B) => P (rightBlock w))
  rw [show (fun z : Cube (ROf B) => P (blk6 z))
    = fun z => P (rightBlock (rightBlock (rightBlock (rightBlock (rightBlock z))))) from rfl,
    h1, h2, h3, h4]
  exact prob_rightBlock P

/-! ### The checks -/

/-- The linearity check on a table, reading at the two halves of the block and
their sum. -/
def LinCheck {m : ℕ} (f : BooleanFunction m) (x : Cube (m + m)) : Prop :=
  f (leftBlock x) * f (rightBlock x) = f (leftBlock x + rightBlock x)

theorem prob_linCheck {m : ℕ} (f : BooleanFunction m) :
    Pr[LinCheck f] = blrAcceptProb f := by
  unfold blrAcceptProb
  rw [prob₂_eq_prob_blocks]
  rfl

/-- **The tester's verdict**: all six checks pass on the random string. -/
def AllChecks (S : Finset (Cube (kOf B))) (Tt Th : Cube B → ZMod 2)
    (F : Cube (nOf B) → ZMod 2) (G : Cube (nOf B * nOf B) → ZMod 2) (z : Cube (ROf B)) : Prop :=
  LinCheck (signOf F) (blk1 z)
    ∧ LinCheck (signOf G) (blk2 z)
    ∧ TesterAccepts (signOf F) (signOf G) (blk3 z)
    ∧ ConstraintAccepts (signOf F) (signOf G)
        (QuadConstraint.combine (oneHotSystem S) (leftBlock (blk4 z))) (rightBlock (blk4 z))
    ∧ CoordAccepts (signOf F) Tt (inTail B) (blk5 z)
    ∧ CoordAccepts (signOf F) Th (inHead B) (blk6 z)

theorem isBooleanValued_signOf {m : ℕ} (F : Cube m → ZMod 2) : IsBooleanValued (signOf F) := by
  intro x
  show chi (F x) = 1 ∨ chi (F x) = -1
  rcases (by decide : ∀ u : ZMod 2, u = 0 ∨ u = 1) (F x) with h | h <;> rw [h] <;> simp [chi]

/-! ### Soundness -/

/-- **Soundness of the assembled tester.** If the six checks all pass with
probability above `31/32`, the proof decodes to an assignment of the variables
that satisfies the one-hot system and whose two input parts are within `3/32`
of the input tables. -/
theorem sound (S : Finset (Cube (kOf B))) (Tt Th : Cube B → ZMod 2)
    (F : Cube (nOf B) → ZMod 2) (G : Cube (nOf B * nOf B) → ZMod 2)
    (h : 1 - 1 / 32 < Pr[AllChecks S Tt Th F G]) :
    ∃ a : Cube (nOf B), (∀ j, (oneHotSystem S j).Sat a)
      ∧ bitDist Tt (tailPart a) ≤ 3 / 32 ∧ bitDist Th (headPart a) ≤ 3 / 32 := by
  classical
  have hf := isBooleanValued_signOf F
  have hg := isBooleanValued_signOf G
  -- each check passes with probability above 31/32
  have h1 : 1 - 1 / 32 < Pr[LinCheck (signOf F)] := by
    rw [← prob_blk1 (LinCheck (signOf F))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.1)
  have h2 : 1 - 1 / 32 < Pr[LinCheck (signOf G)] := by
    rw [← prob_blk2 (LinCheck (signOf G))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.2.1)
  have h3 : 1 - 1 / 32 < Pr[TesterAccepts (signOf F) (signOf G)] := by
    rw [← prob_blk3 (TesterAccepts (signOf F) (signOf G))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.2.2.1)
  have h4 : 1 - 1 / 32 < Pr[fun x : Cube (R4 B) => ConstraintAccepts (signOf F) (signOf G)
      (QuadConstraint.combine (oneHotSystem S) (leftBlock x)) (rightBlock x)] := by
    rw [← prob_blk4 (fun x : Cube (R4 B) => ConstraintAccepts (signOf F) (signOf G)
      (QuadConstraint.combine (oneHotSystem S) (leftBlock x)) (rightBlock x))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.2.2.2.1)
  have h5 : 1 - 1 / 32 < Pr[CoordAccepts (signOf F) Tt (inTail B)] := by
    rw [← prob_blk5 (CoordAccepts (signOf F) Tt (inTail B))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.2.2.2.2.1)
  have h6 : 1 - 1 / 32 < Pr[CoordAccepts (signOf F) Th (inHead B)] := by
    rw [← prob_blk6 (CoordAccepts (signOf F) Th (inHead B))]
    exact lt_of_lt_of_le h (prob_mono fun z hz => hz.2.2.2.2.2)
  -- decode
  rw [prob_linCheck] at h1 h2
  obtain ⟨a, ha⟩ := exists_assignment_of_blr (signOf F) hf (1 / 32) (le_of_lt h1)
  obtain ⟨b, hb⟩ := exists_assignment_of_blr (signOf G) hg (1 / 32) (le_of_lt h2)
  have hfc : IsClose (signOf F) (signOf (hadamard a)) (1 / 32) := ha
  have hgc : IsClose (signOf G) (signOf (hadamard b)) (1 / 32) := hb
  have hb' : b = tensorAssign a :=
    eq_tensorAssign_of_prob_tester a b (signOf F) hf hfc (signOf G) hg hgc (by linarith)
  have hsys := forall_checkValue_of_prob_combined a b (oneHotSystem S) (signOf F) hf hfc
    (signOf G) hg hgc (by linarith)
  refine ⟨a, fun j => ?_, ?_, ?_⟩
  · have := hsys j
    rw [hb'] at this
    exact this
  · have hc := prob_coord_eq_ge a (signOf F) hf hfc Tt (inTail B)
    rw [bitDist_comm, bitDist_eq_one_sub]
    show 1 - Pr[fun r : Cube B => a (inTail B r) = Tt r] ≤ 3 / 32
    linarith
  · have hc := prob_coord_eq_ge a (signOf F) hf hfc Th (inHead B)
    rw [bitDist_comm, bitDist_eq_one_sub]
    show 1 - Pr[fun r : Cube B => a (inHead B r) = Th r] ≤ 3 / 32
    linarith

/-! ### Completeness -/

theorem linCheck_hadamard {m : ℕ} (a : Cube m) (x : Cube (m + m)) :
    LinCheck (signOf (hadamard a)) x := by
  show chi (hadamard a (leftBlock x)) * chi (hadamard a (rightBlock x))
    = chi (hadamard a (leftBlock x + rightBlock x))
  rw [hadamard_add_arg, BooleanAnalysis.Internal.chi_add]

/-- The honest tables pass the constraint check on every random string. -/
theorem constraintAccepts_of_honest {m : ℕ} (a : Cube m) (C : QuadConstraint m) (hC : C.Sat a)
    (z : Cube (m + m * m)) :
    ConstraintAccepts (signOf (hadamard a)) (signOf (hadamard (tensorAssign a))) C z := by
  show signBit (signOf (hadamard (tensorAssign a)) (rightBlock z)
      * signOf (hadamard (tensorAssign a)) (C.quad + rightBlock z))
    + signBit (signOf (hadamard a) (leftBlock z) * signOf (hadamard a) (C.lin + leftBlock z))
    + C.const = 0
  rw [corrected_read_honest, corrected_read_honest, signBit_chi, signBit_chi]
  exact hC

/-- **Completeness of the assembled tester.** The honest proof of an assignment
satisfying the system — its Hadamard encoding and that of its tensor square,
with the input tables read off the assignment — passes every check on every
random string. -/
theorem complete (S : Finset (Cube (kOf B))) (a : Cube (nOf B))
    (ha : ∀ j, (oneHotSystem S j).Sat a) (z : Cube (ROf B)) :
    AllChecks S (tailPart a) (headPart a) (hadamard a) (hadamard (tensorAssign a)) z :=
  ⟨linCheck_hadamard a _, linCheck_hadamard (tensorAssign a) _, testerAccepts_of_honest a _,
    constraintAccepts_of_honest a _ (QuadConstraint.sat_combine (oneHotSystem S) a ha _) _,
    coordAccepts_of_honest a (inTail B) _, coordAccepts_of_honest a (inHead B) _⟩

end Tester

end Complexity
