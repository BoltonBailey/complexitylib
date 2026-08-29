/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.HadamardTester

/-!
# The tester reads its input

An *assignment tester* is not a stand-alone proof system: it is given an input
assignment — in Dinur's composition, the bits the outer constraint graph has
already committed to at the two endpoints of an edge — and must reject unless
those very bits extend to a satisfying assignment. A tester that merely
certifies *some* satisfying assignment exists is useless there, because the
outer graph's assignment would be free to disagree with it.

So the tester needs one more check: that the assignment `a` decoded from its
proof agrees, on the input coordinates, with the input `w` it is handed. The
check is the natural one — pick a random subset of the input coordinates, add up
those bits of `w` directly (the input is a constant number of bits, so this
costs nothing), and compare with the same subset-sum read off the proof by
self-correction.

Soundness is the same rigidity argument that runs throughout the Hadamard
analysis: two assignments whose subset-sums agree on more than half of the
subsets are equal, because their difference would otherwise be a nonzero vector,
and a nonzero vector's subset-sums are odd exactly half the time
(`prob_hadamard_ne_zero`).

## Main definitions

- `Complexity.embedInput` — an input string as a point of the full cube
- `Complexity.InputAccepts` — the input-consistency check on the raw table

## Main results

- `Complexity.eq_of_prob_hadamard_eq` — rigidity: agreeing on more than half
  the subset-sums forces equality
- `Complexity.eq_input_of_prob_inputAccepts` — **the tester verifies its
  input**: passing the check often enough forces the decoded assignment to
  agree with the input
- `Complexity.inputAccepts_of_honest` — and the honest proof always passes
- `Complexity.exists_sat_extending` — **the Hadamard code is an assignment
  tester**: all four checks passing forces the input to extend to a satisfying
  assignment
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {k t : ℕ}

/-! ### Reading the input coordinates -/

/-- An input string, viewed as a point of the full cube: the input coordinates
carry it and the auxiliary coordinates are zero. Reading a Hadamard table here
returns a subset-sum of the input coordinates alone. -/
def embedInput (r : Cube k) : Cube (k + t) := Fin.append r 0

/-- **Reading only the input coordinates.** A subset-sum of an assignment taken
at an embedded input string sees exactly the assignment's input part. -/
theorem hadamard_embedInput (a : Cube (k + t)) (r : Cube k) :
    hadamard a (embedInput r) = hadamard (leftBlock a) r := by
  show ∑ i : Fin (k + t), a i * (Fin.append r (0 : Cube t)) i
    = ∑ i : Fin k, a (Fin.castAdd t i) * r i
  rw [Fin.sum_univ_add]
  have hleft : ∀ i : Fin k,
      a (Fin.castAdd t i) * (Fin.append r (0 : Cube t)) (Fin.castAdd t i)
        = a (Fin.castAdd t i) * r i := fun i => by
    rw [Fin.append_left]
  have hright : ∀ j : Fin t,
      a (Fin.natAdd k j) * (Fin.append r (0 : Cube t)) (Fin.natAdd k j) = 0 := fun j => by
    rw [Fin.append_right]
    show a (Fin.natAdd k j) * (0 : ZMod 2) = 0
    ring
  rw [Finset.sum_congr rfl fun i _ => hleft i, Finset.sum_congr rfl fun j _ => hright j]
  simp

/-! ### Rigidity -/

/-- **Subset-sums determine an assignment.** If two assignments' subset-sums
agree on more than half of the subsets they are equal: otherwise their
difference is a nonzero vector, whose subset-sums are odd on exactly half. -/
theorem eq_of_prob_hadamard_eq {m : ℕ} (u v : Cube m)
    (h : 1 / 2 < Pr[fun r : Cube m => hadamard u r = hadamard v r]) : u = v := by
  classical
  by_contra hne
  have hsum : u + v ≠ 0 := by
    intro h0
    apply hne
    funext i
    have hi := congrFun h0 i
    show u i = v i
    rcases (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) (u i) (v i) hi with h'
    exact h'
  have hhalf := prob_hadamard_ne_zero (u + v) hsum
  have hfail : (fun r : Cube m => hadamard (u + v) r ≠ 0)
      = fun r : Cube m => ¬ (hadamard u r = hadamard v r) := by
    funext r
    rw [hadamard_add]
    have hiff : (hadamard u r + hadamard v r = 0) ↔ (hadamard u r = hadamard v r) := by
      rcases (by decide : ∀ x y : ZMod 2, (x + y = 0) ↔ (x = y)) (hadamard u r)
        (hadamard v r) with h'
      exact h'
    exact propext (not_congr hiff)
  rw [hfail] at hhalf
  have hcompl := BooleanAnalysis.Internal.prob_compl
    (fun r : Cube m => hadamard u r = hadamard v r)
  linarith

/-! ### The input-consistency check -/

/-- **The tester's input check**, made on the raw table: a random subset-sum of
the input, computed directly from the input bits, must equal the same subset-sum
read off the proof by self-correction. The first block picks the subset, the
second is the correction string. -/
def InputAccepts (f : BooleanFunction (k + t)) (w : Cube k)
    (z : Cube (k + (k + t))) : Prop :=
  signBit (f (rightBlock z) * f (embedInput (leftBlock z) + rightBlock z))
    = hadamard w (leftBlock z)

/-- Every read of the input check is right except with probability `2ε`. The
subset is chosen by the first block and the correction by the second, so
`prob_blocks_ge` fixes the read point before the correction is drawn. -/
theorem prob_input_reads (a : Cube (k + t)) (f : BooleanFunction (k + t))
    (hf : IsBooleanValued f) {ε : ℝ} (hfc : IsClose f (signOf (hadamard a)) ε) :
    1 - 2 * ε ≤ Pr[fun z : Cube (k + (k + t)) =>
      f (rightBlock z) * f (embedInput (leftBlock z) + rightBlock z)
        = chi (hadamard a (embedInput (leftBlock z)))] := by
  classical
  refine prob_blocks_ge (fun u c =>
    f c * f (embedInput u + c) = chi (hadamard a (embedInput u))) _ fun u => ?_
  exact prob_read_ge f hf a hfc (embedInput u)

/-- **The tester verifies its input.** If the input check passes on more than
half the randomness — with room for the reads' failure probability — then the
assignment decoded from the proof agrees with the input on every input
coordinate.

Together with `exists_sat_of_prob_tester` this is the assignment-tester
guarantee Dinur's composition consumes: the proof cannot certify a satisfying
assignment other than an extension of the bits the outer graph committed to. -/
theorem eq_input_of_prob_inputAccepts (a : Cube (k + t)) (w : Cube k)
    (f : BooleanFunction (k + t)) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (haccept : 1 / 2 + 2 * ε < Pr[InputAccepts f w]) :
    leftBlock a = w := by
  classical
  have hgood := prob_input_reads a f hf hfc
  have htrans := prob_le_of_imp_of_good (E := InputAccepts f w)
    (F := fun z : Cube (k + (k + t)) =>
      hadamard a (embedInput (leftBlock z)) = hadamard w (leftBlock z))
    (A := fun z : Cube (k + (k + t)) =>
      f (rightBlock z) * f (embedInput (leftBlock z) + rightBlock z)
        = chi (hadamard a (embedInput (leftBlock z))))
    fun z hE hA => by
      have hE' : signBit (chi (hadamard a (embedInput (leftBlock z))))
          = hadamard w (leftBlock z) := by
        rw [← hA]
        exact hE
      rwa [signBit_chi] at hE'
  have hblk : Pr[fun z : Cube (k + (k + t)) =>
      hadamard a (embedInput (leftBlock z)) = hadamard w (leftBlock z)]
      = Pr[fun r : Cube k => hadamard a (embedInput r) = hadamard w r] :=
    prob_leftBlock (fun r : Cube k => hadamard a (embedInput r) = hadamard w r)
  rw [hblk] at htrans
  have hrew : (fun r : Cube k => hadamard a (embedInput r) = hadamard w r)
      = fun r : Cube k => hadamard (leftBlock a) r = hadamard w r := by
    funext r
    rw [hadamard_embedInput]
  rw [hrew] at htrans
  exact eq_of_prob_hadamard_eq (leftBlock a) w (by linarith)

/-- **Completeness of the input check.** The honest proof for an assignment
extending the input passes on every random string. -/
theorem inputAccepts_of_honest (a : Cube (k + t)) (z : Cube (k + (k + t))) :
    InputAccepts (signOf (hadamard a)) (leftBlock a) z := by
  show signBit (signOf (hadamard a) (rightBlock z)
    * signOf (hadamard a) (embedInput (leftBlock z) + rightBlock z)) = _
  rw [corrected_read_honest, signBit_chi, hadamard_embedInput]

/-- The honest proof passes the input check with probability one. -/
theorem prob_inputAccepts_of_honest (a : Cube (k + t)) :
    Pr[InputAccepts (signOf (hadamard a)) (leftBlock a)] = 1 :=
  prob_of_forall (inputAccepts_of_honest a)

/-! ### The assignment tester -/

/-- **The Hadamard code is an assignment tester.** Given an input `w` and a
proof consisting of two tables, if all four checks — linearity of each table,
consistency of the quadratic table with the linear one, the constraint itself,
and agreement with the input — pass often enough, then the input extends to a
satisfying assignment of the constraint.

Nothing is assumed about the tables. This is the whole guarantee Dinur's
alphabet-reduction step asks of its inner verifier: completeness is
`prob_testerAccepts_of_honest` together with `prob_inputAccepts_of_honest`, and
the query count and proof length depend only on the constraint's size, not on
the outer system's. -/
theorem exists_sat_extending (C : QuadConstraint (k + t)) (w : Cube k)
    (f : BooleanFunction (k + t)) (hf : IsBooleanValued f)
    (g : BooleanFunction ((k + t) * (k + t))) (hg : IsBooleanValued g) {ε ε' : ℝ}
    (hblrf : blrAcceptProb f ≥ 1 - ε) (hblrg : blrAcceptProb g ≥ 1 - ε')
    (hcons : 3 / 4 + (4 * ε + 2 * ε') < Pr[TesterAccepts f g])
    (hchk : 2 * ε + 2 * ε' < Pr[ConstraintAccepts f g C])
    (hinp : 1 / 2 + 2 * ε < Pr[InputAccepts f w]) :
    ∃ a : Cube (k + t), C.Sat a ∧ leftBlock a = w := by
  classical
  obtain ⟨a, ha⟩ := exists_assignment_of_blr f hf ε hblrf
  obtain ⟨b, hb⟩ := exists_assignment_of_blr g hg ε' hblrg
  have hfc : IsClose f (signOf (hadamard a)) ε := ha
  have hgc : IsClose g (signOf (hadamard b)) ε' := hb
  exact ⟨a, sat_of_prob_tester a b C f hf hfc g hg hgc hcons
      (checkValue_eq_zero_of_prob a b C f hf hfc g hg hgc hchk),
    eq_input_of_prob_inputAccepts a w f hf hfc hinp⟩

end Complexity
