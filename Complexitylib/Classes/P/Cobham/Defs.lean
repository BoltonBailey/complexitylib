/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.Basic

/-!
# Cobham's characterization of FP — definitions

This file defines Cobham's machine-independent characterization of the polynomial-time
computable functions on bitstrings (Cobham, *The intrinsic computational difficulty of
functions*, 1965): the smallest class of functions `(Fin n → List Bool) → List Bool`
containing the projections, the empty string, the two bit successors, and the smash
function, and closed under composition and **limited recursion on notation**.

Bitstrings are LSB-first: in the recursion on notation, the head of the list is the
least-significant (innermost) bit, so the bit successors *prepend* a bit
(`x ↦ b :: x`, the string analogue of `n ↦ 2·n + bit`), and recursion on notation
peels bits off the head.

The functions are multi-arity (indexed by `Fin n` argument vectors) because limited
recursion on notation inherently produces functions of higher arity; the unary fragment
is collected in `CobhamFP`, which `Complexitylib.Classes.P.Cobham` proves equal to the
machine class `FP`.

## Main definitions

- `Complexity.smash` — Cobham's smash function: a string of length `|x| · |y|`
- `Complexity.caseBit`, `Complexity.caseBit₀` — partial and total dispatch on the
  leading bit of a string
- `Complexity.andBit`, `Complexity.orBit`, `Complexity.notBit` — flag connectives
- `Complexity.bitAt` — the bit of a string at a ruler-marked position
- `Complexity.matchPrefix` — flag testing a string against a fixed constant
- `Complexity.recNotation` — the recursion-on-notation combinator
- `Complexity.Cobham` — the inductive predicate carving out Cobham's function algebra
- `Complexity.CobhamFP` — the unary fragment, as a set of string functions

## Design notes

The bound in `Cobham.boundedRec` follows Cobham's original formulation: the recursively
defined function must be *length-bounded by another function of the class* (rather than
by an external polynomial). Together with `smash` and the successors this realizes
exactly the polynomial length bounds, which is what makes the class no larger than `FP`;
dropping the bound would admit iterated doubling and hence exponential growth.
-/


@[expose] public section

namespace Complexity

/-- **Cobham's smash function** on bitstrings: a canonical string of length
`|x| · |y|`. This is the length-arithmetic engine of the class: composing `smash` with
the bit successors and projections realizes every polynomial length bound, which is
what lets `Cobham.boundedRec` bound recursions by a function of the class itself.

(Cobham's original smash is `x # y = 2^(|x|·|y|)`; over bitstrings we keep only the
length, which is all the class ever uses.) -/
def smash (x y : List Bool) : List Bool :=
  List.replicate (x.length * y.length) false

@[simp] theorem smash_length (x y : List Bool) :
    (smash x y).length = x.length * y.length := by
  simp [smash]

/-- **Bit dispatch**: select `x` or `y` according to the leading bit of `s`,
returning the empty string when `s` is empty.

This is the branching primitive of the algebra. It is definable by a single
limited recursion on notation (`Cobham.caseBit`) because the step functions of
`recNotation` are already selected by the bit being peeled — dispatching on a bit
costs nothing beyond the recursion that is there anyway. -/
def caseBit (s x y : List Bool) : List Bool :=
  match s with
  | [] => []
  | b :: _ => bif b then x else y

@[simp] theorem caseBit_nil (x y : List Bool) : caseBit [] x y = [] := rfl

@[simp] theorem caseBit_cons (b : Bool) (s x y : List Bool) :
    caseBit (b :: s) x y = bif b then x else y := rfl

/-- Bit dispatch never returns more than its two branches together. -/
theorem caseBit_length_le (s x y : List Bool) :
    (caseBit s x y).length ≤ (x ++ y).length := by
  cases s with
  | nil => simp
  | cons b s => cases b <;> simp

/-- **Total bit dispatch**: like `caseBit`, but the empty string selects the
`false` branch instead of returning nothing.

Both variants are needed. `caseBit` is the *partial* reader used when running off
the end of a string must produce nothing (`Cobham.takePrefix` reads bits this
way); `caseBit₀` is the *total* one used for Boolean logic, where "no bit" has to
mean `false` so that flags are always exactly `[true]` or `[false]`. -/
def caseBit₀ (s x y : List Bool) : List Bool :=
  match s with
  | [] => y
  | b :: _ => bif b then x else y

@[simp] theorem caseBit₀_nil (x y : List Bool) : caseBit₀ [] x y = y := rfl

@[simp] theorem caseBit₀_cons (b : Bool) (s x y : List Bool) :
    caseBit₀ (b :: s) x y = bif b then x else y := rfl

/-- Total bit dispatch never returns more than its two branches together. -/
theorem caseBit₀_length_le (s x y : List Bool) :
    (caseBit₀ s x y).length ≤ (x ++ y).length := by
  cases s with
  | nil => simp
  | cons b s => cases b <;> simp

/-! ### Flags

A *flag* is a one-bit string, `[true]` or `[false]`. The connectives below are
each one `caseBit₀`, so they are in the algebra as soon as `caseBit₀` is, and
they are how the finite case analysis of a machine's transition function gets
written inside it. Because they are built on the *total* dispatcher, every flag
these produce is genuinely one bit — never empty — so they compose. -/

/-- Conjunction of flags. -/
def andBit (x y : List Bool) : List Bool :=
  caseBit₀ x (caseBit₀ y [true] [false]) [false]

/-- Disjunction of flags. -/
def orBit (x y : List Bool) : List Bool :=
  caseBit₀ x [true] (caseBit₀ y [true] [false])

/-- Negation of a flag. -/
def notBit (x : List Bool) : List Bool := caseBit₀ x [false] [true]

/-- The bit of `x` at the position marked by the ruler `r`, as a flag; `false`
when the position is past the end of `x`. -/
def bitAt (r x : List Bool) : List Bool :=
  caseBit₀ (x.drop r.length) [true] [false]

@[simp] theorem bitAt_nil_left (x : List Bool) :
    bitAt [] x = caseBit₀ x [true] [false] := by simp [bitAt]

/-- A flag is exactly one bit long. -/
theorem bitAt_length (r x : List Bool) : (bitAt r x).length = 1 := by
  rw [bitAt]
  rcases hx : x.drop r.length with _ | ⟨b, z⟩
  · simp
  · cases b <;> simp

/-- Pad (or truncate) `x` to exactly the width of the ruler `r`, filling with
zeros.

Fixed-width blocks are how a simulated machine's configuration is packed into the
single string a member of the class returns: every field occupies `|r|` bits, so
field `i` is recovered by dropping `i` rulers and taking one — no self-delimiting
decoder is needed inside the algebra. -/
def padTo (r x : List Bool) : List Bool :=
  (x ++ List.replicate r.length false).take r.length

/-- A padded block always has exactly the ruler's width. -/
@[simp] theorem padTo_length (r x : List Bool) : (padTo r x).length = r.length := by
  rw [padTo, List.length_take, List.length_append, List.length_replicate]
  omega

/-- Padding a short string appends zeros. -/
theorem padTo_eq_append (r x : List Bool) (h : x.length ≤ r.length) :
    padTo r x = x ++ List.replicate (r.length - x.length) false := by
  rw [padTo]
  simp [List.take_append, List.take_replicate, List.take_of_length_le h]

/-- The `i`-th block of `x`, when `x` is a concatenation of blocks each as wide
as the ruler `r`. -/
def blockAt (r x : List Bool) (i : ℕ) : List Bool :=
  (x.drop (i * r.length)).take r.length

/-- Block zero of a block-aligned string is its first block. -/
@[simp] theorem blockAt_zero_append (r a x : List Bool) (h : a.length = r.length) :
    blockAt r (a ++ x) 0 = a := by
  rw [blockAt, Nat.zero_mul, List.drop_zero, ← h, List.take_left]

/-- Later blocks of a block-aligned string are the blocks of its tail. -/
theorem blockAt_succ_append (r a x : List Bool) (h : a.length = r.length) (i : ℕ) :
    blockAt r (a ++ x) (i + 1) = blockAt r x i := by
  have hd : (a ++ x).drop (i * a.length + a.length) = x.drop (i * a.length) := by
    rw [Nat.add_comm]
    simp
  rw [blockAt, blockAt, Nat.succ_mul, ← h, hd]

/-! ### Padding algebra

A simulated step reads a padded block, edits it, and re-pads. These three lemmas
say that the padding is invisible to that: re-padding commutes with the edits, so
the encoded step can be reasoned about on raw contents. -/

/-- Extra zero padding is invisible to `padTo`. -/
theorem padTo_append_replicate (r z : List Bool) (m : ℕ) :
    padTo r (z ++ List.replicate m false) = padTo r z := by
  rw [padTo, padTo, List.append_assoc, ← List.replicate_add, List.take_append,
    List.take_append, List.take_replicate, List.take_replicate]
  congr 2
  omega

/-- Re-padding a padded block is the same as padding its raw content. -/
theorem padTo_append_padTo (r y x : List Bool) (hx : x.length ≤ r.length) :
    padTo r (y ++ padTo r x) = padTo r (y ++ x) := by
  rw [padTo_eq_append r x hx, ← List.append_assoc, padTo_append_replicate]

/-- Taking from within the content of a padded block ignores the padding. -/
theorem take_padTo (r x : List Bool) (n : ℕ) (hn : n ≤ x.length)
    (hx : x.length ≤ r.length) :
    (padTo r x).take n = x.take n := by
  rw [padTo, List.take_take, Nat.min_eq_left (by omega : n ≤ r.length),
    List.take_append, Nat.sub_eq_zero_of_le hn, List.take_zero, List.append_nil]

/-- Dropping from a padded block leaves the padding trailing at the end. -/
theorem drop_padTo (r x : List Bool) (n : ℕ) (hn : n ≤ x.length)
    (hx : x.length ≤ r.length) :
    (padTo r x).drop n = x.drop n ++ List.replicate (r.length - x.length) false := by
  rw [padTo_eq_append r x hx, List.drop_append, Nat.sub_eq_zero_of_le hn,
    List.drop_zero]

/-- Dropping from a padded block and re-padding ignores the padding. -/
theorem padTo_drop (r x : List Bool) (n : ℕ) (hn : n ≤ x.length)
    (hx : x.length ≤ r.length) :
    padTo r ((padTo r x).drop n) = padTo r (x.drop n) := by
  rw [padTo_eq_append r x hx, List.drop_append, Nat.sub_eq_zero_of_le hn,
    List.drop_zero, padTo_append_replicate]

/-- **Reading a field out of a block-aligned record.** When `bs` is a list of
blocks all as wide as the ruler `r`, block `i` of their concatenation is `bs[i]`.
This is what makes `Cobham.blockFn` a field accessor. -/
theorem blockAt_flatten (r : List Bool) :
    ∀ (bs : List (List Bool)), (∀ b ∈ bs, b.length = r.length) →
      ∀ (i : ℕ) (hi : i < bs.length), blockAt r bs.flatten i = bs[i] := by
  intro bs
  induction bs with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
      intro hb i hi
      cases i with
      | zero =>
          rw [List.flatten_cons]
          exact blockAt_zero_append r b _ (hb b (by simp))
      | succ i =>
          rw [List.flatten_cons, blockAt_succ_append _ _ _ (hb b (by simp))]
          rw [ih (fun c hc => hb c (by simp [hc])) i (by simpa using hi)]
          simp

/-- Flag: is `x` nonempty? The *partial* dispatcher returns `[]` on the empty
string, and `[]` reads as false to the flag connectives — so this is the one
place `caseBit` rather than `caseBit₀` is what is wanted.

Without it `matchPrefix` could not tell "the head bit is `0`" from "there is no
head bit", and would report a match of `[0]` against `[]`. -/
def nonemptyFlag (x : List Bool) : List Bool := caseBit x [true] [true]

@[simp] theorem nonemptyFlag_nil : nonemptyFlag [] = [] := rfl

@[simp] theorem nonemptyFlag_cons (b : Bool) (x : List Bool) :
    nonemptyFlag (b :: x) = [true] := by cases b <;> rfl

/-- Flag: does `x` begin with the fixed constant `c`? Unfolds into `|c|` bit
tests joined by `andBit`, so for each constant it is a *finite* composition —
no recursion on notation is needed. -/
def matchPrefix : List Bool → List Bool → List Bool
  | [], _ => [true]
  | b :: c, x =>
      andBit (nonemptyFlag x)
        (andBit (bif b then bitAt [] x else notBit (bitAt [] x))
          (matchPrefix c x.tail))

@[simp] theorem matchPrefix_nil (x : List Bool) : matchPrefix [] x = [true] := rfl

@[simp] theorem matchPrefix_cons (b : Bool) (c x : List Bool) :
    matchPrefix (b :: c) x =
      andBit (nonemptyFlag x)
        (andBit (bif b then bitAt [] x else notBit (bitAt [] x))
          (matchPrefix c x.tail)) := rfl

/-- A constant is matched by anything it prefixes. -/
theorem matchPrefix_append (c y : List Bool) : matchPrefix c (c ++ y) = [true] := by
  induction c generalizing y with
  | nil => rfl
  | cons b c ih => cases b <;> simp [andBit, notBit, ih]

/-- Nothing but the empty constant matches the empty string. (Not a `simp`
lemma: `simp` unfolds the left-hand side past this shape.) -/
theorem matchPrefix_nil_right (b : Bool) (c : List Bool) :
    matchPrefix (b :: c) [] = [false] := by
  cases b <;> rfl

/-- Conjunction always returns a genuine one-bit flag, whatever it is given. -/
theorem andBit_flag (x y : List Bool) :
    andBit x y = [true] ∨ andBit x y = [false] := by
  rw [andBit]
  cases x with
  | nil => exact Or.inr rfl
  | cons a x =>
      cases a
      · exact Or.inr rfl
      · rw [caseBit₀_cons, cond_true]
        cases y with
        | nil => exact Or.inr rfl
        | cons d y => cases d <;> simp

/-- The match test always returns a genuine one-bit flag. -/
theorem matchPrefix_flag (c x : List Bool) :
    matchPrefix c x = [true] ∨ matchPrefix c x = [false] := by
  cases c with
  | nil => exact Or.inl rfl
  | cons b c => rw [matchPrefix_cons]; exact andBit_flag _ _

/-- **The match test is exactly the prefix test.** This is what makes a table of
constant patterns behave like a case analysis: the entry whose pattern is a
prefix of the key fires, and no other does. -/
theorem matchPrefix_eq_true_iff (c x : List Bool) :
    matchPrefix c x = [true] ↔ c <+: x := by
  induction c generalizing x with
  | nil => simp
  | cons b c ih =>
      cases x with
      | nil => simp [andBit]
      | cons a x =>
          rw [matchPrefix_cons, nonemptyFlag_cons, andBit, caseBit₀_cons, cond_true,
            andBit]
          have hbit : (bif b then bitAt [] (a :: x) else notBit (bitAt [] (a :: x)))
              = [decide (a = b)] := by
            cases a <;> cases b <;> rfl
          rw [hbit, List.cons_prefix_cons]
          rcases matchPrefix_flag c x with h | h <;> cases a <;> cases b <;>
            simp [h, ← ih x]

/-- **Recursion on notation**: the string analogue of primitive recursion, recursing on
the bit structure of the first argument.

`recNotation g h₀ h₁ x v` computes `g v` when `x` is empty, and on `b :: x` applies the
step function selected by the bit `b` to the argument vector consisting of the tail
`x`, the recursive value on the tail, and the parameters `v`. -/
def recNotation {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) :
    List Bool → (Fin n → List Bool) → List Bool
  | [], v => g v
  | b :: x, v =>
      (bif b then h₁ else h₀) (Fin.cons x (Fin.cons (recNotation g h₀ h₁ x v) v))

@[simp] theorem recNotation_nil {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (v : Fin n → List Bool) :
    recNotation g h₀ h₁ [] v = g v := rfl

@[simp] theorem recNotation_cons {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (b : Bool) (x : List Bool)
    (v : Fin n → List Bool) :
    recNotation g h₀ h₁ (b :: x) v =
      (bif b then h₁ else h₀) (Fin.cons x (Fin.cons (recNotation g h₀ h₁ x v) v)) := rfl

/-- **Cobham's function algebra**: the smallest class of bitstring functions containing
the projections, the empty string, the bit successors `x ↦ b :: x`, and `smash`, and
closed under composition and limited recursion on notation.

In `boundedRec`, the recursion is *limited*: the result must be length-bounded,
uniformly in the arguments, by a function `j` already in the class. This is the
polynomial-growth leash that pins the class to exactly `FP`
(see `Complexitylib.Classes.P.Cobham`). -/
inductive Cobham : ∀ {n : ℕ}, ((Fin n → List Bool) → List Bool) → Prop
  /-- Every projection is in the class. -/
  | proj {n : ℕ} (i : Fin n) : Cobham fun v => v i
  /-- The empty-string constant (at every arity) is in the class. -/
  | empty {n : ℕ} : Cobham fun _ : Fin n → List Bool => []
  /-- The bit successors `x ↦ b :: x` (the string analogue of `n ↦ 2·n + b`) are in
  the class. -/
  | bit (b : Bool) : Cobham fun v : Fin 1 → List Bool => b :: v 0
  /-- The smash function is in the class. -/
  | smash : Cobham fun v : Fin 2 → List Bool => smash (v 0) (v 1)
  /-- The class is closed under composition. -/
  | comp {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
      {gs : Fin m → (Fin n → List Bool) → List Bool} :
      Cobham f → (∀ i, Cobham (gs i)) → Cobham fun v => f fun i => gs i v
  /-- The class is closed under **limited recursion on notation**: recursion on the bit
  structure of the first argument, provided the result is length-bounded by a function
  `j` of the class. -/
  | boundedRec {n : ℕ} {g : (Fin n → List Bool) → List Bool}
      {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
      {j : (Fin (n + 1) → List Bool) → List Bool} :
      Cobham g → Cobham h₀ → Cobham h₁ → Cobham j →
      (∀ x v, (recNotation g h₀ h₁ x v).length ≤ (j (Fin.cons x v)).length) →
      Cobham fun v : Fin (n + 1) → List Bool => recNotation g h₀ h₁ (v 0) (Fin.tail v)

/-- The unary fragment of Cobham's function algebra, as a class of string functions.
`Complexitylib.Classes.P.Cobham` proves `CobhamFP = FP`: this machine-independent
algebra carves out exactly the polynomial-time computable functions. -/
def CobhamFP : Set (List Bool → List Bool) :=
  {f | Cobham fun v : Fin 1 → List Bool => f (v 0)}

end Complexity
