import Complexitylib.Models.TuringMachine.Encoding

/-!
# Fixed-width binary roundtrips

`Nat.fromBits_toBits` (in `Encoding.lean`) inverts one way; here we prove
the other direction — `Nat.toBits` recovers any bit list of the right width
from its value — and the resulting injectivity of `Nat.fromBits` on
fixed-width lists. The universal machine compares state fields symbol-wise
while the abstract table lookup compares their decoded numbers; these
lemmas make the two agree.
-/

/-- Adding multiples of `2^w` does not change the low `w` bits. -/
theorem Nat.toBits_add_pow_mul : ∀ (w val c : ℕ),
    Nat.toBits w (val + c * 2 ^ w) = Nat.toBits w val
  | 0, _, _ => rfl
  | w + 1, val, c => by
    have hrw : val + c * 2 ^ (w + 1) = val + c * 2 * 2 ^ w := by
      rw [pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc]
    have hdiv : (val + c * 2 * 2 ^ w) / 2 ^ w = val / 2 ^ w + c * 2 :=
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos w)
    simp only [hrw, Nat.toBits, hdiv, List.cons.injEq]
    constructor
    · rw [Nat.add_mul_mod_self_right]
    · exact Nat.toBits_add_pow_mul w val (c * 2)

/-- `Nat.toBits` is a left inverse of `Nat.fromBits` at the list's width. -/
theorem Nat.toBits_fromBits : ∀ l : List Bool, Nat.toBits l.length (Nat.fromBits l) = l
  | [] => rfl
  | b :: rest => by
    have hlt := Nat.fromBits_lt_pow_length rest
    have hval : Nat.fromBits (b :: rest)
        = Nat.fromBits rest + (if b then 1 else 0) * 2 ^ rest.length := by
      simp only [Nat.fromBits]
      exact Nat.add_comm _ _
    simp only [Nat.toBits, List.cons.injEq]
    constructor
    · rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
      cases b <;> simp
    · rw [hval, Nat.toBits_add_pow_mul, Nat.toBits_fromBits rest]

/-- `Nat.fromBits` is injective on lists of equal width. -/
theorem Nat.fromBits_inj_of_length_eq {a b : List Bool} (hlen : a.length = b.length)
    (h : Nat.fromBits a = Nat.fromBits b) : a = b := by
  have ha := Nat.toBits_fromBits a
  rw [h, hlen] at ha
  rw [← ha, Nat.toBits_fromBits b]
