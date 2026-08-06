/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.P.PairWithInput

/-!
# The multi-arity bridge — proof internals

`FP` is defined for unary functions only, but Cobham's algebra is inherently
multi-arity. `Cobham.encodeVec` packs an argument vector into one bitstring by
nested pairing and `Cobham.FPn` says a multi-arity function is polynomial-time
*on encoded vectors*; at arity one the encoding is `pair [] x`, so `FPn`
collapses to `FP`.

## Main definitions

- `Cobham.encodeVec` — nested-pairing tuple encoding, head component last
- `Cobham.FPn` — polynomial time on encoded argument vectors
- `Cobham.const_nil_mem_FP`, `Cobham.pairLeftNil_mem_FP` — the two `FP` maps the
  arity-one glue needs
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-! ## Tuple encoding and the multi-arity FP predicate -/

/-- Encode an argument vector as a single bitstring by nested pairing, with the
head component placed in the verbatim suffix:
`encodeVec ![] = []` and `encodeVec (x ::ᵥ v) = pair (encodeVec v) x`.

Putting the head last (as the `pair` suffix) is what makes the arity-one encoding
`pair [] x`, so the soundness glue only needs `pairLeftNil_mem_FP`, which follows
from the existing `mem_FP_pairWithInput`. Because `pair` is injective with a
verbatim suffix, `encodeVec` is injective and its length is linear in the total
length of the components — exactly what the polynomial-time bookkeeping of `FPn`
needs. -/
def encodeVec : {n : ℕ} → (Fin n → List Bool) → List Bool
  | 0, _ => []
  | _ + 1, v => pair (encodeVec (Fin.tail v)) (v 0)

@[simp] theorem encodeVec_zero (v : Fin 0 → List Bool) : encodeVec v = [] := rfl

@[simp] theorem encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    encodeVec v = pair (encodeVec (Fin.tail v)) (v 0) := rfl

/-- The arity-one encoding is the single component placed in the (verbatim)
suffix of an empty block: `encodeVec ![x] = pair [] x`. -/
theorem encodeVec_one (v : Fin 1 → List Bool) : encodeVec v = pair [] (v 0) := by
  simp [encodeVec]

/-- **Multi-arity polynomial time.** A function of an argument vector is `FPn`
when some genuine (unary) `FP` function computes it on encoded vectors. This is
the induction motive for `cobham_imp_FPn`; specialized to arity one it collapses
to `FP` (see `CobhamFP_subset_FP_of_FPn`). -/
def FPn {n : ℕ} (f : (Fin n → List Bool) → List Bool) : Prop :=
  ∃ g, g ∈ FP ∧ ∀ v, g (encodeVec v) = f v

/-! ## Foundational FP building blocks -/

/-- The constant empty-output function is in `FP` (the empty-support case of
`ite_mem_finset_mem_FP`). -/
theorem const_nil_mem_FP : (fun _ : List Bool => ([] : List Bool)) ∈ FP := by
  have h := ite_mem_finset_mem_FP (fun _ => []) (∅ : Finset (List Bool))
  simpa using h

/-- The framing map `x ↦ pair [] x` (i.e. `false :: true :: x`) is
polynomial-time. This is the foundational map behind the arity-one encoding
`encodeVec ![x] = pair [] x`, and it is exactly `mem_FP_pairWithInput` applied to
the constant empty function. -/
theorem pairLeftNil_mem_FP : (fun x : List Bool => pair [] x) ∈ FP := by
  have h := mem_FP_pairWithInput const_nil_mem_FP
  simpa using h

end Cobham

end Complexity
