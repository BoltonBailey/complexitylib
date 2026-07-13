/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.SAT.Tseitin.Internal.EncodingBounds
import Complexitylib.SAT.Tseitin.Internal.Shape

/-!
# Size bounds for Tseitin splitting

The typed transformation is linear in source clauses and literal occurrences.
Because the concrete SAT codec writes variable indices in unary, newly allocated
indices make the honest bit-level bound quadratic in the source encoding length.
-/

namespace Complexity

namespace SAT

namespace CNF

/-- The transformation consumes at most twice as many fresh variables as there
are bits in the source encoding. -/
theorem tseitinFreshCount_le_two_mul_encode_length_internal (φ : CNF) :
    φ.tseitinFreshCount ≤ 2 * φ.encode.length := by
  have hfresh := tseitinFreshCount_le_literalCount_add_length_internal φ
  have hlit := literalCount_le_encode_length_internal φ
  have hclauses := length_le_encode_length_internal φ
  omega

/-- The transformed formula has at most three times as many clauses as source
encoding bits. -/
theorem length_to3_le_three_mul_encode_length_internal (φ : CNF) :
    φ.to3.length ≤ 3 * φ.encode.length := by
  have hout := length_to3Aux_le_internal (φ.maxVar + 1) φ
  have hlit := literalCount_le_encode_length_internal φ
  have hclauses := length_le_encode_length_internal φ
  exact le_trans hout (by omega)

/-- Every transformed variable index is at most three times the source
encoding length. -/
theorem var_le_three_mul_encode_length_of_mem_to3_internal (φ : CNF)
    {c : Clause} (hc : c ∈ φ.to3) {ℓ : Lit} (hℓ : ℓ ∈ c) :
    ℓ.var ≤ 3 * φ.encode.length := by
  have hvar := var_lt_of_mem_to3_internal φ hc hℓ
  have hmax := CNF.maxVar_le_encode_length φ
  have hfresh := tseitinFreshCount_le_two_mul_encode_length_internal φ
  omega

/-- **Concrete quadratic size bound.** Under the current unary-variable SAT
codec, the exact-3 output uses at most `96 * (|encode φ| + 1)^2` bits. -/
theorem encode_to3_length_le_internal (φ : CNF) :
    φ.to3.encode.length ≤ 96 * (φ.encode.length + 1) ^ 2 := by
  let n := φ.encode.length
  have h3 := to3_is3CNF_internal φ
  have hvars : ∀ c ∈ φ.to3, ∀ ℓ ∈ c, ℓ.var ≤ 3 * n := by
    intro c hc ℓ hℓ
    exact var_le_three_mul_encode_length_of_mem_to3_internal φ hc hℓ
  have hencoded := encode_length_le_of_is3CNF_internal h3 hvars
  have hclauses : φ.to3.length ≤ 3 * n := by
    exact length_to3_le_three_mul_encode_length_internal φ
  calc
    φ.to3.encode.length ≤ φ.to3.length * (6 * (3 * n) + 14) := hencoded
    _ ≤ (3 * n) * (6 * (3 * n) + 14) :=
      Nat.mul_le_mul_right (6 * (3 * n) + 14) hclauses
    _ ≤ 96 * (n + 1) ^ 2 := by nlinarith

end CNF

end SAT

end Complexity
