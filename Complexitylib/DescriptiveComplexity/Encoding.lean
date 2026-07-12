/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.DescriptiveComplexity.Structure
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Encoding finite structures as bit strings

To connect descriptive complexity to the machine model, a finite structure must be
presented as an input to a Turing machine — a bit string. The standard encoding
(for an *ordered* universe `Fin card`) lists, for each relation, its **truth
table**: the values over all tuples in the canonical order. This module builds the
relational part of that encoding and computes its length; it is step 5 (structure
→ bit-string encoding) of the Fagin decomposition on roadmap track L6.

## Main definitions and results

- `DescriptiveComplexity.encodeRel`, `encodeRel_length` — a relation's truth table
  (length `card ^ arity`).
- `DescriptiveComplexity.encodeRels`, `encodeRels_length` — the relational part of
  a structure's encoding, and its total length.
-/

namespace Complexity

namespace DescriptiveComplexity

/-- Encode a `Bool`-valued arity-`k` relation on `Fin card` as its **truth table**:
    the list of its values over all `k`-tuples, in the canonical `Fintype` order. -/
noncomputable def encodeRel {card k : Nat} (r : (Fin k → Fin card) → Bool) : List Bool :=
  (Finset.univ : Finset (Fin k → Fin card)).toList.map r

/-- The truth-table encoding of an arity-`k` relation has length `card ^ k`. -/
theorem encodeRel_length {card k : Nat} (r : (Fin k → Fin card) → Bool) :
    (encodeRel r).length = card ^ k := by
  simp only [encodeRel, List.length_map, Finset.length_toList, Finset.card_univ]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The relational part of a decidable structure's encoding: the truth tables of
    all its relations, concatenated. -/
noncomputable def encodeRels {V : Vocabulary} (A : DecFinStruct V) : List Bool :=
  (List.finRange V.numRels).flatMap (fun i => encodeRel (A.rel i))

/-- The relational encoding's length is the sum of the per-relation truth-table
    sizes `card ^ (arity)`. -/
theorem encodeRels_length {V : Vocabulary} (A : DecFinStruct V) :
    (encodeRels A).length
      = ((List.finRange V.numRels).map (fun i => A.card ^ V.relArity i)).sum := by
  simp only [encodeRels, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro i _
  exact encodeRel_length (A.rel i)

end DescriptiveComplexity

end Complexity
