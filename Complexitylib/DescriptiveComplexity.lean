/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.DescriptiveComplexity.Vocabulary
import Complexitylib.DescriptiveComplexity.Structure
import Complexitylib.DescriptiveComplexity.Isomorphism
import Complexitylib.DescriptiveComplexity.Query
import Complexitylib.DescriptiveComplexity.Env
import Complexitylib.DescriptiveComplexity.FirstOrder
import Complexitylib.DescriptiveComplexity.SecondOrder
import Complexitylib.DescriptiveComplexity.Definable
import Complexitylib.DescriptiveComplexity.Encoding
import Complexitylib.DescriptiveComplexity.Examples

/-!
# Descriptive complexity

Foundations of descriptive complexity (after Immerman), imported from the
`descriptive-complexity` project and grown inside this corpus: vocabularies
(signatures), finite structures, isomorphisms/embeddings/substructures,
first-order logic (syntax, semantics, isomorphism-invariance), Boolean queries
and order-independence, and worked examples.

The headline foundational result is `DescriptiveComplexity.Sentence.orderIndependent`
(Immerman Proposition 1.16): first-order sentences define order-independent
queries. This is the substrate for the logic-vs-complexity correspondences
(Fagin's theorem `NP = ∃SO`, `FO ⊆ AC⁰`, etc.) on roadmap track L (descriptive
complexity).
-/
