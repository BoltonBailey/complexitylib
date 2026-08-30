/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Compose
public import Complexitylib.Classes.PCP.Internal.AlphabetLift
public import Complexitylib.Classes.PCP.Internal.ThreeSATReduction

/-!
# The starting constraint graph, over the amplifier's alphabet

Dinur's round is an endomorphism of constraint graphs over the alphabet the
composition step produces, `MultiTest.Alpha ReadIdx`, while the reduction from
3-SAT lands in `Fin 3 → Bool`. The latter has eight symbols and the former
`2^23`, so the small alphabet embeds, and `AlphabetLift` carries the graph
across without disturbing satisfiability.

## Main definitions

- `Complexity.alphaEmb` — an injection of the 3-SAT alphabet into the
  amplifier's
- `Complexity.baseCSP` — the 3-SAT constraint graph, read over that alphabet

## Main results

- `Complexity.satisfiable_baseCSP_iff` — it is satisfiable exactly when the
  formula is
-/

@[expose] public section

namespace Complexity

open ThreeSATCSP SAT

/-- The alphabet Dinur's round runs over. -/
abbrev GapAlpha : Type := MultiTest.Alpha ReadIdx

theorem card_le_gapAlpha : Fintype.card (Fin 3 → Bool) ≤ Fintype.card GapAlpha := by
  classical
  have hl : Fintype.card (Fin 3 → Bool) = 8 := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num
  have hr : Fintype.card GapAlpha = 2 * 2 ^ 22 := by
    show Fintype.card (ZMod 2 × (ReadIdx → ZMod 2)) = 2 * 2 ^ 22
    rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, card_readIdx]
  rw [hl, hr]
  norm_num

/-- An injection of the 3-SAT alphabet into the amplifier's. -/
noncomputable def alphaEmb : (Fin 3 → Bool) ↪ GapAlpha :=
  (Function.Embedding.nonempty_of_card_le card_le_gapAlpha).some

/-- The 3-SAT constraint graph, read over the amplifier's alphabet. -/
noncomputable def baseCSP (φ : CNF) : ConstraintGraph GapAlpha :=
  (toGraph φ).lift alphaEmb

@[simp] theorem numEdges_baseCSP (φ : CNF) : (baseCSP φ).numEdges = 3 * φ.length := rfl

theorem satisfiable_baseCSP_iff {φ : CNF} (h3 : φ.Is3CNF) :
    (baseCSP φ).Satisfiable ↔ φ.Satisfiable := by
  classical
  rw [baseCSP, ConstraintGraph.satisfiable_lift_iff _ alphaEmb.injective]
  exact satisfiable_toGraph_iff h3

end Complexity
