/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.AuxiliaryUnary.Defs
public import Complexitylib.Metacomplexity.MINKT.Defs

/-!
# Auxiliary-unary MINKT instances -- definitions

This layer identifies the auxiliary-unary distribution's seed-level sample
with the canonical MINKT instance it encodes. Keeping this map named avoids
re-decoding `(x, 1^t)` in every average-case theorem.
-/


@[expose] public section

namespace Complexity

namespace AuxiliaryUnarySeed

/-- The canonical MINKT instance sampled by an auxiliary-unary seed. -/
def minktInstance {m : ℕ} (seed : AuxiliaryUnarySeed m) : MINKT.Instance where
  output := seed.binary
  time := m - seed.split

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- Exact probability that the positive or totalized auxiliary-unary slice is
a strict MINKT yes-instance. Classical decidability is confined to this finite
enumeration boundary. -/
noncomputable def auxiliaryUnaryMINKTProbability {tapes : ℕ}
    (machine : TM tapes) (threshold : ℕ → ℕ) (m : ℕ) : ℚ := by
  classical
  exact auxiliaryUnary.probability m fun bits => bits ∈ MINKT machine threshold

end FiniteEnsemble

end Complexity
