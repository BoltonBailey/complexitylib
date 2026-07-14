/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Internal

/-!
# Verified direct-tableau generator

This module exposes the complete append-only generator for the regularly
padded direct-unrolling family. Its concrete binary routine is sound and emits
exactly the family's tagged circuit code, including the separate zero-length
member.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emitting all transition layers and restoring the outer counter is sound. -/
theorem emitTransitionSteps_sound (tm : TM k) :
    (emitTransitionSteps tm).Sound :=
  emitTransitionSteps_sound_internal tm

/-- A clean positive-horizon entry with a clear layer counter satisfies the
complete transition loop's domain. -/
theorem emitTransitionSteps_requires (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hloop : values Work.loop₂ = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitTransitionSteps tm).requires values :=
  emitTransitionSteps_requires_internal tm values hclean hloop hhorizon

/-- From the canonical initial configuration base and frontier, the complete
transition loop emits exactly the canonical flattened step stream. -/
theorem emitTransitionSteps_emitted (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    (emitTransitionSteps tm).emitted values =
      ((List.finRange (values Work.horizon)).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode :=
  emitTransitionSteps_emitted_exact_internal tm values hclean hhorizon n hloop
    hconfigBase havailable

/-- The complete positive tableau body is sound. -/
theorem positiveTableauBody_sound (tm : TM k) :
    (positiveTableauBody tm).Sound :=
  positiveTableauBody_sound_internal tm

/-- On a positive input length, the tableau body emits exactly the encoded raw
gate stream of the padded direct-unrolling member. -/
theorem positiveTableauBody_emitted (tm : TM k) (q : Polynomial ℕ)
    (n : ℕ) [NeZero n] (hn : 0 < n) :
    (positiveTableauBody tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (tm.paddedDirectUnrollingRawCircuit
        (TM.directSerializerHorizonPolynomial q).eval n).flatMap
          CircuitCode.RawGate.encode :=
  positiveTableauBody_emitted_internal tm q n hn

/-- The complete zero/positive padded-tableau generator is sound. -/
theorem paddedDirectUnrollingProgram_sound (tm : TM k)
    (q : Polynomial ℕ) : (paddedDirectUnrollingProgram tm q).Sound :=
  paddedDirectUnrollingProgram_sound_internal tm q

/-- The complete generator emits exactly the regularly padded direct family
code at every input length. -/
theorem paddedDirectUnrollingProgram_emitted (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).emitted
        (BinaryRoutine.inputLengthValues Work.inputLength n) =
      tm.paddedDirectUnrollingCode
        (TM.directSerializerHorizonPolynomial q).eval n :=
  paddedDirectUnrollingProgram_emitted_internal tm q n

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
