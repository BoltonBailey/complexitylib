/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs

/-!
# Complete direct-unrolling generator -- definitions

The positive tableau body emits the initial packed configuration, exactly one
packed transition layer per horizon step, and the padded terminal acceptance
fragment. The outer step counter is restored after the loop. Prefixing this
body with `program` also handles the separately tagged length-zero family
member.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emit all packed transition layers and restore the outer step counter. -/
noncomputable def emitTransitionSteps (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor (emitStep tm) Work.loop₂ Work.horizon)
    (BinaryRoutine.clear Work.loop₂)

/-- Complete positive-length tableau body, excluding the tagged header. -/
noncomputable def positiveTableauBody (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [initialization tm, emitTransitionSteps tm, finalization tm]

/-- Complete zero/positive generator for the padded direct-unrolling code. -/
noncomputable def paddedDirectUnrollingProgram
    (tm : TM k) (q : Polynomial ℕ) : BinaryRoutine WorkCount :=
  program tm q (positiveTableauBody tm)

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
