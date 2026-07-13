/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine
import Complexitylib.Models.TuringMachine.SingleTape
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.ForInput
import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Experimental.Routine
import Complexitylib.Models.TuringMachine.Tape.Encoding
import Complexitylib.Models.TuringMachine.Subroutines
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput
import Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
import Complexitylib.Models.TuringMachine.Subroutines.PairEmit
import Complexitylib.Models.TuringMachine.Subroutines.PairValidate
import Complexitylib.Models.TuringMachine.Subroutines.PairSplit
import Complexitylib.Models.TuringMachine.Subroutines.ScanRight
import Complexitylib.Models.TuringMachine.Subroutines.UnaryLength
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.Models.TuringMachine.SpaceTime
import Complexitylib.Models.TuringMachine.Placement
import Complexitylib.Models.TuringMachine.Composition
import Complexitylib.Models.TuringMachine.Composition.PairWithInput
import Complexitylib.Models.TuringMachine.Deterministic
import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Repetition
import Complexitylib.Models.TuringMachine.Repetition.Correctness
import Complexitylib.Models.TuringMachine.UTM.Encoding
import Complexitylib.Models.TuringMachine.UTM.Machine
import Complexitylib.Models.TuringMachine.UTM.Universal
import Complexitylib.Models.TuringMachine.UTM.Clock
import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
import Complexitylib.Models.TuringMachine.UTM.ClockedUtm
import Complexitylib.Models.TuringMachine.UTM.HierarchySupport
import Complexitylib.Models.TuringMachine.UTM.Diagonal
import Complexitylib.Models.RandomAccessMachine

/-!
# Computation models

Aggregation module for the machine models: the core Turing-machine
semantics, the single-tape simulation, machine combinators, time- and
space-aware Hoare specifications, experimental first-order routine lowering, reusable
read-only-input loops, binary count-up loops, binary successor, binary length,
unary length, and pair-emission subroutines,
computed-value/input fanout, finite space-to-time bounds, determinism results,
the universal machine, and the logarithmic-cost random access machine
(`Complexitylib.Models.RandomAccessMachine`). Proof-internal modules
(`…/Internal/…`, register machinery, emitter plumbing) are deliberately not
imported here — they stay in the build through the surface modules and theorem
files that need them.
-/
