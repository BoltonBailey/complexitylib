/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine
import Complexitylib.Models.TuringMachine.SingleTape
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Subroutines
import Complexitylib.Models.TuringMachine.Deterministic
import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Repetition
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
semantics, the single-tape simulation, machine combinators, Hoare-style
specifications, reusable subroutines, determinism results, the
universal machine, and the logarithmic-cost random access machine
(`Complexitylib.Models.RandomAccessMachine`). Proof-internal modules
(`…/Internal/…`, register machinery, emitter plumbing) are deliberately
not imported here — they stay in the build through the surface modules and
theorem files that need them.
-/
