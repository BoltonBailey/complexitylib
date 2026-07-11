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
import Complexitylib.Models.TuringMachine.UTM.Encoding
import Complexitylib.Models.TuringMachine.UTM.Desc
import Complexitylib.Models.TuringMachine.UTM.Interp
import Complexitylib.Models.TuringMachine.UTM.VTape
import Complexitylib.Models.TuringMachine.UTM.Bits
import Complexitylib.Models.TuringMachine.UTM.Extract
import Complexitylib.Models.TuringMachine.UTM.Body
import Complexitylib.Models.TuringMachine.UTM.HaltTest
import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.Verdict
import Complexitylib.Models.TuringMachine.UTM.BodyMatch
import Complexitylib.Models.TuringMachine.UTM.BodyApply
import Complexitylib.Models.TuringMachine.UTM.DescLayout
import Complexitylib.Models.TuringMachine.UTM.BodyLookup
import Complexitylib.Models.TuringMachine.UTM.BodyAssembly
import Complexitylib.Models.TuringMachine.UTM.BodyLoop
import Complexitylib.Models.TuringMachine.UTM.StepGlue
import Complexitylib.Models.TuringMachine.UTM.Machine
import Complexitylib.Models.TuringMachine.UTM.PairSelf
import Complexitylib.Models.TuringMachine.UTM.BodyIteration
import Complexitylib.Models.TuringMachine.UTM.Terminated
import Complexitylib.Models.TuringMachine.UTM.Sim
import Complexitylib.Models.TuringMachine.UTM.SimLoop
import Complexitylib.Models.TuringMachine.UTM.Universal
import Complexitylib.Models.TuringMachine.UTM.Clock
import Complexitylib.Models.TuringMachine.UTM.ClockFrontier
import Complexitylib.Models.TuringMachine.UTM.SimClocked
import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
import Complexitylib.Models.TuringMachine.UTM.SeekFrontier
import Complexitylib.Models.TuringMachine.UTM.ClockedUtm
import Complexitylib.Models.TuringMachine.UTM.TermCheck
import Complexitylib.Models.TuringMachine.UTM.NegOut
import Complexitylib.Models.TuringMachine.UTM.HierarchySupport
import Complexitylib.Models.TuringMachine.UTM.Diagonal

/-!
# Computation models

Aggregation module for the machine models: the core Turing-machine
semantics, the single-tape simulation, machine combinators, Hoare-style
specifications, reusable subroutines, determinism results, and the
universal machine. Proof-internal modules (`…/Internal/…`, register
machinery, emitter plumbing) are deliberately not imported here — they
stay in the build through the surface modules and theorem files that
need them.
-/
