/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.AC0.Defs
import Complexitylib.Circuits.DepthClasses

/-!
# The class AC⁰

Compatibility surface for `Complexity.AC0`: Boolean-function families computed
by constant-depth, polynomial-size circuit families of unbounded fan-in AND/OR
gates with free negation on wires. The definition and basic API now live in
`Complexitylib.Circuits.DepthClasses`; separation results against AC⁰ remain
a roadmap item.
-/
