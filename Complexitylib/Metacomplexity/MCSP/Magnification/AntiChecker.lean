/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.GoodString
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Encoding
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Relation
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Circuit
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Randomized
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Hashing
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Estimator

/-!
# The Oliveira--Pich--Santhanam Anti-Checker Lemma

Public aggregation module for the rounded finite parameters, typed multi-output
generator contract, semantic approximate-selection rounds, and the explicit
conditional approximate-counter circuit and estimator interfaces. The
randomized-counter layer isolates the finite union-bound and hardwiring step,
and the fixed-width domain layer embeds variable-length canonical circuit codes
with one delimiter bit and without changing the survivor count. A specialized
bridge now turns any bounded relative-hashing circuit on that domain into the
required deterministic counter. Constructing those hashing circuits from
`NP ⊆ P/poly` remains open.
-/
