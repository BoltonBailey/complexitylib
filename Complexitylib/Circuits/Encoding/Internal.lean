/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Internal.Codec
import Complexitylib.Circuits.Encoding.Internal.Fragment
import Complexitylib.Circuits.Encoding.Internal.Semantics
import Complexitylib.Circuits.Encoding.Internal.ToCircuit

/-!
# Encoded-circuit proof internals

Aggregation module for the codec, appendable-fragment laws, semantics, and
raw-to-typed reconstruction internals of the canonical fan-in-two circuit
encoding.
-/
