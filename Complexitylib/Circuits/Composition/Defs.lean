/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Circuit composition -- definitions

Serial composition materializes the `K` output gates of an inner
`N → K` circuit as internal wires, then rewires every input of an outer
`K → M` circuit to those wires. If the two circuits have `G₁` and `G₂`
internal gates, the composite has exactly `G₁ + K + G₂` internal gates.
Consequently its library size is the sum of the two source sizes.
-/


@[expose] public section

namespace Complexity

namespace Gate

/-- Reindex every input wire of a gate, preserving its operation, arity, and
per-edge negation flags. -/
def rewire {B : Basis} {W W' : ℕ}
    (gate : Gate B W) (mapWire : Fin W → Fin W') : Gate B W' where
  op := gate.op
  fanIn := gate.fanIn
  arityOk := gate.arityOk
  inputs input := mapWire (gate.inputs input)
  negated := gate.negated

end Gate

namespace Circuit

variable {B : Basis} {N K M G₁ G₂ : ℕ}
  [NeZero N] [NeZero K] [NeZero M]

/-- Embed an inner-circuit wire into the initial region of the composite. -/
def embedInnerWire (wire : Fin (N + G₁)) :
    Fin (N + (G₁ + K + G₂)) :=
  ⟨wire.val, by omega⟩

/-- The composite wire driven by one materialized inner output gate. -/
def embedInnerOutput (output : Fin K) :
    Fin (N + (G₁ + K + G₂)) :=
  ⟨N + G₁ + output.val, by omega⟩

/-- Embed an outer-circuit wire into the composite. Outer primary inputs map
to the materialized inner outputs; outer internal wires map after that block. -/
def embedOuterWire (wire : Fin (K + G₂)) :
    Fin (N + (G₁ + K + G₂)) :=
  if hinput : wire.val < K then
    ⟨N + G₁ + wire.val, by omega⟩
  else
    ⟨N + G₁ + K + (wire.val - K), by omega⟩

/-- The gate at one flat index of a serially composed circuit, bundled with
its acyclicity proof. -/
def composeGate
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (index : Fin (G₁ + K + G₂)) :
    {gate : Gate B (N + (G₁ + K + G₂)) //
      ∀ input : Fin gate.fanIn,
        (gate.inputs input).val < N + index.val} := by
  if hinner : index.val < G₁ then
    refine ⟨(inner.gates ⟨index.val, hinner⟩).rewire embedInnerWire, ?_⟩
    intro input
    have hacyclic := inner.acyclic ⟨index.val, hinner⟩ input
    change ((inner.gates ⟨index.val, hinner⟩).inputs input).val <
      N + index.val at hacyclic
    exact hacyclic
  else if houtput : index.val < G₁ + K then
    refine
      ⟨(inner.outputs ⟨index.val - G₁, by omega⟩).rewire
        embedInnerWire, ?_⟩
    intro input
    dsimp only [Gate.rewire, embedInnerWire]
    omega
  else
    refine
      ⟨(outer.gates ⟨index.val - G₁ - K, by omega⟩).rewire
        embedOuterWire, ?_⟩
    intro input
    dsimp only [Gate.rewire, embedOuterWire]
    let source :=
      (outer.gates ⟨index.val - G₁ - K, by omega⟩).inputs input
    have hacyclic :=
      outer.acyclic ⟨index.val - G₁ - K, by omega⟩ input
    change source.val < K + (index.val - G₁ - K) at hacyclic
    split_ifs with hsource
    · dsimp only
      omega
    · dsimp only
      have hsource' : source.val - K < index.val - G₁ - K := by
        omega
      omega

/-- Serially compose `outer : K → M` after `inner : N → K`.

The `K` output gates of `inner` become internal gates so that they can feed
arbitrarily many gates of `outer` without duplicating computation. -/
def compose (outer : Circuit B K M G₂) (inner : Circuit B N K G₁) :
    Circuit B N M (G₁ + K + G₂) where
  gates index := (composeGate outer inner index).val
  outputs output := (outer.outputs output).rewire embedOuterWire
  acyclic index := (composeGate outer inner index).property

/-! ## Parallel composition -/

/-- Embed a wire of the left parallel component without changing its index. -/
def embedParallelLeftWire (wire : Fin (N + G₁)) :
    Fin (N + (G₁ + G₂)) :=
  ⟨wire.val, by omega⟩

/-- Embed a wire of the right parallel component. Primary inputs remain shared,
while internal gates move after the left component's internal gates. -/
def embedParallelRightWire (wire : Fin (N + G₂)) :
    Fin (N + (G₁ + G₂)) :=
  if hinput : wire.val < N then
    ⟨wire.val, by omega⟩
  else
    ⟨N + G₁ + (wire.val - N), by omega⟩

/-- The gate at one flat index of two circuits placed in parallel, bundled with
its acyclicity proof. -/
def parallelGate
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (index : Fin (G₁ + G₂)) :
    {gate : Gate B (N + (G₁ + G₂)) //
      ∀ input : Fin gate.fanIn,
        (gate.inputs input).val < N + index.val} := by
  if hleft : index.val < G₁ then
    refine
      ⟨(left.gates ⟨index.val, hleft⟩).rewire
        embedParallelLeftWire, ?_⟩
    intro input
    have hacyclic := left.acyclic ⟨index.val, hleft⟩ input
    change ((left.gates ⟨index.val, hleft⟩).inputs input).val <
      N + index.val at hacyclic
    exact hacyclic
  else
    refine
      ⟨(right.gates ⟨index.val - G₁, by omega⟩).rewire
        embedParallelRightWire, ?_⟩
    intro input
    let source :=
      (right.gates ⟨index.val - G₁, by omega⟩).inputs input
    have hacyclic :=
      right.acyclic ⟨index.val - G₁, by omega⟩ input
    change source.val < N + (index.val - G₁) at hacyclic
    change (embedParallelRightWire source).val < N + index.val
    unfold embedParallelRightWire
    split_ifs with hsource
    · change source.val < N + index.val
      omega
    · have hinternal : source.val - N < index.val - G₁ := by
        omega
      change N + G₁ + (source.val - N) < N + index.val
      omega

/-- Place two circuits with the same primary inputs in parallel. Their internal
gates occupy disjoint consecutive blocks and their output tuples are appended. -/
def parallel (left : Circuit B N K G₁) (right : Circuit B N M G₂) :
    Circuit B N (K + M) (G₁ + G₂) where
  gates index := (parallelGate left right index).val
  outputs output :=
    if hleft : output.val < K then
      (left.outputs ⟨output.val, hleft⟩).rewire embedParallelLeftWire
    else
      (right.outputs ⟨output.val - K, by omega⟩).rewire
        embedParallelRightWire
  acyclic index := (parallelGate left right index).property

end Circuit

end Complexity
