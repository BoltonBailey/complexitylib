/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.AlgCompose
public import Complexitylib.Classes.PCP.Internal.AlgPreRel
public import Complexitylib.Classes.PCP.Internal.AlgStep

/-!
# A composed position's number

A read of the assembled tester lands in one of three kinds of block: the
encoding block of a vertex, a dart's linear table, or a dart's quadratic table.
Which kind, and which cube inside the block, depends only on the read and the
random string — with two exceptions, where the cube is shifted by the
arithmetization of the dart's satisfying set. Which *block*, on the other hand,
is a vertex or a dart of the outer graph, so it is the only part that grows with
the input.

This module splits a position's number along that seam.

## Main definitions

- `Complexity.RegCSP.readKind` — which kind of block a read lands in
- `Complexity.RegCSP.blockNum`, `Complexity.RegCSP.cubeNum` — the block and the
  cube inside it
- `Complexity.RegCSP.posNum` — the number the two make

## Main results

- `Complexity.RegCSP.enc_pos_compose` — that number is the position's
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis Tester

namespace RegCSP

variable {β : Type} [Fintype β] [DecidableEq β] [Nonempty β] (R : RegCSP β)
  [NumEnc R.graph.V] [NumEnc R.graph.D] {B : ℕ} (enc : β → Cube B)

/-- Which kind of block a read's position lies in: an encoding block (`0`), a
dart's linear table (`1`), or a dart's quadratic table (`2`). -/
def readKind : ReadIdx → ℕ
  | .i5r | .i6r => 0
  | .g2x | .g2y | .g2s | .c3cQ | .c3tQ | .k4qG | .k4tG => 2
  | _ => 1

/-- The number of the vertex or dart whose block a read's position lies in. -/
noncomputable def blockNum (p : R.Dart) : ReadIdx → ℕ
  | .i5r => NumEnc.enc p.1
  | .i6r => NumEnc.enc (R.graph.nbr p.1 p.2)
  | .f1x | .f1y | .f1s | .g2x | .g2y | .g2s | .c3cQ | .c3tQ | .c3cX | .c3xX | .c3cY | .c3yY
  | .k4qG | .k4tG | .k4cF | .k4lF | .i5c | .i5b | .i6c | .i6b => NumEnc.enc p

/-- The cube a read names, from the satisfying set alone. -/
noncomputable def cubeOfSet (S : Finset (Cube (kOf B))) (z : Cube (ROf B)) : ReadIdx → ℕ
  | .f1x => NumEnc.enc (leftBlock (blk1 z))
  | .f1y => NumEnc.enc (rightBlock (blk1 z))
  | .f1s => NumEnc.enc (leftBlock (blk1 z) + rightBlock (blk1 z))
  | .g2x => NumEnc.enc (leftBlock (blk2 z))
  | .g2y => NumEnc.enc (rightBlock (blk2 z))
  | .g2s => NumEnc.enc (leftBlock (blk2 z) + rightBlock (blk2 z))
  | .c3cQ => NumEnc.enc (cQ (blk3 z))
  | .c3tQ => NumEnc.enc (tensor (qX (blk3 z)) (qY (blk3 z)) + cQ (blk3 z))
  | .c3cX => NumEnc.enc (cX (blk3 z))
  | .c3xX => NumEnc.enc (qX (blk3 z) + cX (blk3 z))
  | .c3cY => NumEnc.enc (cY (blk3 z))
  | .c3yY => NumEnc.enc (qY (blk3 z) + cY (blk3 z))
  | .k4qG => NumEnc.enc (rightBlock (rightBlock (blk4 z)))
  | .k4tG => NumEnc.enc ((QuadConstraint.combine (oneHotSystem S)
      (leftBlock (blk4 z))).quad + rightBlock (rightBlock (blk4 z)))
  | .k4cF => NumEnc.enc (leftBlock (rightBlock (blk4 z)))
  | .k4lF => NumEnc.enc ((QuadConstraint.combine (oneHotSystem S)
      (leftBlock (blk4 z))).lin + leftBlock (rightBlock (blk4 z)))
  | .i5r => NumEnc.enc (leftBlock (blk5 z))
  | .i5c => NumEnc.enc (rightBlock (blk5 z))
  | .i5b => NumEnc.enc (basisVec (inTail B (leftBlock (blk5 z))) + rightBlock (blk5 z))
  | .i6r => NumEnc.enc (leftBlock (blk6 z))
  | .i6c => NumEnc.enc (rightBlock (blk6 z))
  | .i6b => NumEnc.enc (basisVec (inHead B (leftBlock (blk6 z))) + rightBlock (blk6 z))

/-- The number of the cube a read's position names inside its block. -/
noncomputable def cubeNum (p : R.Dart) (z : Cube (ROf B)) : ReadIdx → ℕ :=
  cubeOfSet (R.satSet enc p) z

/-- The number a kind, a block and a cube make: encoding blocks first, then the
linear tables, then the quadratic ones. -/
def posNum (cardV cardD cardB cardN cardNN k w c : ℕ) : ℕ :=
  if k = 0 then w * cardB + c
  else if k = 1 then cardV * cardB + (w * cardN + c)
  else cardV * cardB + (cardV * cardD * cardN + (w * cardNN + c))

omit [DecidableEq β] [Nonempty β] in
/-- **A composed position's number.** -/
theorem enc_pos_compose (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx) :
    NumEnc.enc ((R.compose enc).pos p z i)
      = posNum (NumEnc.card R.graph.V) (NumEnc.card R.graph.D) (NumEnc.card (Cube B))
        (NumEnc.card (Cube (nOf B))) (NumEnc.card (Cube (nOf B * nOf B)))
        (readKind i) (R.blockNum p i) (R.cubeNum enc p z i) := by
  cases i <;> rfl

omit [DecidableEq β] [Nonempty β] in
/-- The test's verdict, from the satisfying set alone. -/
noncomputable def checkOfSet (S : Finset (Cube (kOf B))) (z : Cube (ROf B))
    (rd : ReadIdx → ZMod 2) : Bool :=
  decide (bitFormula S z rd)

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **The cube depends on the satisfying set alone.** -/
theorem cubeNum_eq_cubeOfSet (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx) :
    R.cubeNum enc p z i = cubeOfSet (R.satSet enc p) z i := rfl

omit [DecidableEq β] [Nonempty β] [NumEnc R.graph.V] [NumEnc R.graph.D] in
/-- **And so does the verdict.** -/
theorem check_eq_checkOfSet (p : R.Dart) (z : Cube (ROf B)) :
    (R.compose enc).check p z = checkOfSet (R.satSet enc p) z := rfl

omit [DecidableEq β] [Nonempty β] in
set_option maxHeartbeats 800000 in
/-- **An edge's data and all three of its numbers**, in one package: a caller
never has to spell the composed system out, nor match anything against it. -/
theorem edge_facts (e : ℕ) (he : e < (R.compose enc).toGraph.numEdges) :
    ∃ (p : R.Dart) (z : Cube (ROf B)) (i : ReadIdx),
      e = ((NumEnc.enc p.1 * NumEnc.card R.graph.D + NumEnc.enc p.2) * 2 ^ ROf B
            + NumEnc.enc z) * 22 + NumEnc.enc i
        ∧ ((R.compose enc).toGraph.tail ⟨e, he⟩).val = (R.compose enc).tailNum e
        ∧ ((R.compose enc).toGraph.head ⟨e, he⟩).val
            = posNum (NumEnc.card R.graph.V) (NumEnc.card R.graph.D)
                (NumEnc.card (Cube B)) (NumEnc.card (Cube (nOf B)))
                (NumEnc.card (Cube (nOf B * nOf B)))
                (readKind i) (R.blockNum p i) (R.cubeNum enc p z i)
        ∧ (R.compose enc).toGraph.rel ⟨e, he⟩
            = MultiTest.relOfCheck ((R.compose enc).check p z) i := by
  obtain ⟨p, z, i, hp, hz, hi, hsplit⟩ := R.edge_data B enc e he
  refine ⟨p, z, i, hsplit, (MultiTest.tailNum_eq _ ⟨e, he⟩).symm, ?_, ?_⟩
  · rw [hp, hz, hi, MultiTest.val_head_toGraph, enc_pos_compose]
    rfl
  · rw [hp, hz, hi]
    exact MultiTest.rel_toGraph_eq _ _

end RegCSP

end Complexity
