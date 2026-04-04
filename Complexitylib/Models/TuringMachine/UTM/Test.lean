import Complexitylib.Models.TuringMachine

/-!
# UTM Algorithm Test — Position 0 Debugging

Traces what happens when a TM starts at position 0 with head on ▷.
-/

namespace TM

deriving instance Repr for Γ
deriving instance Repr for Γw
deriving instance Repr for Dir3

def gName : Γ → String
  | .zero => "0" | .one => "1" | .blank => "□" | .start => "▷"

-- A trivial 1-work-tape TM that moves right and halts.
-- δ_right_of_start requires ALL states (even halted) to move right when reading ▷.
def testTM : TM 1 where
  Q := Fin 2
  qstart := 0
  qhalt := 1
  δ _q _iHead _wHeads _oHead :=
    -- Both states: write blank, move right (satisfies δ_right_of_start trivially)
    (1, fun _ => Γw.blank, Γw.blank, Dir3.right, fun _ => Dir3.right, Dir3.right)
  δ_right_of_start := by
    intro q iHead wHeads oHead
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def testInit : Cfg 1 (Fin 2) := testTM.initCfg []

def testStep : Option (Cfg 1 (Fin 2)) := testTM.step testInit

#eval do
  let init := testInit
  IO.println s!"=== Initial config ==="
  IO.println s!"state: {init.state.val}"
  IO.println s!"work[0].head: {(init.work 0).head}"
  IO.println s!"work[0].cells 0: {gName ((init.work 0).cells 0)}"
  IO.println s!"work[0].read: {gName (init.work 0).read}"
  IO.println s!"output.head: {init.output.head}"
  IO.println s!"output.cells 0: {gName (init.output.cells 0)}"
  IO.println s!"output.read: {gName init.output.read}"

  -- What does δ return?
  let δr := testTM.δ init.state init.input.read (fun i => (init.work i).read) init.output.read
  IO.println s!"\n=== δ result ==="
  IO.println s!"q': {δr.1.val}"
  IO.println s!"workWrite[0]: {repr (δr.2.1 0)}"
  IO.println s!"outWrite: {repr δr.2.2.1}"
  IO.println s!"inDir: {repr δr.2.2.2.1}"
  IO.println s!"workDir[0]: {repr (δr.2.2.2.2.1 0)}"
  IO.println s!"outDir: {repr δr.2.2.2.2.2}"

  match testStep with
  | none => IO.println "\nHalted immediately"
  | some c' =>
    IO.println s!"\n=== After step ==="
    IO.println s!"state: {c'.state.val}"
    IO.println s!"work[0].head: {(c'.work 0).head}"
    IO.println s!"work[0].cells 0: {gName ((c'.work 0).cells 0)}"
    IO.println s!"work[0].cells 1: {gName ((c'.work 0).cells 1)}"
    IO.println s!"output.head: {c'.output.head}"
    IO.println s!"output.cells 0: {gName (c'.output.cells 0)}"
    IO.println s!"output.cells 1: {gName (c'.output.cells 1)}"

    IO.println s!"\n=== Position 0 analysis ==="
    IO.println s!"δ says write Γw.blank to work[0], which is: {gName (Γw.blank).toΓ}"
    IO.println s!"Actual work[0].cells 0 after step: {gName ((c'.work 0).cells 0)}"
    let mismatch := ((c'.work 0).cells 0) != (Γw.blank).toΓ
    IO.println s!"Mismatch at position 0: {mismatch}"
    IO.println ""
    IO.println "CONCLUSION: Tape.write is a no-op at position 0."
    IO.println "The simulated tape keeps ▷ at cell 0, but δ returned □."
    IO.println "The UTM would encode □ in the sim tape at position 0,"
    IO.println "creating a mismatch with the actual simulated state."

end TM
