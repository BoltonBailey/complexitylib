import Mathlib.Data.Set.Functor

universe u v

class Possible (M : Type u → Type v) extends Monad M where
  possible : M α → α → Prop
  possible_pure : ∀ (a b : α), possible (pure a) b ↔ a = b
  possible_bind : ∀ (ma : M α) (f : α → M β) (b : β),
    possible (ma >>= f) b ↔ ∃ a, possible ma a ∧ possible (f a) b

instance : Possible Id where
  possible ma a := ma = a
  possible_pure _ _ := Iff.rfl
  possible_bind ma _ _ := ⟨fun h => ⟨ma, rfl, h⟩, fun ⟨_, ha, hb⟩ => ha ▸ hb⟩

instance : Possible SetM where
  possible s a := a ∈ SetM.run s
  possible_pure a b := by
    simp [SetM.run, Set.pure_def]
    exact eq_comm
  possible_bind ma f b := by
    simp [SetM.run, Set.bind_def]
