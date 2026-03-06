import Mathlib.Data.Set.Functor

/-!
# The Possible Typeclass

`Possible M` equips a monad `M` with a predicate `possible : M α → α → Prop` that extracts
which values a monadic computation can produce. The laws ensure `possible` respects `pure`
(exactly the given value) and `>>=` (sequencing decomposes into an intermediate value).

This lets us write monadic transition functions for Turing machines and then extract a
step *relation* uniformly — `Id` yields deterministic machines, `SetM` yields nondeterministic
machines.
-/

universe u v

/-- A monad equipped with a predicate identifying which values a computation can produce. -/
class Possible (M : Type u → Type v) extends Monad M where
  possible : M α → α → Prop
  possible_pure : ∀ (a b : α), possible (pure a) b ↔ a = b
  possible_bind : ∀ (ma : M α) (f : α → M β) (b : β),
    possible (ma >>= f) b ↔ ∃ a, possible ma a ∧ possible (f a) b

/-- In the identity monad, the only possible value is the value itself. -/
instance : Possible Id where
  possible ma a := ma = a
  possible_pure _ _ := Iff.rfl
  possible_bind ma _ _ := ⟨fun h => ⟨ma, rfl, h⟩, fun ⟨_, ha, hb⟩ => ha ▸ hb⟩

/-- In the set monad, the possible values are the members of the set. -/
instance : Possible SetM where
  possible s a := a ∈ SetM.run s
  possible_pure a b := by
    simp [SetM.run, Set.pure_def]
    exact eq_comm
  possible_bind ma f b := by
    simp [SetM.run, Set.bind_def]
