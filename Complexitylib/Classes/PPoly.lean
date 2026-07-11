import Complexitylib.Classes.PPoly.Defs
import Complexitylib.Circuits.Family

namespace Complexity

/-!
# P/poly and circuit-size classes

This module supplies the public API for nonuniform circuit classes. It relates
the exact pointwise-polynomial definition of `PPoly` to the big-O power
convention used elsewhere in the library.
-/

namespace BoolFunFamily

@[simp] theorem mem_toLanguage {f : BoolFunFamily} {x : List Bool} :
    x ∈ f.toLanguage ↔ f x.length x.get = true := Iff.rfl

@[simp] theorem mem_toLanguage_toList {f : BoolFunFamily} {n : ℕ}
    (x : BitString n) : x.toList ∈ f.toLanguage ↔ f n x = true := by
  change f x.toList.length x.toList.get = true ↔ f n x = true
  have h := List.equivSigmaTuple.apply_symm_apply
    (⟨n, x⟩ : Σ n, BitString n)
  have heval : f x.toList.length x.toList.get = f n x := by
    unfold BitString.toList
    exact congrArg (fun p : Σ n, BitString n => f p.1 p.2) h
  rw [heval]

theorem toLanguage_injective : Function.Injective toLanguage := by
  intro f g hfg
  funext n x
  have hx := Set.ext_iff.mp hfg x.toList
  simp only [mem_toLanguage_toList] at hx
  cases hfx : f n x <;> cases hgx : g n x <;> simp_all

end BoolFunFamily

namespace CircuitFamily

variable {B : Basis}

@[simp] theorem mem_language {F : CircuitFamily B} {x : List Bool} :
    x ∈ F.language ↔ F.evalList x = true := Iff.rfl

@[simp] theorem nil_mem_language {F : CircuitFamily B} :
    [] ∈ F.language ↔ F.emptyOutput = true := by
  rw [mem_language, F.evalList_nil]

theorem decides_iff (F : CircuitFamily B) (L : Language) :
    F.Decides L ↔ ∀ x, F.evalList x = true ↔ x ∈ L := by
  rw [Decides, Set.ext_iff]
  rfl

theorem decides_congr (F : CircuitFamily B) {L K : Language} (h : L = K) :
    F.Decides L ↔ F.Decides K := by
  subst K
  rfl

theorem decides_unique (F : CircuitFamily B) {L K : Language}
    (hL : F.Decides L) (hK : F.Decides K) : L = K :=
  hL.symm.trans hK

theorem Decides.evalList {F : CircuitFamily B} {L : Language}
    (h : F.Decides L) (x : List Bool) :
    F.evalList x = true ↔ x ∈ L :=
  (F.decides_iff L).mp h x

/-- A deciding family agrees with language membership on the canonical
    serialization of every fixed-length input. -/
theorem Decides.apply {F : CircuitFamily B} {L : Language}
    (h : F.Decides L) {n : ℕ} (x : BitString n) :
    F.function n x = true ↔ x.toList ∈ L := by
  rw [← F.evalList_toList]
  exact h.evalList x.toList

theorem Computes.decides {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) : F.Decides f.toLanguage := by
  change F.function.toLanguage = f.toLanguage
  exact congrArg BoolFunFamily.toLanguage h

/-- Computing a Boolean function family is equivalent to deciding its induced
    language. -/
theorem decides_toLanguage_iff (F : CircuitFamily B) (f : BoolFunFamily) :
    F.Decides f.toLanguage ↔ F.Computes f := by
  constructor
  · intro h
    change F.function.toLanguage = f.toLanguage at h
    exact BoolFunFamily.toLanguage_injective h
  · exact fun h => h.decides

end CircuitFamily

theorem SIZEWithBasis_mono (B : Basis) {s t : ℕ → ℕ}
    (hst : ∀ n, s n ≤ t n) :
    SIZEWithBasis B s ⊆ SIZEWithBasis B t := by
  rintro L ⟨F, hL, hs⟩
  exact ⟨F, hL, F.sizeBoundedBy_mono hs hst⟩

theorem SIZE_mono {s t : ℕ → ℕ} (hst : ∀ n, s n ≤ t n) :
    SIZE s ⊆ SIZE t :=
  SIZEWithBasis_mono Basis.andOr2 hst

section BigO

open Complexity

/-- Big-O characterization of membership in `PPoly`. -/
theorem mem_PPoly_iff {L : Language} :
    L ∈ PPoly ↔
      ∃ (F : CircuitFamily Basis.andOr2) (k : ℕ),
        F.Decides L ∧ F.size =O ((· ^ k) : ℕ → ℕ) := by
  constructor
  · rintro ⟨F, hL, hpoly⟩
    obtain ⟨k, hk⟩ := (F.polynomialSize_iff_bigO).mp hpoly
    exact ⟨F, k, hL, hk⟩
  · rintro ⟨F, k, hL, hk⟩
    exact ⟨F, hL, (F.polynomialSize_iff_bigO).mpr ⟨k, hk⟩⟩

end BigO

/-- Under the library's exact gate-count convention, unfolding the definitions
    identifies `PPoly` with the union of pointwise size classes over all natural
    polynomials. This is not the substantive advice-machine characterization of
    `P/poly`. -/
theorem PPoly_eq_iUnion_SIZE :
    PPoly = ⋃ p : Polynomial ℕ, SIZE fun n => p.eval n := by
  ext L
  simp only [PPoly, SIZE, SIZEWithBasis, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨F, hL, p, hp⟩
    exact ⟨p, F, hL, hp⟩
  · rintro ⟨p, F, hL, hp⟩
    exact ⟨F, hL, p, hp⟩

end Complexity
