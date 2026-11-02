module

public import LargeIndecomposable.RayCategories.Basic.Basic
public import Mathlib.Data.Fintype.Option

/-!
# Thin ray categories

A thin ray category has at most one nonzero morphism between two objects. It
is given by a relation `le x y` ("there is a nonzero morphism `x → y`") and a
predicate `nz x y z` ("the composite `x → y → z` is nonzero"), subject to the
axioms of `RayCat.ThinData`. All cleaving diagrams of BO13a §2.2 (trees with
zero relations, commutative squares, diamonds) are of this kind.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

namespace RayCat

/-- The data of a thin ray category on a finite type of objects. -/
structure ThinData (V : Type) where
  le : V → V → Prop
  nz : V → V → V → Prop
  refl : ∀ x, le x x
  antisymm : ∀ x y, le x y → le y x → x = y
  nz_le : ∀ x y z, le x y → le y z → nz x y z → le x z
  nz_left : ∀ x z, le x z → nz x x z
  nz_right : ∀ x z, le x z → nz x z z
  /-- Associativity: a triple composite is nonzero computed either way. -/
  assoc : ∀ x y z w, le x y → le y z → le z w →
    (nz x y z ∧ nz x z w ↔ nz y z w ∧ nz x y w)

variable {V : Type} (T : ThinData V)

open Classical

/-- The objects of the thin category. -/
@[nolint unusedArguments]
structure ThinCat (T : ThinData V) where
  /-- The vertex. -/
  as : V

/-- Morphisms: `none` is zero, `some` the unique nonzero morphism. -/
abbrev ThinHom (x y : V) : Type := Option {_u : Unit // T.le x y}

/-- Composition. -/
def ThinHom.comp {x y z : V} : ThinHom T x y → ThinHom T y z → ThinHom T x z
  | some ⟨_, h⟩, some ⟨_, h'⟩ => if hn : T.nz x y z then some ⟨(), T.nz_le x y z h h' hn⟩ else none
  | _, _ => none

lemma ThinHom.comp_some {x y z : V} (h : T.le x y) (h' : T.le y z) :
    ThinHom.comp T (some ⟨(), h⟩) (some ⟨(), h'⟩) =
      if hn : T.nz x y z then some ⟨(), T.nz_le x y z h h' hn⟩ else none := rfl

lemma ThinHom.comp_none_left {x y z : V} (g : ThinHom T y z) :
    ThinHom.comp T (none : ThinHom T x y) g = none := rfl

lemma ThinHom.comp_none_right {x y z : V} (f : ThinHom T x y) :
    ThinHom.comp T f (none : ThinHom T y z) = none := by
  rcases f with _ | ⟨_, _⟩ <;> rfl

lemma ThinHom.comp_eq_some_iff {x y z : V} (f : ThinHom T x y) (g : ThinHom T y z) :
    ThinHom.comp T f g ≠ none ↔ ∃ hf hg, f = some ⟨(), hf⟩ ∧ g = some ⟨(), hg⟩ ∧ T.nz x y z := by
  rcases f with _ | ⟨⟨⟩, hf⟩
  · exact ⟨fun h ↦ absurd (ThinHom.comp_none_left T g) h, fun ⟨_, _, h, _⟩ ↦ by cases h⟩
  rcases g with _ | ⟨⟨⟩, hg⟩
  · exact ⟨fun h ↦ absurd (ThinHom.comp_none_right T _) h, fun ⟨_, _, _, h, _⟩ ↦ by cases h⟩
  rw [ThinHom.comp_some]
  by_cases hn : T.nz x y z
  · rw [dif_pos hn]
    exact ⟨fun _ ↦ ⟨hf, hg, rfl, rfl, hn⟩, fun _ ↦ Option.some_ne_none _⟩
  · rw [dif_neg hn]
    exact ⟨fun h ↦ absurd rfl h, fun ⟨_, _, _, _, h⟩ ↦ absurd h hn⟩

lemma ThinHom.ext_ne_none {x y : V} {f g : ThinHom T x y} (hf : f ≠ none ↔ g ≠ none) : f = g := by
  rcases f with _ | ⟨⟨⟩, _⟩ <;> rcases g with _ | ⟨⟨⟩, _⟩
  · rfl
  · exact absurd (hf.2 (by simp)) (by simp)
  · exact absurd (hf.1 (by simp)) (by simp)
  · rfl

instance : Category (ThinCat T) where
  Hom X Y := ThinHom T X.as Y.as
  id X := some ⟨(), T.refl X.as⟩
  comp f g := ThinHom.comp T f g
  id_comp f := by
    rcases f with _ | ⟨⟨⟩, h⟩
    · rfl
    · rw [ThinHom.comp_some, dif_pos (T.nz_left _ _ h)]
  comp_id f := by
    rcases f with _ | ⟨⟨⟩, h⟩
    · rfl
    · rw [ThinHom.comp_some, dif_pos (T.nz_right _ _ h)]
  assoc {W X Y Z} f g h := by
    apply ThinHom.ext_ne_none
    rw [ThinHom.comp_eq_some_iff, ThinHom.comp_eq_some_iff]
    constructor
    · rintro ⟨hfg, hh, efg, rfl, hn2⟩
      obtain ⟨hf, hg, rfl, rfl, hn1⟩ := (ThinHom.comp_eq_some_iff T f g).1 (by rw [efg]; simp)
      have := (T.assoc _ _ _ _ hf hg hh).1 ⟨hn1, hn2⟩
      refine ⟨hf, T.nz_le _ _ _ hg hh this.1, rfl, ?_, this.2⟩
      rw [ThinHom.comp_some, dif_pos this.1]
    · rintro ⟨hf, hgh, rfl, egh, hn2⟩
      obtain ⟨hg, hh, rfl, rfl, hn1⟩ := (ThinHom.comp_eq_some_iff T g h).1 (by rw [egh]; simp)
      have := (T.assoc _ _ _ _ hf hg hh).2 ⟨hn1, hn2⟩
      refine ⟨T.nz_le _ _ _ hf hg this.1, hh, ?_, rfl, this.2⟩
      rw [ThinHom.comp_some, dif_pos this.1]

namespace ThinCat

variable {T}

lemma comp_def {X Y Z : ThinCat T} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = ThinHom.comp T f g := rfl

instance : HasZeroMorphisms (ThinCat T) where
  zero _ _ := ⟨none⟩
  comp_zero := by intro _ _ f _; rcases f with _ | ⟨_, _⟩ <;> rfl
  zero_comp := by intros; rfl

lemma ext_as {X Y : ThinCat T} (h : X.as = Y.as) : X = Y := by
  cases X; cases Y; cases h; rfl

/-- The nonzero morphism. -/
def mor {X Y : ThinCat T} (h : T.le X.as Y.as) : X ⟶ Y := (some ⟨(), h⟩ : ThinHom T _ _)

lemma mor_comp {X Y Z : ThinCat T} (h : T.le X.as Y.as) (h' : T.le Y.as Z.as)
    (hn : T.nz X.as Y.as Z.as) : mor h ≫ mor h' = mor (T.nz_le _ _ _ h h' hn) := by
  rw [comp_def, mor, mor, ThinHom.comp_some, dif_pos hn]; rfl

lemma mor_comp_zero {X Y Z : ThinCat T} (h : T.le X.as Y.as) (h' : T.le Y.as Z.as)
    (hn : ¬T.nz X.as Y.as Z.as) : mor h ≫ mor h' = 0 := by
  rw [comp_def, mor, mor, ThinHom.comp_some, dif_neg hn]; rfl

lemma eq_zero_or_mor {X Y : ThinCat T} (f : X ⟶ Y) : f = 0 ∨ ∃ h, f = mor h := by
  rcases f with _ | ⟨_, h⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h, rfl⟩

instance [Fintype V] : Fintype (ThinCat T) :=
  Fintype.ofEquiv V ⟨ThinCat.mk, ThinCat.as, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [Finite V] : Finite (ThinCat T) := Finite.of_injective ThinCat.as fun _ _ h ↦ ext_as h

instance [DecidableEq V] : DecidableEq (ThinCat T) := fun X Y ↦
  decidable_of_iff (X.as = Y.as) ⟨ext_as, fun h ↦ h ▸ rfl⟩

/-- A thin category is a ray category. -/
instance isRayCategory [Finite V] : IsRayCategory (ThinCat T) where
  skeletal := by
    rintro ⟨a⟩ ⟨b⟩ ⟨i⟩
    obtain ⟨f, g, hfg, -⟩ := i
    rcases f with _ | ⟨_, h⟩
    · cases hfg
    · rcases g with _ | ⟨_, h'⟩
      · cases hfg
      · exact ext_as (T.antisymm a b h h')
  finite_out _ := Set.toFinite _
  finite_in _ := Set.toFinite _
  finite_hom X Y := by
    classical
    change Finite (Option {_u : Unit // T.le X.as Y.as})
    infer_instance
  id_ne_zero _ := fun h ↦ by cases h
  nil X e he := by
    refine ⟨1, ?_⟩
    change 𝟙 X ≫ e = 0
    rw [Category.id_comp]
    rcases e with _ | ⟨_, h⟩
    · rfl
    · exact absurd rfl he

end ThinCat

end RayCat

end LargeIndecomposable
