module

public import LargeIndecomposable.RayCategories.Basic.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# The radical-square-zero category of a bipartite quiver

For a finite quiver given by `src tgt : E → V` in which no arrow ends where an
arrow starts, the category `RSZ src tgt` has the vertices as objects; its
morphisms are the identities, the arrows and zero, and every composite of two
arrows is zero. It is a finite ray category (`RayCat.RSZ.isRayCategory`). For
the alternating cycle it is the crown category used to show that crowns make
algebras representation-infinite.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

namespace RayCat

variable {V E : Type}

/-- The objects of the radical-square-zero category. -/
@[nolint unusedArguments]
structure RSZ (src tgt : E → V) where
  /-- The vertex. -/
  as : V

/-- Morphisms: `none` is zero, `inl` an identity, `inr` an arrow. -/
def RHom (src tgt : E → V) (v w : V) : Type :=
  Option ({_u : Unit // v = w} ⊕ {e : E // src e = v ∧ tgt e = w})

variable {src tgt : E → V}

/-- Composition. -/
def RHom.comp {u v w : V} : RHom src tgt u v → RHom src tgt v w → RHom src tgt u w
  | none, _ => none
  | some _, none => none
  | some (.inl ⟨_, h⟩), some (.inl ⟨_, h'⟩) => some (.inl ⟨(), h.trans h'⟩)
  | some (.inl ⟨_, h⟩), some (.inr ⟨e, hs, ht⟩) => some (.inr ⟨e, hs.trans h.symm, ht⟩)
  | some (.inr ⟨e, hs, ht⟩), some (.inl ⟨_, h'⟩) => some (.inr ⟨e, hs, ht.trans h'⟩)
  | some (.inr _), some (.inr _) => none

instance : Category (RSZ src tgt) where
  Hom X Y := RHom src tgt X.as Y.as
  id X := some (.inl ⟨(), rfl⟩)
  comp f g := RHom.comp f g
  id_comp f := by
    rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩ <;> rfl
  comp_id f := by
    rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩ <;> rfl
  assoc f g h := by
    rcases f with _ | ⟨⟨_, _⟩ | ⟨_, _, _⟩⟩ <;> rcases g with _ | ⟨⟨_, _⟩ | ⟨_, _, _⟩⟩ <;>
      rcases h with _ | ⟨⟨_, _⟩ | ⟨_, _, _⟩⟩ <;> rfl

namespace RSZ

lemma comp_def {X Y Z : RSZ src tgt} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = RHom.comp (src := src) (tgt := tgt) f g := rfl

instance : HasZeroMorphisms (RSZ src tgt) where
  zero _ _ := ⟨none⟩
  comp_zero := by
    intro _ _ f _
    rcases f with _ | ⟨⟨_, _⟩ | ⟨_, _, _⟩⟩ <;> rfl
  zero_comp := by intros; rfl

lemma zero_def {X Y : RSZ src tgt} : (0 : X ⟶ Y) = (none : RHom src tgt X.as Y.as) := rfl

lemma id_def (X : RSZ src tgt) : 𝟙 X = (some (.inl ⟨(), rfl⟩) : RHom src tgt X.as X.as) := rfl

/-- The morphism of an arrow. -/
def arr (e : E) : (⟨src e⟩ : RSZ src tgt) ⟶ ⟨tgt e⟩ := (some (.inr ⟨e, rfl, rfl⟩) : RHom src tgt _ _)

lemma ext_as {X Y : RSZ src tgt} (h : X.as = Y.as) : X = Y := by
  cases X; cases Y; cases h; rfl

instance [DecidableEq V] [DecidableEq E] {X Y : RSZ src tgt} : DecidableEq (X ⟶ Y) :=
  inferInstanceAs
    (DecidableEq (Option ({_u : Unit // X.as = Y.as} ⊕ {e : E // src e = X.as ∧ tgt e = Y.as})))

instance [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {X Y : RSZ src tgt} :
    Fintype (X ⟶ Y) :=
  inferInstanceAs
    (Fintype (Option ({_u : Unit // X.as = Y.as} ⊕ {e : E // src e = X.as ∧ tgt e = Y.as})))

instance [Fintype V] : Fintype (RSZ src tgt) :=
  Fintype.ofEquiv V ⟨RSZ.mk, RSZ.as, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [DecidableEq V] : DecidableEq (RSZ src tgt) := fun X Y ↦
  decidable_of_iff (X.as = Y.as) ⟨ext_as, fun h ↦ h ▸ rfl⟩

variable (hb : ∀ e e' : E, tgt e ≠ src e')

include hb in
/-- An arrow composed with anything but an identity is zero. -/
lemma isRayCategory [Finite V] [Finite E] : IsRayCategory (RSZ src tgt) where
  skeletal := by
    rintro X Y ⟨i⟩
    obtain ⟨f, g, hfg, -⟩ := i
    rcases f with _ | ⟨⟨_, h⟩ | ⟨e, hs, ht⟩⟩
    · cases hfg
    · exact ext_as h
    · rcases g with _ | ⟨⟨_, h'⟩ | ⟨e', hs', ht'⟩⟩
      · cases hfg
      · exact ext_as h'.symm
      · cases hfg
  finite_out _ := by
    classical
    have := Fintype.ofFinite V
    exact Set.toFinite _
  finite_in _ := by
    classical
    have := Fintype.ofFinite V
    exact Set.toFinite _
  finite_hom X Y := by
    classical
    have := Fintype.ofFinite V
    have := Fintype.ofFinite E
    exact Finite.of_fintype _
  id_ne_zero _ := fun h ↦ by cases h
  nil X e he := by
    refine ⟨1, ?_⟩
    change 𝟙 X ≫ e = 0
    rw [Category.id_comp]
    rcases e with _ | ⟨⟨_, h⟩ | ⟨e', hs, ht⟩⟩
    · rfl
    · exact absurd rfl he
    · exact absurd (ht.trans hs.symm) (hb e' e')

end RSZ

end RayCat

end LargeIndecomposable
