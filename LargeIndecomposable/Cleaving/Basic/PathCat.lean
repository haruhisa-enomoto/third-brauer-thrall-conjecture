module

public import LargeIndecomposable.RayCategories.Basic.Basic
public import LargeIndecomposable.Quivers.Paths.AcyclicFinitePaths
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The path category of a finite acyclic quiver

For a finite acyclic quiver `Q`, the category `PathCat Q` has the vertices as
objects and the paths, together with a zero morphism, as morphisms. It is a
finite ray category (`RayCat.PathCat.isRayCategory`); its linearization is the
path algebra `kQ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

namespace RayCat

variable {Q : Type} [Quiver.{0} Q]

variable (Q) in
/-- The objects of the path category. -/
structure PathCat where
  /-- The vertex. -/
  as : Q

/-- Composition of possibly zero paths. -/
def pcomp {a b c : Q} : Option (Quiver.Path a b) → Option (Quiver.Path b c) → Option (Quiver.Path a c)
  | some p, some q => some (p.comp q)
  | _, _ => none

instance : Category (PathCat Q) where
  Hom X Y := Option (Quiver.Path X.as Y.as)
  id X := some Quiver.Path.nil
  comp f g := pcomp f g
  id_comp f := by rcases f with _ | p <;> simp [pcomp]
  comp_id f := by rcases f with _ | p <;> simp [pcomp]
  assoc f g h := by
    rcases f with _ | p <;> rcases g with _ | q <;> rcases h with _ | r <;> simp [pcomp]

namespace PathCat

lemma comp_def {X Y Z : PathCat Q} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = pcomp f g := rfl

instance : HasZeroMorphisms (PathCat Q) where
  zero _ _ := ⟨none⟩
  comp_zero := by intro _ _ f _; rcases f with _ | p <;> rfl
  zero_comp := by intros; rfl

lemma zero_def {X Y : PathCat Q} : (0 : X ⟶ Y) = (none : Option (Quiver.Path X.as Y.as)) := rfl

lemma id_def (X : PathCat Q) : 𝟙 X = (some Quiver.Path.nil : Option (Quiver.Path X.as X.as)) := rfl

/-- The morphism of a path. -/
def ofPath {a b : Q} (p : Quiver.Path a b) : (⟨a⟩ : PathCat Q) ⟶ ⟨b⟩ := (some p : Option _)

lemma ext_as {X Y : PathCat Q} (h : X.as = Y.as) : X = Y := by
  cases X; cases Y; cases h; rfl

instance [Fintype Q] : Fintype (PathCat Q) :=
  Fintype.ofEquiv Q ⟨PathCat.mk, PathCat.as, fun _ ↦ rfl, fun _ ↦ rfl⟩

instance [Finite Q] : Finite (PathCat Q) :=
  Finite.of_injective PathCat.as fun X Y h ↦ ext_as h

instance [DecidableEq Q] : DecidableEq (PathCat Q) := fun X Y ↦
  decidable_of_iff (X.as = Y.as) ⟨ext_as, fun h ↦ h ▸ rfl⟩

/-- The path category of a finite acyclic quiver is a ray category. -/
lemma isRayCategory [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] (hQ : LargeIndecomposable.Foundations.Quiver.IsAcyclic Q) :
    IsRayCategory (PathCat Q) where
  skeletal := by
    rintro ⟨a⟩ ⟨b⟩ ⟨i⟩
    obtain ⟨f, g, hfg, -⟩ := i
    rcases f with _ | p
    · cases hfg
    · rcases g with _ | q
      · cases hfg
      · exact ext_as (LargeIndecomposable.Foundations.Quiver.IsAcyclic.eq_of_paths hQ p q)
  finite_out _ := Set.toFinite _
  finite_in _ := Set.toFinite _
  finite_hom X Y := by
    have := LargeIndecomposable.Foundations.finite_paths_of_isAcyclic hQ
    have : Finite (Quiver.Path X.as Y.as) :=
      Finite.of_injective (fun p ↦ (⟨X.as, Y.as, p⟩ : Σ a b : Q, Quiver.Path a b))
        (fun p q h ↦ by simpa using h)
    change Finite (Option (Quiver.Path X.as Y.as))
    infer_instance
  id_ne_zero _ := fun h ↦ by cases h
  nil X e he := by
    refine ⟨1, ?_⟩
    change 𝟙 X ≫ e = 0
    rw [Category.id_comp]
    rcases e with _ | p
    · rfl
    · exact absurd (by rw [LargeIndecomposable.Foundations.Quiver.IsAcyclic.eq_nil hQ p]; rfl) he

/-! ### Functors out of a path category -/

section Lift

variable {C : Type*} [Category C] [HasZeroMorphisms C] (φ : Q ⥤q C)

/-- The functor `PathCat Q ⥤ C` sending an arrow `a` to `φ a`. -/
def lift : PathCat Q ⥤ C where
  obj X := φ.obj X.as
  map {X Y} f := match f with
    | none => 0
    | some p => composePath (φ.mapPath p)
  map_id X := rfl
  map_comp {X Y Z} f g := by
    rw [comp_def]
    rcases f with _ | p <;> rcases g with _ | q
    all_goals simp only [pcomp, zero_comp, comp_zero]
    rw [Prefunctor.mapPath_comp, composePath_comp]

instance : (lift φ).PreservesZeroMorphisms where
  map_zero _ _ := rfl

lemma lift_map_ofPath {a b : Q} (p : Quiver.Path a b) :
    (lift φ).map (ofPath p) = composePath (φ.mapPath p) := rfl

end Lift

lemma ofPath_comp {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    ofPath p ≫ ofPath q = ofPath (p.comp q) := rfl

end PathCat

end RayCat

end LargeIndecomposable
