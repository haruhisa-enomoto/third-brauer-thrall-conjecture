module

public import LargeIndecomposable.Foundations.CategoryTheory.MorphismIdeal
@[expose] public section

/-!
# Linear functors out of Hom-ideal quotients

An additive linear functor which kills a two-sided Hom ideal factors through
the corresponding categorical quotient.  Fullness descends to the quotient,
while the reverse inclusion from the functor kernel into the Hom ideal makes
the descended functor faithful.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MorphismIdeal

universe u₁ v₁ u₂ v₂ w

variable {k : Type w} [Ring k]
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear k D]
variable (I : MorphismIdeal C) (F : C ⥤ D) [F.Additive] [F.Linear k]

local instance quotientPreadditiveInstance :
    Preadditive (CategoryTheory.Quotient I.rel) :=
  I.quotientPreadditive

local instance quotientLinearInstance :
    Linear k (CategoryTheory.Quotient I.rel) :=
  I.quotientLinear

/-- The two-sided Hom ideal consisting of the morphisms killed by a linear
functor. -/
def functorKernel : MorphismIdeal C where
  hom X Y := (LinearMap.ker (F.mapLinearMap k)).toAddSubgroup
  precomp := by
    intro X Y Z f g hg
    change F.map (f ≫ g) = 0
    change F.map g = 0 at hg
    rw [F.map_comp, hg]
    simp
  postcomp := by
    intro X Y Z f g hf
    change F.map (f ≫ g) = 0
    change F.map f = 0 at hf
    rw [F.map_comp, hf]
    simp

@[simp]
theorem mem_functorKernel_iff {X Y : C} (f : X ⟶ Y) :
    f ∈ (functorKernel (k := k) F).hom X Y ↔ F.map f = 0 :=
  Iff.rfl

/-- An additive functor kills a Hom ideal when every member of the ideal maps
to zero. -/
def IsKilledBy : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, f ∈ I.hom X Y → F.map f = 0

/-- A functor which kills a Hom ideal respects congruence modulo that ideal. -/
theorem map_eq_of_rel (hI : I.IsKilledBy F) {X Y : C}
    (f g : X ⟶ Y) (hfg : I.rel f g) : F.map f = F.map g := by
  change f - g ∈ I.hom X Y at hfg
  have hzero := hI hfg
  rw [F.map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The functor induced on the quotient by a killed Hom ideal. -/
def quotientLift (hI : I.IsKilledBy F) :
    CategoryTheory.Quotient I.rel ⥤ D :=
  CategoryTheory.Quotient.lift I.rel F
    (fun _ _ f g hfg ↦ I.map_eq_of_rel F hI f g hfg)

@[simp]
theorem quotientLift_map_functor_map (hI : I.IsKilledBy F)
    {X Y : C} (f : X ⟶ Y) :
    (I.quotientLift F hI).map
        ((CategoryTheory.Quotient.functor I.rel).map f) = F.map f :=
  rfl

instance quotientLift_additive (hI : I.IsKilledBy F) :
    (I.quotientLift F hI).Additive where
  map_add := by
    intro X Y f g
    obtain ⟨f, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective f
    obtain ⟨g, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective g
    exact F.map_add

instance quotientLift_linear (hI : I.IsKilledBy F) :
    (I.quotientLift F hI).Linear k where
  map_smul := by
    intro X Y f r
    obtain ⟨f, rfl⟩ :=
      (CategoryTheory.Quotient.functor I.rel).map_surjective f
    exact F.map_smul r f

instance quotientLift_full (hI : I.IsKilledBy F) [F.Full] :
    (I.quotientLift F hI).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := F.map_surjective f
    refine ⟨(CategoryTheory.Quotient.functor I.rel).map g, ?_⟩
    exact hg

/-- If every morphism killed by the original functor already belongs to the
quotient ideal, the descended functor is faithful. -/
theorem quotientLift_faithful (hI : I.IsKilledBy F)
    (hker : ∀ {X Y : C} {f : X ⟶ Y},
      F.map f = 0 → f ∈ I.hom X Y) :
    (I.quotientLift F hI).Faithful := by
  constructor
  intro X Y f g hfg
  obtain ⟨f, rfl⟩ :=
    (CategoryTheory.Quotient.functor I.rel).map_surjective f
  obtain ⟨g, rfl⟩ :=
    (CategoryTheory.Quotient.functor I.rel).map_surjective g
  apply CategoryTheory.Quotient.sound
  change f - g ∈ I.hom _ _
  apply hker
  change F.map f = F.map g at hfg
  rw [F.map_sub, hfg, sub_self]

end MorphismIdeal
