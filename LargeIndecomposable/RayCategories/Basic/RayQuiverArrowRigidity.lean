module

public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement

@[expose] public section

/-!
# Rigidity of irreducible arrows in a finite ray category

Factorization comparability and the absence of nontrivial invertible endorays
force two irreducible rays with the same endpoints to coincide.  Consequently
the neighboring vertex determines an incoming or outgoing quiver arrow.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

private theorem irreducible_eq_of_same_endpoints
    [IsFiniteRayCategory C]
    {X Y : C} {f g : X ⟶ Y}
    (hf : IsIrreducibleRayMorphism f)
    (hg : IsIrreducibleRayMorphism g) : f = g := by
  rcases IsFiniteRayCategory.factorization_comparable f g with hfg | hgf
  · rcases hfg with ⟨a, b, hab⟩
    have hbIso : IsIso b := by
      rcases hg.2.2 Y (a ≫ f) b.asHom (by simpa using hab.symm) with hafIso | hbIso
      · letI : IsIso (a ≫ f) := hafIso
        exact (hf.2.1 (ray_isIso_factors a.asHom f).2).elim
      · exact hbIso
    letI : IsIso b := hbIso
    have hb : b = 1 := ray_endomorphism_eq_id_of_isIso b
    have hag : g = a.asHom ≫ f := by simpa [hb] using hab
    have haIso : IsIso a := by
      rcases hg.2.2 X a.asHom f hag.symm with haIso | hfIso
      · exact haIso
      · exact (hf.2.1 hfIso).elim
    letI : IsIso a := haIso
    have ha : a = 1 := ray_endomorphism_eq_id_of_isIso a
    simpa [ha] using hag.symm
  · rcases hgf with ⟨a, b, hab⟩
    have hbIso : IsIso b := by
      rcases hf.2.2 Y (a ≫ g) b.asHom (by simpa using hab.symm) with hagIso | hbIso
      · letI : IsIso (a ≫ g) := hagIso
        exact (hg.2.1 (ray_isIso_factors a.asHom g).2).elim
      · exact hbIso
    letI : IsIso b := hbIso
    have hb : b = 1 := ray_endomorphism_eq_id_of_isIso b
    have haf : f = a.asHom ≫ g := by simpa [hb] using hab
    have haIso : IsIso a := by
      rcases hf.2.2 X a.asHom g haf.symm with haIso | hgIso
      · exact haIso
      · exact (hg.2.1 hgIso).elim
    letI : IsIso a := haIso
    have ha : a = 1 := ray_endomorphism_eq_id_of_isIso a
    simpa [ha] using haf

/-- A finite ray category has no parallel arrows in its reversed
irreducible-morphism quiver. -/
theorem rayQuiver_hom_subsingleton [IsFiniteRayCategory C]
    (x y : RayVertex C) : Subsingleton (x ⟶ y) := by
  constructor
  intro a b
  apply Subtype.ext
  exact irreducible_eq_of_same_endpoints a.property b.property

/-- Targets distinguish outgoing irreducible arrows. -/
theorem outgoingQuiverArrow_fst_injective [IsFiniteRayCategory C]
    (x : RayVertex C) :
    Function.Injective (fun a : OutgoingQuiverArrow x ↦ a.1) := by
  intro a b h
  rcases a with ⟨y, a⟩
  rcases b with ⟨z, b⟩
  dsimp at h
  subst z
  have hab : a = b := (rayQuiver_hom_subsingleton x y).allEq a b
  subst b
  rfl

/-- Sources distinguish incoming irreducible arrows. -/
theorem incomingQuiverArrow_fst_injective [IsFiniteRayCategory C]
    (z : RayVertex C) :
    Function.Injective (fun a : IncomingQuiverArrow z ↦ a.1) := by
  intro a b h
  rcases a with ⟨x, a⟩
  rcases b with ⟨y, b⟩
  dsimp at h
  subst y
  have hab : a = b := (rayQuiver_hom_subsingleton x z).allEq a b
  subst b
  rfl

end LargeIndecomposable
