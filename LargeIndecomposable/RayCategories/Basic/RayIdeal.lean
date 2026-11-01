module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayFinite

/-!
# Rays of composites

In a category with a well-defined BGRS ray product and Artinian endomorphism
rings, the ray of a nonzero composite `f ≫ g` is a left multiple of the ray of
`g` and a right multiple of the ray of `f`: the composite can be rewritten
with a non-special pair (`RayCat.unitRay_comp_eq_left`,
`RayCat.unitRay_comp_eq_right`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable

universe u v

namespace RayCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The mirror of `exists_nonspecial_middle_factor_of_comp`: a nonzero composite has a
non-special factorization with the same left factor. -/
theorem exists_nonspecial_right_of_comp {X Y Z : C} [IsArtinianRing (End Y)]
    (f : X ⟶ Y) (g₀ : Y ⟶ Z) (hf : f ≫ g₀ ≠ 0) :
    ∃ g : Y ⟶ Z, f ≫ g₀ = f ≫ g ∧ ¬IsBGRSSpecialZero f g := by
  by_contra hnone
  push Not at hnone
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hn
  have hiter : ∀ m : ℕ, ∃ (a : End Y) (g : Y ⟶ Z),
      a ∈ (Ring.jacobson (End Y)) ^ m ∧ g = a.asHom ≫ g₀ ∧ f ≫ g₀ = f ≫ g := by
    intro m
    induction m with
    | zero =>
        refine ⟨1, g₀, ?_, ?_, rfl⟩
        · rw [Submodule.pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        · simp
    | succ m ih =>
        rcases ih with ⟨a, g, ha, rfl, hfg⟩
        rcases hnone (a.asHom ≫ g₀) hfg with ⟨rho, hrho⟩
        refine ⟨a * rho.1, rho.1.asHom ≫ a.asHom ≫ g₀, ?_, ?_, ?_⟩
        · rw [Submodule.pow_succ]
          exact Submodule.mul_mem_mul ha rho.2
        · rw [End.mul_def, Category.assoc]
        · rw [hfg, hrho, Category.assoc]
  rcases hiter n with ⟨a, g, ha, hg, hfg⟩
  rw [hn] at ha
  have ha0 : a = 0 := (Submodule.mem_bot (R := End Y)).1 ha
  apply hf
  rw [hfg, hg, ha0]
  change f ≫ ((0 : Y ⟶ Y) ≫ g₀) = 0
  simp

variable [HasWellDefinedBGRSRayProduct C]

/-- **The ray of a composite is a left multiple of the ray of the second factor.** -/
theorem unitRay_comp_eq_left {X Y Z : C} [IsArtinianRing (End Y)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : f ≫ g ≠ 0) :
    ∃ ρ : (BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y),
      (unitRay (f ≫ g) : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Z) =
        ρ ≫ (unitRay g : BGRSRayCategory.mk Y ⟶ BGRSRayCategory.mk Z) := by
  obtain ⟨f', hf', hns⟩ := exists_nonspecial_middle_factor_of_comp f g hfg rfl
  refine ⟨unitRay f', ?_⟩
  rw [BGRSRayCategory.comp_unitRay, bgrsRayRepresentativeProduct_eq_comp_of_not_special hns, hf']

/-- **The ray of a composite is a right multiple of the ray of the first factor.** -/
theorem unitRay_comp_eq_right {X Y Z : C} [IsArtinianRing (End Y)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : f ≫ g ≠ 0) :
    ∃ ρ : (BGRSRayCategory.mk Y ⟶ BGRSRayCategory.mk Z),
      (unitRay (f ≫ g) : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Z) =
        (unitRay f : BGRSRayCategory.mk X ⟶ BGRSRayCategory.mk Y) ≫ ρ := by
  obtain ⟨g', hg', hns⟩ := exists_nonspecial_right_of_comp f g hfg
  refine ⟨unitRay g', ?_⟩
  rw [BGRSRayCategory.comp_unitRay, bgrsRayRepresentativeProduct_eq_comp_of_not_special hns, hg']

end RayCat

end LargeIndecomposable
