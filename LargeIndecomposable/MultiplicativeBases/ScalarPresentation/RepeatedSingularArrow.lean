module

public import LargeIndecomposable.RayCategories.Distributive.BGRSRayPathLift
public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [hlinear : Linear k C]
variable [hlocal : ∀ X : C, IsLocalRing (End X)]
variable [hartinian : ∀ X : C, IsArtinianRing (End X)]
variable [hdistributive : HasBGRSDistributiveHomStructure k C]

include k hlinear hlocal hartinian hdistributive

/-- If two consecutive morphisms lie in the same endomorphism ray, changing
both representatives preserves the ray of their ordinary composite.  The
point is that the sole middle unit can be moved through one of the two copies
using transit-or-cotransit. -/
theorem unitRayEquivalent_square_of_same_ray
    {X : C} (f f₁ f₂ : End X) (hf : f ≠ 0)
    (h₁ : UnitRayEquivalent f f₁)
    (h₂ : UnitRayEquivalent f f₂) :
    UnitRayEquivalent (f ≫ f) (f₁ ≫ f₂) := by
  rcases h₁ with ⟨a, b, rfl⟩
  rcases h₂ with ⟨c, d, rfl⟩
  let m : End X := b.hom ≫ c.hom
  haveI : IsIso m := by
    dsimp [m]
    infer_instance
  have hm : IsUnit m := (isUnit_iff_isIso m).2 inferInstance
  have hmiddle : UnitRayEquivalent (f ≫ f) ((f ≫ m.asHom) ≫ f) := by
    rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) f with htransit | hcotransit
    · exact unitRayEquivalent_middleUnit_of_allowsTransit_right
        hf htransit m hm
    · exact unitRayEquivalent_middleUnit_of_allowsCotransit_left
        hf hcotransit m hm
  rcases hmiddle with ⟨p, q, hpq⟩
  refine ⟨a.trans p, q.trans d, ?_⟩
  dsimp [m] at hpq ⊢
  calc
    (a.hom ≫ f ≫ b.hom) ≫ (c.hom ≫ f ≫ d.hom) =
        a.hom ≫ ((f ≫ (b.hom ≫ c.hom)) ≫ f) ≫ d.hom := by
      simp only [Category.assoc]
    _ = a.hom ≫ (p.hom ≫ (f ≫ f) ≫ q.hom) ≫ d.hom := by
      rw [hpq]
    _ = (a.trans p).hom ≫ (f ≫ f) ≫ (q.trans d).hom := by
      simp only [Iso.trans_hom, Category.assoc]

/-- Consequently, for a fixed nonzero endomorphism ray, either every pair of
representatives composes to zero or none does.  A singular length-two path
therefore cannot repeat the same arrow. -/
theorem comp_eq_zero_iff_of_four_same_endomorphism_rays
    {X : C} (f f₁ f₂ g₁ g₂ : End X) (hf : f ≠ 0)
    (hf₁ : UnitRayEquivalent f f₁)
    (hf₂ : UnitRayEquivalent f f₂)
    (hg₁ : UnitRayEquivalent f g₁)
    (hg₂ : UnitRayEquivalent f g₂) :
    f₁ ≫ f₂ = 0 ↔ g₁ ≫ g₂ = 0 := by
  have hfcomp := unitRayEquivalent_square_of_same_ray
    (k := k) f f₁ f₂ hf hf₁ hf₂
  have hgcomp := unitRayEquivalent_square_of_same_ray
    (k := k) f g₁ g₂ hf hg₁ hg₂
  have hfray : unitRay (f ≫ f) = unitRay (f₁ ≫ f₂) :=
    (unitRay_eq_iff _ _).2 hfcomp
  have hgray : unitRay (f ≫ f) = unitRay (g₁ ≫ g₂) :=
    (unitRay_eq_iff _ _).2 hgcomp
  constructor
  · intro hzero
    apply (unitRay_eq_zero_iff (g₁ ≫ g₂)).1
    rw [← hgray, hfray, hzero]
    rfl
  · intro hzero
    apply (unitRay_eq_zero_iff (f₁ ≫ f₂)).1
    rw [← hfray, hgray, hzero]
    rfl

section RayArrow

variable [hpair : HasBGRSPairDichotomy C]

include hpair

/-- The "two arrows are distinct" clause needed by simultaneous singular
normalization is already forced by distributivity: a repeated loop arrow has
the same zero/nonzero composite status for every choice of its two
representatives. -/
theorem repeatedRayArrow_not_singular
    {i : RayVertex (BGRSRayCategory C)} (a : i ⟶ i) :
    ¬(rayPathMap (a.toPath.comp a.toPath) = 0 ∧
      ∃ (f g : End i.obj.as),
        unitRay f = a.1 ∧ unitRay g = a.1 ∧ f ≫ g ≠ 0) := by
  rintro ⟨hray, f, g, hf, hg, hfg⟩
  have hcomp : a.1 ≫ a.1 = 0 := by
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp,
      rayPathMap_toPath, rayArrowMorphism] using hray
  change bgrsRayComp a.1 a.1 = 0 at hcomp
  let r : End i.obj.as := a.1.out
  have hra : unitRay r = a.1 := unitRay_out a.1
  have hr0 : r ≠ 0 := by
    intro hr
    have hrayzero : unitRay r = 0 :=
      (unitRay_eq_zero_iff r).2 hr
    rw [hra] at hrayzero
    exact a.2.1 hrayzero
  have hspecial : IsBGRSSpecialZero r r := by
    by_contra hnot
    have hordinary : r ≫ r ≠ 0 :=
      (HasBGRSPairDichotomy.pair r r).nonzero_common_ray_of_not_special
        hnot r r
        ((unitRay_eq_iff r r).1 rfl)
        ((unitRay_eq_iff r r).1 rfl) |>.1
    have hproductRay : unitRay (bgrsRayRepresentativeProduct r r) = 0 := by
      calc
        unitRay (bgrsRayRepresentativeProduct r r) =
            bgrsRayComp (unitRay r) (unitRay r) := rfl
        _ = bgrsRayComp a.1 a.1 := by rw [hra]
        _ = 0 := hcomp
    have hproductZero : bgrsRayRepresentativeProduct r r = 0 :=
      (unitRay_eq_zero_iff _).1 hproductRay
    rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hnot]
      at hproductZero
    exact hordinary hproductZero
  obtain ⟨fzero, gzero, hfzero, hgzero, hzero⟩ :=
    (HasBGRSPairDichotomy.pair r r).zero_representatives_of_special
      hspecial
  have hrf : UnitRayEquivalent r f :=
    (unitRay_eq_iff r f).1 (hra.trans hf.symm)
  have hrg : UnitRayEquivalent r g :=
    (unitRay_eq_iff r g).1 (hra.trans hg.symm)
  have hforced : f ≫ g = 0 :=
    (comp_eq_zero_iff_of_four_same_endomorphism_rays
      (k := k) r fzero gzero f g hr0 hfzero hgzero hrf hrg).1 hzero
  exact hfg hforced

/-- A packaged arrow type lets the distinctness conclusion be stated even
when the two consecutive arrows initially have different endpoint types. -/
abbrev PackedRayArrow :=
  Σ i : RayVertex (BGRSRayCategory C),
    Σ j : RayVertex (BGRSRayCategory C), (i ⟶ j)

def packRayArrow
    {i j : RayVertex (BGRSRayCategory C)} (a : i ⟶ j) :
    PackedRayArrow (C := C) :=
  ⟨i, j, a⟩

/-- Exact packaged form of the distinct-arrow conclusion for singular
length-two paths. -/
theorem singularPair_packedArrows_ne
    {i j l : RayVertex (BGRSRayCategory C)}
    (a : i ⟶ j) (b : j ⟶ l)
    (hsingular : rayPathMap (a.toPath.comp b.toPath) = 0 ∧
      ∃ (first : j.obj.as ⟶ i.obj.as)
        (second : l.obj.as ⟶ j.obj.as),
        unitRay first = a.1 ∧ unitRay second = b.1 ∧
          second ≫ first ≠ 0) :
    packRayArrow a ≠ packRayArrow b := by
  intro heq
  cases heq
  apply repeatedRayArrow_not_singular (k := k) a
  refine ⟨hsingular.1, ?_⟩
  obtain ⟨first, second, hfirst, hsecond, hnonzero⟩ := hsingular.2
  exact ⟨second, first, hsecond, hfirst, hnonzero⟩

end RayArrow

end LargeIndecomposable
