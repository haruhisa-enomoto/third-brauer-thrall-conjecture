module

public import LargeIndecomposable.RayCategories.Distributive.DistributiveHomStructure
public import LargeIndecomposable.RayCategories.ClosedChains.RayCrownClosedChain

@[expose] public section

/-!
# The finite-category attachment for the BGRS ray product

This file isolates the representative-level inputs needed to transport
factorization comparability and cancellation to the BGRS ray category, derives
both from distributive Hom structure and Artinian endpoint rings, then packages
the generic finite-ray-category consequences.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v w

/-- Inclusion of principal two-sided spans is realized, up to source and target
units, by one nested BGRS product. -/
class HasBGRSRaySpanFactorizations
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  factor_of_span_le : ∀ {X Y : C} (f g : X ⟶ Y),
    twoSidedEndomorphismSpan k f ≤ twoSidedEndomorphismSpan k g →
      ∃ (a : End X) (b : End Y),
        UnitRayEquivalent f
          (bgrsRayRepresentativeProduct
            (bgrsRayRepresentativeProduct a g) b)

/-- Nonzero cancellation for the representative-level BGRS product, stated
only up to two-sided source and target units. -/
class HasBGRSRayRepresentativeCancellation
    (C : Type u) [Category.{v} C] [Preadditive C] : Prop where
  cancel_right : ∀ {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z),
    UnitRayEquivalent
        (bgrsRayRepresentativeProduct f h)
        (bgrsRayRepresentativeProduct g h) →
      bgrsRayRepresentativeProduct f h ≠ 0 →
        UnitRayEquivalent f g
  cancel_left : ∀ {X Y Z : C} (h : X ⟶ Y) (f g : Y ⟶ Z),
    UnitRayEquivalent
        (bgrsRayRepresentativeProduct h f)
        (bgrsRayRepresentativeProduct h g) →
      bgrsRayRepresentativeProduct h f ≠ 0 →
        UnitRayEquivalent f g

private theorem bgrsFactorization_exists_comp_of_mem_span_of_allowsTransit
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsTransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ b : End Y, g = f ≫ b.asHom := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht a
      refine ⟨b * c, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom = f ≫ (b * c).asHom
      rw [hc, End.mul_def, Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = f ≫ (0 : Y ⟶ Y)
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (f ≫ a.asHom) + (f ≫ b.asHom) =
        f ≫ (a.asHom + b.asHom)
      rw [Preadditive.comp_add]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (f ≫ a.asHom) = f ≫ (c • a.asHom)
      rw [Linear.comp_smul]

private theorem bgrsFactorization_exists_comp_of_mem_span_of_allowsCotransit
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    {X Y : C} {f g : X ⟶ Y} (ht : AllowsCotransit f)
    (hg : g ∈ twoSidedEndomorphismSpan k f) :
    ∃ a : End X, g = a.asHom ≫ f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, b, rfl⟩
      obtain ⟨c, hc⟩ := ht b
      refine ⟨a.asHom ≫ c.asHom, ?_⟩
      change (a.asHom ≫ f) ≫ b.asHom =
        (a.asHom ≫ c.asHom) ≫ f
      rw [Category.assoc, hc]
      simp only [Category.assoc]
  | zero =>
      refine ⟨0, ?_⟩
      change (0 : X ⟶ Y) = (0 : X ⟶ X) ≫ f
      simp
  | add g h _ _ hg hh =>
      rcases hg with ⟨a, rfl⟩
      rcases hh with ⟨b, rfl⟩
      refine ⟨a + b, ?_⟩
      change (a.asHom ≫ f) + (b.asHom ≫ f) =
        (a.asHom + b.asHom) ≫ f
      rw [Preadditive.add_comp]
  | smul c g _ hg =>
      rcases hg with ⟨a, rfl⟩
      refine ⟨c • a, ?_⟩
      change c • (a.asHom ≫ f) = (c • a.asHom) ≫ f
      rw [Linear.smul_comp]

private theorem exists_nonspecial_right_factor
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [IsArtinianRing (End Y)]
    {f g : X ⟶ Y} (hf : f ≠ 0) (b₀ : End Y)
    (hfg : f = g ≫ b₀.asHom) :
    ∃ b : End Y, f = g ≫ b.asHom ∧
      ¬ IsBGRSSpecialZero g b.asHom := by
  by_contra hnone
  push Not at hnone
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hn
  have hiter : ∀ m : ℕ, ∃ b : End Y,
      b ∈ (Ring.jacobson (End Y)) ^ m ∧ f = g ≫ b.asHom := by
    intro m
    induction m with
    | zero =>
        refine ⟨b₀, ?_, hfg⟩
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ m ih =>
        rcases ih with ⟨b, hb, hfb⟩
        have hs : IsBGRSSpecialZero g b.asHom := hnone b hfb
        rcases hs with ⟨ρ, hρ⟩
        refine ⟨b * ρ.1, ?_, ?_⟩
        · rw [Submodule.pow_succ]
          exact Ideal.mul_mem_mul hb ρ.2
        · calc
            f = g ≫ b.asHom := hfb
            _ = (g ≫ ρ.1.asHom) ≫ b.asHom := hρ
            _ = g ≫ (b * ρ.1).asHom := by
              rw [End.mul_def, Category.assoc]
  rcases hiter n with ⟨b, hb, hfb⟩
  rw [hn] at hb
  have hb0 : b = 0 := (Submodule.mem_bot (R := End Y)).1 hb
  apply hf
  have hb0hom : b.asHom = (0 : Y ⟶ Y) := congrArg End.asHom hb0
  calc
    f = g ≫ b.asHom := hfb
    _ = g ≫ (0 : Y ⟶ Y) := by rw [hb0hom]
    _ = 0 := comp_zero

private theorem exists_nonspecial_left_factor
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y : C} [IsArtinianRing (End X)]
    {f g : X ⟶ Y} (hf : f ≠ 0) (a₀ : End X)
    (hfg : f = a₀.asHom ≫ g) :
    ∃ a : End X, f = a.asHom ≫ g ∧
      ¬ IsBGRSSpecialZero a.asHom g := by
  by_contra hnone
  push Not at hnone
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End X)
  rw [Ideal.jacobson_bot] at hn
  have hiter : ∀ m : ℕ, ∃ a : End X,
      a ∈ (Ring.jacobson (End X)) ^ m ∧ f = a.asHom ≫ g := by
    intro m
    induction m with
    | zero =>
        refine ⟨a₀, ?_, hfg⟩
        rw [Submodule.pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
    | succ m ih =>
        rcases ih with ⟨a, ha, hfa⟩
        have hs : IsBGRSSpecialZero a.asHom g := hnone a hfa
        rcases hs with ⟨ρ, hρ⟩
        refine ⟨ρ.1 * a, ?_, ?_⟩
        · rw [Ideal.IsTwoSided.pow_succ]
          exact Ideal.mul_mem_mul ρ.2 ha
        · calc
            f = a.asHom ≫ g := hfa
            _ = (a.asHom ≫ ρ.1.asHom) ≫ g := hρ
            _ = (ρ.1 * a).asHom ≫ g := by
              rw [End.mul_def]
  rcases hiter n with ⟨a, ha, hfa⟩
  rw [hn] at ha
  have ha0 : a = 0 := (Submodule.mem_bot (R := End X)).1 ha
  apply hf
  have ha0hom : a.asHom = (0 : X ⟶ X) := congrArg End.asHom ha0
  calc
    f = a.asHom ≫ g := hfa
    _ = (0 : X ⟶ X) ≫ g := by rw [ha0hom]
    _ = 0 := zero_comp

/-- Any nonzero ordinary factorization can be adjusted at its middle object
so that the same right factor forms a nonexceptional BGRS pair.  Repeatedly
absorbing a hypothetical exceptional radical insertion into the left factor
would eventually put that factor in a zero power of the middle Jacobson
radical, contradicting nonvanishing.  This is the representative-level core
of the stable-path refinement used in BGRS 2.2. -/
theorem exists_nonspecial_middle_factor_of_comp
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X Y Z : C} [IsArtinianRing (End Y)]
    {f : X ⟶ Z} (g₀ : X ⟶ Y) (h : Y ⟶ Z)
    (hf : f ≠ 0) (hfactor : f = g₀ ≫ h) :
    ∃ g : X ⟶ Y, f = g ≫ h ∧ ¬IsBGRSSpecialZero g h := by
  by_contra hnone
  push Not at hnone
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := End Y)
  rw [Ideal.jacobson_bot] at hn
  have hiter : ∀ m : ℕ, ∃ (a : End Y) (g : X ⟶ Y),
      a ∈ (Ring.jacobson (End Y)) ^ m ∧
        g = g₀ ≫ a.asHom ∧ f = g ≫ h := by
    intro m
    induction m with
    | zero =>
        refine ⟨1, g₀, ?_, ?_, hfactor⟩
        · rw [Submodule.pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        · simp
    | succ m ih =>
        rcases ih with ⟨a, g, ha, rfl, hgh⟩
        have hs : IsBGRSSpecialZero (g₀ ≫ a.asHom) h :=
          hnone (g₀ ≫ a.asHom) hgh
        rcases hs with ⟨rho, hrho⟩
        refine ⟨rho.1 * a, (g₀ ≫ a.asHom) ≫ rho.1.asHom, ?_, ?_, ?_⟩
        · rw [Ideal.IsTwoSided.pow_succ]
          exact Ideal.mul_mem_mul rho.2 ha
        · rw [End.mul_def, Category.assoc]
        · exact hgh.trans hrho
  rcases hiter n with ⟨a, g, ha, hg, hfg⟩
  rw [hn] at ha
  have ha0 : a = 0 := (Submodule.mem_bot (R := End Y)).1 ha
  apply hf
  rw [hfg, hg, ha0]
  change (g₀ ≫ (0 : Y ⟶ Y)) ≫ h = 0
  simp

/-- A nonzero morphism lying in the principal span of a transit generator
has a right-endomorphism factorization whose BGRS product is nonspecial. -/
theorem exists_nonspecial_right_factor_of_mem_span_of_allowsTransit
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    {X Y : C} [IsArtinianRing (End Y)]
    {f g : X ⟶ Y} (hf : f ≠ 0) (hg : AllowsTransit g)
    (hmem : f ∈ twoSidedEndomorphismSpan k g) :
    ∃ b : End Y, f = g ≫ b.asHom ∧
      ¬IsBGRSSpecialZero g b.asHom := by
  obtain ⟨b₀, hfb₀⟩ :=
    bgrsFactorization_exists_comp_of_mem_span_of_allowsTransit hg hmem
  exact exists_nonspecial_right_factor hf b₀ hfb₀

/-- The cotransit dual: a nonzero morphism in the generator span has a
nonspecial left-endomorphism factorization. -/
theorem exists_nonspecial_left_factor_of_mem_span_of_allowsCotransit
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    {X Y : C} [IsArtinianRing (End X)]
    {f g : X ⟶ Y} (hf : f ≠ 0) (hg : AllowsCotransit g)
    (hmem : f ∈ twoSidedEndomorphismSpan k g) :
    ∃ a : End X, f = a.asHom ≫ g ∧
      ¬IsBGRSSpecialZero a.asHom g := by
  obtain ⟨a₀, hfa₀⟩ :=
    bgrsFactorization_exists_comp_of_mem_span_of_allowsCotransit hg hmem
  exact exists_nonspecial_left_factor hf a₀ hfa₀

/-- Distributive Hom structure and Artinian endpoint rings realize principal
span inclusions by nested BGRS products. -/
instance hasBGRSRaySpanFactorizations_of_bgrsDistributiveHomStructure
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C] :
    HasBGRSRaySpanFactorizations k C := by
  constructor
  intro X Y f g hfg
  by_cases hf0 : f = 0
  · subst f
    refine ⟨End.of (0 : X ⟶ X), End.of (𝟙 Y), ?_⟩
    rw [bgrsRayRepresentativeProduct_comp_id,
      bgrsRayRepresentativeProduct_zero_left]
    exact ⟨Iso.refl X, Iso.refl Y, by simp⟩
  · have hfmem : f ∈ twoSidedEndomorphismSpan k g :=
      hfg (mem_twoSidedEndomorphismSpan k f)
    rcases HasBGRSDistributiveHomStructure.transit_or_cotransit
        (k := k) (C := C) g with hgT | hgC
    · obtain ⟨b₀, hfb₀⟩ :=
        bgrsFactorization_exists_comp_of_mem_span_of_allowsTransit hgT hfmem
      obtain ⟨b, hfb, hns⟩ :=
        exists_nonspecial_right_factor hf0 b₀ hfb₀
      refine ⟨𝟙 X, b, ?_⟩
      simp only [bgrsRayRepresentativeProduct_id_comp,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special hns]
      rw [← hfb]
      exact ⟨Iso.refl X, Iso.refl Y, by simp⟩
    · obtain ⟨a₀, hfa₀⟩ :=
        bgrsFactorization_exists_comp_of_mem_span_of_allowsCotransit hgC hfmem
      obtain ⟨a, hfa, hns⟩ :=
        exists_nonspecial_left_factor hf0 a₀ hfa₀
      refine ⟨a, 𝟙 Y, ?_⟩
      simp only [bgrsRayRepresentativeProduct_comp_id,
        bgrsRayRepresentativeProduct_eq_comp_of_not_special hns]
      rw [← hfa]
      exact ⟨Iso.refl X, Iso.refl Y, by simp⟩

/-- Distributive Hom structure and local Artinian endomorphism rings supply
representative-level BGRS cancellation. -/
theorem hasBGRSRayRepresentativeCancellation_of_bgrsDistributiveHomStructure
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [∀ X : C, IsLocalRing (End X)]
    [∀ X : C, IsArtinianRing (End X)]
    [HasBGRSDistributiveHomStructure k C] :
    HasBGRSRayRepresentativeCancellation C where
  cancel_right :=
    bgrsRayRepresentativeProduct_cancel_right_of_bgrsDistributiveHomStructure
      (k := k)
  cancel_left :=
    bgrsRayRepresentativeProduct_cancel_left_of_bgrsDistributiveHomStructure
      (k := k)

namespace BGRSRayCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- Representative-level BGRS cancellation descends to nonzero cancellation
in the BGRS ray category. -/
instance hasRayCancellation_of_representativeCancellation
    [HasBGRSRayRepresentativeCancellation C] :
    HasRayCancellation (BGRSRayCategory C) where
  cancel_right := by
    intro X Y Z f g h heq hn
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    rcases Z with ⟨Z⟩
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h =>
          apply (unitRay_eq_iff _ _).2
          apply HasBGRSRayRepresentativeCancellation.cancel_right f g h
          · apply (unitRay_eq_iff _ _).1
            exact heq
          · apply (unitRay_ne_zero_iff _).1
            exact hn
  cancel_left := by
    intro X Y Z h f g heq hn
    rcases X with ⟨X⟩
    rcases Y with ⟨Y⟩
    rcases Z with ⟨Z⟩
    induction h using Quotient.inductionOn with
    | _ h =>
      induction f using Quotient.inductionOn with
      | _ f =>
        induction g using Quotient.inductionOn with
        | _ g =>
          apply (unitRay_eq_iff _ _).2
          apply HasBGRSRayRepresentativeCancellation.cancel_left h f g
          · apply (unitRay_eq_iff _ _).1
            exact heq
          · apply (unitRay_ne_zero_iff _).1
            exact hn

/-- Comparable principal spans, together with realization of span inclusions
by BGRS products, give the two-sided factorization comparability axiom in the
BGRS ray category. -/
theorem factorization_comparable_of_spans
    {k : Type w} [Field k] [Linear k C]
    [HasClassifyingComparableUnitRaySpans k C]
    [HasBGRSRaySpanFactorizations k C]
    {X Y : BGRSRayCategory C} (f g : X ⟶ Y) :
    TwoSidedEndomorphismFactors f g ∨
      TwoSidedEndomorphismFactors g f := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      rcases HasClassifyingComparableUnitRaySpans.span_comparable
          (k := k) (C := C) (unitRay f) (unitRay g) with hfg | hgf
      · rcases HasBGRSRaySpanFactorizations.factor_of_span_le
            (k := k) (C := C) f g (by simpa using hfg) with ⟨a, b, h⟩
        exact Or.inr ⟨unitRay a, unitRay b, (unitRay_eq_iff _ _).2 h⟩
      · rcases HasBGRSRaySpanFactorizations.factor_of_span_le
            (k := k) (C := C) g f (by simpa using hgf) with ⟨a, b, h⟩
        exact Or.inl ⟨unitRay a, unitRay b, (unitRay_eq_iff _ _).2 h⟩

/-- Assemble the finite-ray-category structure on a BGRS ray category.

The nilpotence and source-stabilizer fields are consequences of finite Hom
sets, cancellation, and the already transported identity and skeletality
facts; they are not additional source hypotheses. -/
theorem isFiniteRayCategory
    {k : Type w} [Field k] [Linear k C]
    [HasClassifyingComparableUnitRaySpans k C]
    [HasBGRSRaySpanFactorizations k C]
    [HasBGRSRayRepresentativeCancellation C]
    (hid : ∀ X : C, (𝟙 X : X ⟶ X) ≠ 0)
    (hfinite : ∀ X Y : C, Finite (UnitRayOrbit X Y))
    (hskel : Skeletal C) :
    IsFiniteRayCategory (BGRSRayCategory C) where
  id_ne_zero X := by
    change unitRay (𝟙 X.as) ≠ (0 : UnitRayOrbit X.as X.as)
    exact (unitRay_ne_zero_iff (𝟙 X.as)).2 (hid X.as)
  hom_finite X Y := hfinite X.as Y.as
  endomorphism_nilpotent := by
    intro X f hf
    letI : Finite (End X) := hfinite X.as X.as
    apply endomorphism_nilpotent_of_finite_of_rayCancellation
      (X := X) (f := f)
    · change unitRay (𝟙 X.as) ≠ (0 : UnitRayOrbit X.as X.as)
      exact (unitRay_ne_zero_iff (𝟙 X.as)).2 (hid X.as)
    · intro a _
      rcases X with ⟨X⟩
      exact BGRSRayCategory.end_eq_id_of_isIso hid a
    · exact hf
  skeletal := by
    intro X Y hXY
    exact BGRSRayCategory.skeletal hid hskel hXY
  factorization_comparable :=
    factorization_comparable_of_spans (k := k)
  source_stabilizer_trivial := by
    intro X Y Z f g a hfg heq
    exact source_stabilizer_trivial_of_rayCancellation f g a hfg heq

end BGRSRayCategory

end LargeIndecomposable
