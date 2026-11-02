module

public import LargeIndecomposable.RayCategories.Distributive.LinearizationRepresentationFinite
public import LargeIndecomposable.RayCategories.Quotients.RayIdealSpan
public import LargeIndecomposable.RayCategories.Quotients.ResidueQuiver

/-!
# Ray presentations of quotients (B5)

For split basic data `S` of `B` and a two-sided ideal `K ⊆ rad B`, corners,
corner units, rays and insertion spans of `B` map into those of `B / K`, and
corner elements, units and radical corner elements of `B / K` lift.

For a nonzero non-invertible `τ` of the small ray category `P` of a
distributive `B`, with representative `t`, a morphism of `P` factors through
`τ` iff its representative lies in `(t)` (`repP_mem_idealOf_iff`), and the ray
table of the residue category `P/τ` presents `B / (t)` (`isRayPres_res`).
Hence `k(P/τ)` is representation-finite when `B / (t)` is
(`isRepresentationFinite_res`), in every characteristic.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits LargeIndecomposable RayQuiver RayCat RayCat.RaySmall
  LargeIndecomposable

universe u

namespace SplitBasicData

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)
  (K : TwoSidedIdeal B) (hK : K.asIdeal ≤ Ring.jacobson B)

/-- The quotient map. -/
abbrev qmk : B →ₐ[k] B ⧸ K.asIdeal := Ideal.Quotient.mkₐ k K.asIdeal

section QuotLemmas

include hK

lemma quot_primitiveIdempotents_e (i : Fin S.primitiveIdempotents.m) : (S.quotient K hK).primitiveIdempotents.e i = qmk (k := k) K (S.primitiveIdempotents.e i) := rfl

lemma qmk_corner {i j : Fin S.primitiveIdempotents.m} {a : B} (ha : a ∈ S.primitiveIdempotents.corner (k := k) i j) :
    qmk (k := k) K a ∈ (S.quotient K hK).primitiveIdempotents.corner (k := k) i j := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨qmk (k := k) K r, by simp [quot_primitiveIdempotents_e]⟩

lemma qmk_radical {a : B} (ha : a ∈ algebraRadical k B) :
    qmk (k := k) K a ∈ algebraRadical k (B ⧸ K.asIdeal) :=
  mk_mem_jacobson K hK ha

lemma qmk_cornerRadical {i : Fin S.primitiveIdempotents.m} {a : B} (ha : a ∈ S.primitiveIdempotents.cornerRadical (k := k) i) :
    qmk (k := k) K a ∈ (S.quotient K hK).primitiveIdempotents.cornerRadical (k := k) i :=
  ⟨S.qmk_corner K hK ha.1, qmk_radical K hK ha.2⟩

lemma qmk_unit {i : Fin S.primitiveIdempotents.m} {u : B} (hu : S.primitiveIdempotents.IsCornerUnit (k := k) i u) :
    (S.quotient K hK).primitiveIdempotents.IsCornerUnit (k := k) i (qmk (k := k) K u) := by
  obtain ⟨hu, u', hu', h1, h2⟩ := hu
  exact ⟨S.qmk_corner K hK hu, qmk (k := k) K u', S.qmk_corner K hK hu',
    by rw [← map_mul, h1]; rfl, by rw [← map_mul, h2]; rfl⟩

lemma qmk_ray {i j : Fin S.primitiveIdempotents.m} {f g : B} (hg : g ∈ S.primitiveIdempotents.ray (k := k) i j f) :
    qmk (k := k) K g ∈ (S.quotient K hK).primitiveIdempotents.ray (k := k) i j (qmk (k := k) K f) := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hg
  exact ⟨qmk (k := k) K u, qmk (k := k) K w, S.qmk_unit K hK hu, S.qmk_unit K hK hw, by simp only [map_mul]⟩

lemma qmk_insertionSpan {i j l : Fin S.primitiveIdempotents.m} {f h g : B}
    (hg : g ∈ S.primitiveIdempotents.insertionSpan (k := k) i j l f h) :
    qmk (k := k) K g ∈ (S.quotient K hK).primitiveIdempotents.insertionSpan (k := k) i j l (qmk (k := k) K f) (qmk (k := k) K h) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, ha, r, hr, b, hb, rfl⟩ := hg
      exact Submodule.subset_span ⟨qmk (k := k) K a, S.qmk_corner K hK ha, qmk (k := k) K r,
        S.qmk_cornerRadical K hK hr, qmk (k := k) K b, S.qmk_corner K hK hb, by simp only [map_mul]⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add g g' _ _ hg hg' => rw [map_add]; exact Submodule.add_mem _ hg hg'
  | smul c g _ hg => rw [map_smul]; exact Submodule.smul_mem _ c hg

/-- **Corner elements lift.** -/
lemma lift_corner {i j : Fin S.primitiveIdempotents.m} {a' : B ⧸ K.asIdeal}
    (ha : a' ∈ (S.quotient K hK).primitiveIdempotents.corner (k := k) i j) :
    ∃ a ∈ S.primitiveIdempotents.corner (k := k) i j, qmk (k := k) K a = a' := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a'
  refine ⟨S.primitiveIdempotents.e i * b * S.primitiveIdempotents.e j, ⟨b, by simp [mul_assoc]⟩, ?_⟩
  obtain ⟨r, hr⟩ := ha
  have hei := ((S.quotient K hK).primitiveIdempotents.complete.idem i).eq
  have hej := ((S.quotient K hK).primitiveIdempotents.complete.idem j).eq
  have hb : (S.quotient K hK).primitiveIdempotents.e i * Ideal.Quotient.mk K.asIdeal b *
      (S.quotient K hK).primitiveIdempotents.e j = Ideal.Quotient.mk K.asIdeal b := by
    rw [← hr]
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    simp only [← mul_assoc, hei]
    simp only [mul_assoc, hej]
  rw [← hb]
  simp [quot_primitiveIdempotents_e]

/-- **Radical corner elements lift.** -/
lemma lift_cornerRadical {i : Fin S.primitiveIdempotents.m} {ρ' : B ⧸ K.asIdeal}
    (hρ : ρ' ∈ (S.quotient K hK).primitiveIdempotents.cornerRadical (k := k) i) :
    ∃ ρ ∈ S.primitiveIdempotents.cornerRadical (k := k) i, qmk (k := k) K ρ = ρ' := by
  obtain ⟨j, hj, hjρ⟩ := (mem_jacobson_quotient_iff K hK ρ').1 hρ.2
  refine ⟨S.primitiveIdempotents.e i * j * S.primitiveIdempotents.e i, ⟨⟨j, by simp [mul_assoc]⟩, ?_⟩, ?_⟩
  · exact (Ring.jacobson B).mul_mem_right _ ((Ring.jacobson B).mul_mem_left _ hj)
  · obtain ⟨r, hr⟩ := hρ.1
    have hρ' : (S.quotient K hK).primitiveIdempotents.e i * ρ' * (S.quotient K hK).primitiveIdempotents.e i = ρ' := by
      rw [← hr]
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      simp only [← mul_assoc, ((S.quotient K hK).primitiveIdempotents.complete.idem i).eq]
      simp only [mul_assoc, ((S.quotient K hK).primitiveIdempotents.complete.idem i).eq]
    rw [map_mul, map_mul]
    change (S.quotient K hK).primitiveIdempotents.e i * Ideal.Quotient.mk K.asIdeal j *
      (S.quotient K hK).primitiveIdempotents.e i = ρ'
    rw [hjρ]
    exact hρ'

/-- **Corner units lift.** -/
lemma lift_unit {i : Fin S.primitiveIdempotents.m} {u' : B ⧸ K.asIdeal}
    (hu : (S.quotient K hK).primitiveIdempotents.IsCornerUnit (k := k) i u') :
    ∃ u, S.primitiveIdempotents.IsCornerUnit (k := k) i u ∧ qmk (k := k) K u = u' := by
  obtain ⟨u, hu0, rfl⟩ := S.lift_corner K hK hu.1
  refine ⟨u, S.primitiveIdempotents.isCornerUnit_of_not_mem hu0 fun hrad ↦ ?_, rfl⟩
  apply (S.quotient K hK).primitiveIdempotents.e_not_mem_radical (k := k) i
  obtain ⟨-, u'', -, h1, -⟩ := hu
  rw [← h1]
  exact (Ring.jacobson _).mul_mem_right _ (qmk_radical K hK hrad.2)

end QuotLemmas

section Ideal

variable [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]

/-- **Uniseriality step**: if `f = g + d` with `d` in an ideal `J` that does not contain
`f`, then `g` lies in the ray of `f`. -/
lemma unitRayEquivalent_of_sub_mem (J : TwoSidedIdeal B) {X Y : S.toIdempotents.ProjectiveCategory}
    (f g : X ⟶ Y) (hf : f.1 ∉ J) (hd : (f - g).1 ∈ J) : UnitRayEquivalent f g := by
  by_cases hd0 : f - g = 0
  · have : g = f := (sub_eq_zero.1 hd0).symm
    subst this
    exact ⟨Iso.refl _, Iso.refl _, by simp⟩
  -- the `J`-part of `X ⟶ Y`
  let M : Submodule k (X ⟶ Y) :=
    { carrier := {q | q.1 ∈ J}
      add_mem' := fun ha hb ↦ J.add_mem ha hb
      zero_mem' := J.zero_mem
      smul_mem' := fun c q hq ↦ by
        change (c • q).1 ∈ J
        rw [show (c • q).1 = algebraMap k B c * q.1 from Algebra.smul_def c q.1]
        exact J.mul_mem_left _ _ hq }
  have hM : IsHomSubbimodule M :=
    ⟨fun a q hq ↦ by
      change (a.asHom ≫ q).1 ∈ J
      rw [SplitBasicIdempotents.ProjectiveCategory.comp_val]
      exact J.mul_mem_right _ _ hq,
     fun b q hq ↦ by
      change (q ≫ b.asHom).1 ∈ J
      rw [SplitBasicIdempotents.ProjectiveCategory.comp_val]
      exact J.mul_mem_left _ _ hq⟩
  have hMf : M ≤ twoSidedEndomorphismSpan k f := by
    rcases HasBGRSDistributiveHomStructure.homSubbimodule_comparable (k := k) M
        (twoSidedEndomorphismSpan k f) hM (isHomSubbimodule_twoSidedEndomorphismSpan f) with h | h
    · exact h
    · exact absurd (h (mem_twoSidedEndomorphismSpan k f)) hf
  have hdf : f - g ∈ twoSidedEndomorphismSpan k f := hMf hd
  rcases HasBGRSDistributiveHomStructure.transit_or_cotransit (k := k) f with hT | hC
  · obtain ⟨b, hb, -⟩ := exists_nonspecial_right_factor_of_mem_span_of_allowsTransit hd0 hT hdf
    have hbJ : b ∈ Ring.jacobson (End Y) := by
      rw [mem_ringJacobson_iff_not_isUnit]
      rintro ⟨u, rfl⟩
      apply hf
      have : f = (f - g) ≫ (u⁻¹ : (End Y)ˣ).1.asHom := by
        rw [hb, Category.assoc, ← End.mul_def]
        simp
      rw [this, SplitBasicIdempotents.ProjectiveCategory.comp_val]
      exact J.mul_mem_left _ _ hd
    have hunit : IsUnit (1 - b) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits b
      ((mem_ringJacobson_iff_not_isUnit (R := End Y) b).1 hbJ)
    obtain ⟨u, hu⟩ := hunit
    refine ⟨Iso.refl X, Aut.unitsEndEquivAut Y u, ?_⟩
    change g = 𝟙 X ≫ f ≫ u.1
    rw [hu, Category.id_comp]
    change g = f ≫ (𝟙 Y - b.asHom)
    rw [Preadditive.comp_sub, ← hb, Category.comp_id]
    abel
  · obtain ⟨a, ha, -⟩ := exists_nonspecial_left_factor_of_mem_span_of_allowsCotransit hd0 hC hdf
    have haJ : a ∈ Ring.jacobson (End X) := by
      rw [mem_ringJacobson_iff_not_isUnit]
      rintro ⟨u, rfl⟩
      apply hf
      have : f = (u⁻¹ : (End X)ˣ).1.asHom ≫ (f - g) := by
        rw [ha, ← Category.assoc, ← End.mul_def]
        simp
      rw [this, SplitBasicIdempotents.ProjectiveCategory.comp_val]
      exact J.mul_mem_right _ _ hd
    have hunit : IsUnit (1 - a) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((mem_ringJacobson_iff_not_isUnit (R := End X) a).1 haJ)
    obtain ⟨u, hu⟩ := hunit
    refine ⟨Aut.unitsEndEquivAut X u, Iso.refl Y, ?_⟩
    change g = u.1 ≫ f ≫ 𝟙 Y
    rw [hu, Category.comp_id]
    change g = (𝟙 X - a.asHom) ≫ f
    rw [Preadditive.sub_comp, ← ha, Category.id_comp]
    abel

/-- Unit-ray equivalence preserves membership in an ideal. -/
lemma mem_of_unitRayEquivalent (J : TwoSidedIdeal B) {X Y : S.toIdempotents.ProjectiveCategory}
    {φ ψ : X ⟶ Y} (h : UnitRayEquivalent φ ψ) (hφ : φ.1 ∈ J) : ψ.1 ∈ J := by
  obtain ⟨a, b, rfl⟩ := h
  rw [SplitBasicIdempotents.ProjectiveCategory.comp_val,
    SplitBasicIdempotents.ProjectiveCategory.comp_val]
  exact J.mul_mem_right _ _ (J.mul_mem_left _ _ hφ)

lemma unitRayEquivalent_symm' {X Y : S.toIdempotents.ProjectiveCategory} {φ ψ : X ⟶ Y}
    (h : UnitRayEquivalent φ ψ) : UnitRayEquivalent ψ φ :=
  (unitRay_eq_iff _ _).1 ((unitRay_eq_iff _ _).2 h).symm

/-- **Rays of `B / J` pull back to unit-ray equivalence** for morphisms outside `J`. -/
lemma unitRayEquivalent_of_qmk_mem_ray {X Y : S.toIdempotents.ProjectiveCategory} {φ ψ : X ⟶ Y}
    (hφ : φ.1 ∉ K)
    (h : qmk (k := k) K ψ.1 ∈
      (S.quotient K hK).primitiveIdempotents.ray (k := k) (S.pidx Y) (S.pidx X) (qmk (k := k) K φ.1)) :
    UnitRayEquivalent φ ψ := by
  obtain ⟨u', w', hu', hw', heq⟩ := h
  obtain ⟨u, hu, rfl⟩ := S.lift_unit K hK hu'
  obtain ⟨w, hw, rfl⟩ := S.lift_unit K hK hw'
  have hray : u * φ.1 * w ∈ S.primitiveIdempotents.ray (k := k) (S.pidx Y) (S.pidx X) φ.1 := ⟨u, w, hu, hw, rfl⟩
  let χ : X ⟶ Y := S.ofCorner (u * φ.1 * w) (S.primitiveIdempotents.ray_subset_corner (S.val_mem_corner φ) hray)
  have h1 : UnitRayEquivalent φ χ := (S.unitRayEquivalent_iff φ χ).2 hray
  have hχ : χ.1 ∉ K := fun h ↦ hφ (S.mem_of_unitRayEquivalent K (S.unitRayEquivalent_symm' h1) h)
  have hd : (χ - ψ).1 ∈ K := by
    change χ.1 - ψ.1 ∈ K
    have : Ideal.Quotient.mk K.asIdeal χ.1 = Ideal.Quotient.mk K.asIdeal ψ.1 := by
      change qmk (k := k) K (u * φ.1 * w) = qmk (k := k) K ψ.1
      rw [heq, map_mul, map_mul]
    exact Ideal.Quotient.eq.1 this
  have h2 := S.unitRayEquivalent_of_sub_mem K χ ψ hχ hd
  exact (unitRay_eq_iff _ _).1 (((unitRay_eq_iff _ _).2 h1).trans ((unitRay_eq_iff _ _).2 h2))

/-- A non-invertible endomorphism has radical value. -/
lemma val_mem_jacobson_of_not_isIso {X : S.toIdempotents.ProjectiveCategory} (f : X ⟶ X)
    (hf : ¬IsIso f) : f.1 ∈ Ring.jacobson B := by
  refine (SplitBasicIdempotents.projectiveEnd_mem_jacobson_iff_val_mem_jacobson S.toIdempotents X f).1
    ((mem_ringJacobson_iff_not_isUnit (R := End X) f).2 ?_)
  rintro ⟨u, hu⟩
  apply hf
  subst hu
  exact (Aut.unitsEndEquivAut X u).isIso_hom

end Ideal

section Small

variable [HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory]
  [LocallySmall.{0} S.toIdempotents.RayCategory]
  {x y : RaySmall.{0} S.toIdempotents.RayCategory} (τ : x ⟶ y)

/-- The ideal generated by a representative of `τ`. -/
def idealOf : TwoSidedIdeal B := TwoSidedIdeal.span {(S.repP τ).1}

/-- **Morphisms of the small ray category factoring through `τ` are those whose
representatives lie in the ideal of `τ`.** -/
lemma repP_mem_idealOf_iff {X Y : RaySmall.{0} S.toIdempotents.RayCategory} (f : X ⟶ Y) :
    (S.repP f).1 ∈ S.idealOf τ ↔ FactorsThroughMorphism τ f := by
  constructor
  · intro h
    by_cases hf0 : f = 0
    · exact ⟨0, 0, by rw [hf0]; simp⟩
    have hr0 : S.repP f ≠ 0 := fun h0 ↦ hf0 ((S.repP_eq_zero_iff f).1 h0)
    obtain ⟨α, β, hαβ⟩ := S.ray_factorsThrough_of_mem_span (S.repP τ) (S.repP f) hr0 h
    refine ⟨sh.{0} α, sh.{0} β, ?_⟩
    rw [← (sh.{0}).apply_symm_apply f, ← S.unitRay_repP f]
    change sh.{0} (show X.as ⟶ Y.as from unitRay (S.repP f)) = _
    rw [hαβ, sh_comp, sh_comp, S.unitRay_repP τ, Equiv.apply_symm_apply]
  · rintro ⟨a, b, rfl⟩
    by_cases hf0 : a ≫ τ ≫ b = 0
    · rw [(S.repP_eq_zero_iff _).2 hf0]
      exact (S.idealOf τ).zero_mem
    have hval : ∀ {X' Y' Z' : S.toIdempotents.ProjectiveCategory} (φ : X' ⟶ Y') (ψ : Y' ⟶ Z'),
        φ.1 ∈ S.idealOf τ ∨ ψ.1 ∈ S.idealOf τ →
          (bgrsRayRepresentativeProduct φ ψ).1 ∈ S.idealOf τ := by
      intro X' Y' Z' φ ψ h
      by_cases hs : IsBGRSSpecialZero φ ψ
      · rw [bgrsRayRepresentativeProduct_eq_zero_of_special hs]
        exact (S.idealOf τ).zero_mem
      · rw [bgrsRayRepresentativeProduct_eq_comp_of_not_special hs,
          SplitBasicIdempotents.ProjectiveCategory.comp_val]
        rcases h with h | h
        · exact (S.idealOf τ).mul_mem_left _ _ h
        · exact (S.idealOf τ).mul_mem_right _ _ h
    let N := bgrsRayRepresentativeProduct (S.repP a)
      (bgrsRayRepresentativeProduct (S.repP τ) (S.repP b))
    have hN : N.1 ∈ S.idealOf τ :=
      hval _ _ (Or.inr (hval _ _ (Or.inl (TwoSidedIdeal.subset_span rfl))))
    have hray : (unitRay N : X.as ⟶ Y.as) = unitRay (S.repP (a ≫ τ ≫ b)) := by
      have h2 : (unitRay (bgrsRayRepresentativeProduct (S.repP τ) (S.repP b)) : x.as ⟶ Y.as) =
          unitRay (S.repP (τ ≫ b)) := by
        rw [S.unitRay_repP, S.sh_symm_comp_repP]
      rw [S.unitRay_repP, S.sh_symm_comp_repP]
      exact (unitRay_eq_iff _ _).2 (bgrsRayRepresentativeProduct_unitRayEquivalent
        ((unitRay_eq_iff _ _).1 rfl) ((unitRay_eq_iff _ _).1 h2))
    obtain ⟨u, w, huw⟩ := (unitRay_eq_iff _ _).1 hray
    rw [huw, SplitBasicIdempotents.ProjectiveCategory.comp_val,
      SplitBasicIdempotents.ProjectiveCategory.comp_val]
    exact (S.idealOf τ).mul_mem_right _ _ ((S.idealOf τ).mul_mem_left _ _ hN)

/-- **The ideal of a non-invertible `τ` lies in the radical.** -/
lemma idealOf_le_jacobson (hτ : ¬IsIso τ) : (S.idealOf τ).asIdeal ≤ Ring.jacobson B := by
  have hrad : (S.repP τ).1 ∈ Ring.jacobson B := by
    obtain ⟨⟨x⟩⟩ := x
    obtain ⟨⟨y⟩⟩ := y
    by_cases hxy : x = y
    swap
    · exact SplitBasicIdempotents.ProjectiveCategory.offDiagonal_val_mem_jacobson S.toIdempotents hxy _
    subst hxy
    refine S.val_mem_jacobson_of_not_isIso (S.repP τ) fun hiso ↦ ?_
    apply hτ
    have h1 : UnitRayEquivalent (𝟙 _) (S.repP τ) :=
      ⟨Iso.refl _, asIso (S.repP τ), by simp⟩
    have h2 : τ = 𝟙 _ := by
      rw [← (sh.{0}).apply_symm_apply τ, ← S.unitRay_repP, ← (unitRay_eq_iff _ _).2 h1]
      rfl
    rw [h2]
    infer_instance
  intro z hz
  have hle : S.idealOf τ ≤ (Ring.jacobson B).toTwoSided :=
    TwoSidedIdeal.span_le.2 (by rintro _ rfl; exact Ideal.mem_toTwoSided.2 hrad)
  exact Ideal.mem_toTwoSided.1 (hle hz)

section Res

variable [IsRayCategory (RaySmall.{0} S.toIdempotents.RayCategory)]
  [Fintype (RaySmall.{0} S.toIdempotents.RayCategory)] [DecidableEq (RaySmall.{0} S.toIdempotents.RayCategory)]

/-- Nonzero corner elements determine their corner. -/
lemma _root_.LargeIndecomposable.SplitBasicData.eq_of_mem_corner' {A : Type*} [Ring A]
    [Algebra k A] [FiniteDimensional k A] (F : PrimitiveIdempotents A) {x y x' y' : Fin F.m} {a : A}
    (ha : a ∈ F.corner (k := k) x y) (ha' : a ∈ F.corner (k := k) x' y') (h0 : a ≠ 0) :
    x = x' ∧ y = y' := by
  have e1 := F.e_mul_of_mem ha
  have e2 := F.e_mul_of_mem ha'
  have e3 := F.mul_e_of_mem ha
  have e4 := F.mul_e_of_mem ha'
  constructor
  · by_contra hxx
    apply h0
    rw [← e1, ← e2, ← mul_assoc, F.complete.ortho hxx, zero_mul]
  · by_contra hyy
    apply h0
    rw [← e3, ← e4, mul_assoc, F.complete.ortho (Ne.symm hyy), mul_zero]

/-- A lift of a morphism of the residue category `P/τ`. -/
def liftQ {X Y : RayResidueCategory τ} (f : X ⟶ Y) : X.as ⟶ Y.as := Quot.out f

lemma resQ_liftQ {X Y : RayResidueCategory τ} (f : X ⟶ Y) :
    (rayResidueFunctor τ).map (S.liftQ τ f) = f :=
  Quot.out_eq f

lemma liftQ_not_ftm {X Y : RayResidueCategory τ} {f : X ⟶ Y} (hf : f ≠ 0) :
    ¬FactorsThroughMorphism τ (S.liftQ τ f) := fun h ↦
  hf (by rw [← S.resQ_liftQ τ f]; exact (rayResidueFunctor_map_eq_zero_iff τ _).2 h)

lemma liftQ_resQ {X Y : RaySmall.{0} S.toIdempotents.RayCategory} (g : X ⟶ Y)
    (hg : ¬FactorsThroughMorphism τ g) : S.liftQ τ ((rayResidueFunctor τ).map g) = g :=
  (RayCat.resF_map_injective τ hg (S.resQ_liftQ τ _).symm).symm

lemma repP_liftQ_not_mem {X Y : RayResidueCategory τ} {f : X ⟶ Y} (hf : f ≠ 0) :
    (S.repP (S.liftQ τ f)).1 ∉ S.idealOf τ := fun h ↦
  S.liftQ_not_ftm τ hf ((S.repP_mem_idealOf_iff τ _).1 h)

/-- The labels of the objects of `P/τ`. -/
def labelQ : RayResidueCategory τ ≃ Fin S.primitiveIdempotents.m :=
  (⟨fun X ↦ X.as, fun X ↦ ⟨X⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ :
    RayResidueCategory τ ≃ RaySmall.{0} S.toIdempotents.RayCategory).trans S.labelEquiv

variable [IsRayCategory (RayResidueCategory τ)] [Fintype (RayResidueCategory τ)]
  [DecidableEq (RayResidueCategory τ)]

/-- The representative in `B / (t)` of a nonzero morphism of `P/τ`. -/
def betaQ (r : NZ (RayResidueCategory τ)) : B ⧸ (S.idealOf τ).asIdeal :=
  qmk (k := k) (S.idealOf τ) (S.repP (S.liftQ τ r.2.2.1)).1

lemma morElt_ne_zero_nzQ (t : NZ (RayResidueCategory τ)) : morElt k t.2.2.1 ≠ 0 := by
  rw [← linBasisR_apply]
  exact (linBasisR k _).ne_zero t

/-- A special pair has its product in the insertion span. -/
lemma mul_mem_insertionSpan_of_special {X Y Z : S.toIdempotents.ProjectiveCategory} (μ : X ⟶ Y)
    (ν : Y ⟶ Z) (hsp : IsBGRSSpecialZero μ ν) :
    ν.1 * μ.1 ∈ S.primitiveIdempotents.insertionSpan (k := k) (S.pidx Z) (S.pidx Y) (S.pidx X) ν.1 μ.1 := by
  obtain ⟨ρ, hρ⟩ := hsp
  have hρv : (ρ.1.asHom : Y ⟶ Y).1 ∈ S.primitiveIdempotents.cornerRadical (k := k) (S.pidx Y) :=
    (S.mem_jacobson_iff ρ.1).1 ρ.2
  have h2 := congrArg Subtype.val hρ
  simp only [LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val] at h2
  refine Submodule.subset_span ⟨S.primitiveIdempotents.e (S.pidx Z), S.primitiveIdempotents.e_mem_corner _, _, hρv,
    S.primitiveIdempotents.e (S.pidx X), S.primitiveIdempotents.e_mem_corner _, ?_⟩
  rw [S.primitiveIdempotents.e_mul_of_mem (S.val_mem_corner ν), mul_assoc, mul_assoc,
    S.primitiveIdempotents.mul_e_of_mem (S.val_mem_corner μ), h2]

variable (hτ : ¬IsIso τ)

set_option maxHeartbeats 1600000 in
/-- **The ray table of `P/τ` presents `B / (t)`.** -/
theorem isRayPres_res :
    (S.quotient (S.idealOf τ) (S.idealOf_le_jacobson τ hτ)).primitiveIdempotents.IsRayPres (k := k)
      (linTable k (RayResidueCategory τ)) (S.labelQ τ) (S.betaQ τ) := by
  set K := S.idealOf τ
  have hK := S.idealOf_le_jacobson τ hτ
  have hcorner : ∀ r : NZ (RayResidueCategory τ), S.betaQ τ r ∈
      (S.quotient K hK).primitiveIdempotents.corner (k := k) (S.labelQ τ r.2.1) (S.labelQ τ r.1) :=
    fun r ↦ S.qmk_corner K hK (S.val_mem_corner _)
  have hne : ∀ r : NZ (RayResidueCategory τ), S.betaQ τ r ≠ 0 := fun r h ↦
    S.repP_liftQ_not_mem τ r.2.2.2 (TwoSidedIdeal.mem_asIdeal.1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  refine ⟨hcorner, hne, ?_, ?_, ?_, ?_⟩
  · -- injectivity
    intro r s h
    have hc := (S.quotient K hK).primitiveIdempotents.ray_subset_corner (hcorner s) h
    obtain ⟨h1, h2⟩ := eq_of_mem_corner' (k := k) _ (hcorner r) hc (hne r)
    obtain ⟨Xr, Yr, fr, hr⟩ := r
    obtain ⟨Xs, Ys, fs, hs⟩ := s
    have hY := (S.labelQ τ).injective h1
    have hX := (S.labelQ τ).injective h2
    subst hY hX
    have hu := S.unitRayEquivalent_of_qmk_mem_ray K hK (S.repP_liftQ_not_mem τ hs) h
    have e : S.liftQ τ fs = S.liftQ τ fr :=
      (sh.{0}).symm.injective ((S.unitRay_repP (S.liftQ τ fs)).symm.trans
        (((unitRay_eq_iff _ _).2 hu).trans (S.unitRay_repP (S.liftQ τ fr))))
    have : fs = fr := calc
      fs = (rayResidueFunctor τ).map (S.liftQ τ fs) := (S.resQ_liftQ τ fs).symm
      _ = (rayResidueFunctor τ).map (S.liftQ τ fr) := by rw [e]
      _ = fr := S.resQ_liftQ τ fr
    first
      | exact congrArg (fun f ↦ (⟨_, _, f⟩ : NZ (RayResidueCategory τ))) (Subtype.ext this.symm)
      | exact congrArg (fun f ↦ (⟨_, _, f⟩ : NZ (RayResidueCategory τ))) (Subtype.ext this)
  · -- surjectivity
    intro x y f' hf' hf0
    obtain ⟨f, hf, rfl⟩ := S.lift_corner K hK hf'
    have hfK : f ∉ K := fun h ↦ hf0 (Ideal.Quotient.eq_zero_iff_mem.2 (TwoSidedIdeal.mem_asIdeal.2 h))
    obtain ⟨⟨X, Y, g, hg⟩, hx, hy, hfr⟩ := S.betaP_surj x y f hf (fun h ↦ hfK (h ▸ K.zero_mem))
    subst hx hy
    have hgK : (S.repP g).1 ∉ K := by
      intro h
      apply hfK
      obtain ⟨u, w, -, -, rfl⟩ := hfr
      exact K.mul_mem_right _ _ (K.mul_mem_left _ _ h)
    have hftm : ¬FactorsThroughMorphism τ g := fun h ↦ hgK ((S.repP_mem_idealOf_iff τ g).2 h)
    have hg0 : (rayResidueFunctor τ).map g ≠ 0 := fun h ↦
      hftm ((rayResidueFunctor_map_eq_zero_iff τ g).1 h)
    refine ⟨⟨⟨X⟩, ⟨Y⟩, (rayResidueFunctor τ).map g, hg0⟩, rfl, rfl, ?_⟩
    change qmk (k := k) K f ∈ (S.quotient K hK).primitiveIdempotents.ray (k := k) _ _
      (qmk (k := k) K (S.repP (S.liftQ τ ((rayResidueFunctor τ).map g))).1)
    rw [S.liftQ_resQ τ g hftm]
    exact S.qmk_ray K hK hfr
  · -- products that are rays
    rintro ⟨Xr, Yr, fr, hr⟩ ⟨Xs, Ys, fs, hs⟩ t h
    rw [linTable_mul_eq_some] at h
    by_cases hY : Ys = Xr
    swap
    · exact absurd (h.symm.trans (morElt_mul_ne k fs fr hY)) (S.morElt_ne_zero_nzQ τ t)
    subst hY
    rw [morElt_mul] at h
    have hne' : fs ≫ fr ≠ 0 := fun h0 ↦ S.morElt_ne_zero_nzQ τ t (by rw [← h, h0, morElt_zero])
    have ht : (⟨Xs, Yr, fs ≫ fr, hne'⟩ : NZ (RayResidueCategory τ)) = t := morElt_injective_nz k h
    subst ht
    set gs := S.liftQ τ fs
    set gr := S.liftQ τ fr
    have himg : (rayResidueFunctor τ).map (gs ≫ gr) = fs ≫ fr := by
      rw [Functor.map_comp, S.resQ_liftQ, S.resQ_liftQ]
    have hftm : ¬FactorsThroughMorphism τ (gs ≫ gr) := fun h0 ↦
      hne' (himg ▸ (rayResidueFunctor_map_eq_zero_iff τ _).2 h0)
    have hlift : S.liftQ τ (fs ≫ fr) = gs ≫ gr := by
      have := S.liftQ_resQ τ (gs ≫ gr) hftm
      rwa [himg] at this
    have hg0 : gs ≫ gr ≠ 0 := fun h0 ↦ hne' (by rw [← himg, h0, Functor.map_zero])
    set μ := S.repP gs
    set ν := S.repP gr
    have hcomp := S.sh_symm_comp_repP gs gr
    have hprod : bgrsRayRepresentativeProduct μ ν ≠ 0 := by
      intro h0
      apply S.sh_symm_ne_zero hg0
      rw [hcomp, h0]
      rfl
    have hns : ¬IsBGRSSpecialZero μ ν := fun hsp ↦
      hprod (bgrsRayRepresentativeProduct_eq_zero_of_special hsp)
    have heq : bgrsRayRepresentativeProduct μ ν = μ ≫ ν :=
      bgrsRayRepresentativeProduct_eq_comp_of_not_special hns
    have hval : (μ ≫ ν).1 = ν.1 * μ.1 :=
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _
    have hu : UnitRayEquivalent (S.repP (gs ≫ gr)) (μ ≫ ν) := by
      rw [← unitRay_eq_iff, S.unitRay_repP, hcomp, heq]
    have hnotK : (μ ≫ ν).1 ∉ K := fun h0 ↦
      (S.repP_mem_idealOf_iff τ _).not.2 hftm
        (S.mem_of_unitRayEquivalent K (S.unitRayEquivalent_symm' hu) h0)
    change qmk (k := k) K ν.1 * qmk (k := k) K μ.1 ∉ _ ∧
      qmk (k := k) K ν.1 * qmk (k := k) K μ.1 ∈ (S.quotient K hK).primitiveIdempotents.ray (k := k) _ _
        (qmk (k := k) K (S.repP (S.liftQ τ (fs ≫ fr))).1)
    rw [hlift]
    refine ⟨?_, ?_⟩
    · refine mul_not_mem_insertionSpan (S.quotient K hK).primitiveIdempotents (f := qmk (k := k) K ν.1)
        (h := qmk (k := k) K μ.1) (S.qmk_corner K hK (S.val_mem_corner ν))
        (S.qmk_corner K hK (S.val_mem_corner μ)) ?_ ?_
      · rw [← map_mul, ← hval]
        intro h0
        exact hnotK (TwoSidedIdeal.mem_asIdeal.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0))
      · intro t' ρ' hρ'
        obtain ⟨ρ, hρ, rfl⟩ := S.lift_cornerRadical K hK hρ'
        obtain ⟨u, w, hu', hw', huw⟩ := S.hray_of_not_special μ ν hns t' ρ hρ
        refine ⟨qmk (k := k) K u, qmk (k := k) K w, S.qmk_unit K hK hu', S.qmk_unit K hK hw', ?_⟩
        have := congrArg (qmk (k := k) K) huw
        simp only [map_mul, map_add, map_smul] at this
        exact this
    · rw [← map_mul, ← hval]
      exact S.qmk_ray K hK ((S.unitRayEquivalent_iff _ _).1 hu)
  · -- products that vanish
    rintro ⟨Xr, Yr, fr, hr⟩ ⟨Xs, Ys, fs, hs⟩ h hmid
    change Xr = Ys at hmid
    subst hmid
    by_cases h0 : fs ≫ fr = 0
    swap
    · have : (linTable k (RayResidueCategory τ)).mul ⟨Xr, Yr, fr, hr⟩ ⟨Xs, Xr, fs, hs⟩ =
          some ⟨Xs, Yr, fs ≫ fr, h0⟩ := by
        rw [linTable_mul_eq_some]
        exact morElt_mul k fs fr
      rw [h] at this
      exact absurd this (by simp)
    set gs := S.liftQ τ fs
    set gr := S.liftQ τ fr
    have himg : (rayResidueFunctor τ).map (gs ≫ gr) = fs ≫ fr := by
      rw [Functor.map_comp, S.resQ_liftQ, S.resQ_liftQ]
    have hftm : FactorsThroughMorphism τ (gs ≫ gr) :=
      (rayResidueFunctor_map_eq_zero_iff τ _).1 (himg.trans h0)
    set μ := S.repP gs
    set ν := S.repP gr
    have hval : (μ ≫ ν).1 = ν.1 * μ.1 :=
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.comp_val _ _ _
    change qmk (k := k) K ν.1 * qmk (k := k) K μ.1 ∈ _
    by_cases hsp : IsBGRSSpecialZero μ ν
    · rw [← map_mul]
      exact S.qmk_insertionSpan K hK (S.mul_mem_insertionSpan_of_special μ ν hsp)
    · have hu : UnitRayEquivalent (S.repP (gs ≫ gr)) (μ ≫ ν) := by
        rw [← unitRay_eq_iff, S.unitRay_repP, S.sh_symm_comp_repP,
          bgrsRayRepresentativeProduct_eq_comp_of_not_special hsp]
      have hK' : (μ ≫ ν).1 ∈ K :=
        S.mem_of_unitRayEquivalent K hu ((S.repP_mem_idealOf_iff τ _).2 hftm)
      have hz : qmk (k := k) K (μ ≫ ν).1 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (TwoSidedIdeal.mem_asIdeal.2 hK')
      rw [← map_mul, ← hval, hz]
      exact Submodule.zero_mem _

/-- **B5: if `B / (t)` is representation-finite, so is the linearization of `P/τ`.** -/
theorem isRepresentationFinite_res [Nontrivial B] (hτ : ¬IsIso τ)
    (hfin : Statement.IsRepresentationFinite (B ⧸ (S.idealOf τ).asIdeal)) :
    Statement.IsRepresentationFinite (Linearization (RayResidueCategory τ) k) := by
  have hK := S.idealOf_le_jacobson τ hτ
  have : Nontrivial (B ⧸ (S.idealOf τ).asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (Ring.jacobson_lt_top B).ne hK)
  have h1 := (S.quotient _ hK).lin_isRepresentationFinite_of_isRayPres hfin _ _ _
    (S.isRayPres_res τ hτ)
  have h2 := isRepresentationFinite_of_surjective
    (B := Linearization (RayResidueCategory τ) k)
    (linTableEquiv k (RayResidueCategory τ)).toAlgHom
    (by exact (linTableEquiv k (RayResidueCategory τ)).surjective) h1
  exact of_right_isRepresentationFinite h2

end Res

end Small

end SplitBasicData

end LargeIndecomposable
