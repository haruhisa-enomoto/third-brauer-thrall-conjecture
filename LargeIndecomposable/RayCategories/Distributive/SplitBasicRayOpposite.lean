module

public import LargeIndecomposable.Modules.SplitBasic.SplitBasicOpposite
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory
public import LargeIndecomposable.Foundations.PathCategories.LoopPathPower
public import LargeIndecomposable.RayCategories.Contours.ProperPathInterlacement
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPairMatching

@[expose] public section

/-!
# Opposite split-basic ray categories

Reverse the BGRS unit-ray product through the primitive-projective
equivalence between a split-basic algebra and its opposite.  The resulting
equivalence of ray categories reverses irreducible ray-quiver arrows and sends
singular pairs to singular pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u₁ v₁ u₂ v₂

theorem IsIrreducibleRayMorphism.op
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism f.op := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    have hunop := congrArg Quiver.Hom.unop hzero
    simpa using hunop
  · intro hIso
    exact hf.2.1 ((isIso_op_iff f).1 hIso)
  · intro Z g h hcomp
    have hcompUnop : h.unop ≫ g.unop = f := by
      have hunop := congrArg Quiver.Hom.unop hcomp
      simpa using hunop
    rcases hf.2.2 Z.unop h.unop g.unop hcompUnop with hh | hg
    · right
      exact (isIso_unop_iff h).1 hh
    · left
      exact (isIso_unop_iff g).1 hg

/-- Unopposing an irreducible morphism again gives an irreducible
morphism. -/
theorem IsIrreducibleRayMorphism.unop
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism f.unop := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    apply Quiver.Hom.unop_inj
    simpa using hzero
  · intro hIso
    exact hf.2.1 ((isIso_unop_iff f).1 hIso)
  · intro Z g h hcomp
    have hcompOp : h.op ≫ g.op = f := by
      apply Quiver.Hom.unop_inj
      simpa using hcomp
    rcases hf.2.2 (Opposite.op Z) h.op g.op hcompOp with hh | hg
    · right
      exact (isIso_op_iff h).1 hh
    · left
      exact (isIso_op_iff g).1 hg

/-- Precomposition by an isomorphism preserves irreducibility. -/
theorem IsIrreducibleRayMorphism.precomp_isIso
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {W X Y : C} (e : W ⟶ X) [IsIso e] {f : X ⟶ Y}
    (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism (e ≫ f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    have hcomp := congrArg (fun q ↦ inv e ≫ q) hzero
    simpa [Category.assoc] using hcomp
  · intro hcomp
    letI : IsIso (e ≫ f) := hcomp
    exact hf.2.1 (IsIso.of_isIso_comp_left e f)
  · intro Z g h hgh
    have hfactor : (inv e ≫ g) ≫ h = f := by
      have hcomp := congrArg (fun q ↦ inv e ≫ q) hgh
      simpa [Category.assoc] using hcomp
    rcases hf.2.2 Z (inv e ≫ g) h hfactor with hig | hih
    · left
      letI : IsIso (inv e ≫ g) := hig
      exact IsIso.of_isIso_comp_left (inv e) g
    · exact Or.inr hih

theorem IsIrreducibleRayMorphism.map_of_equivalence
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.Full] [F.Faithful] [F.EssSurj]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleRayMorphism f) :
    IsIrreducibleRayMorphism (F.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    apply F.map_injective
    simpa using hzero
  · intro hIso
    exact hf.2.1 (isIso_of_reflects_iso f F)
  · intro Z g h hcomp
    let W : C := F.objPreimage Z
    let e : F.obj W ≅ Z := F.objObjPreimageIso Z
    let a : X ⟶ W := F.preimage (g ≫ e.inv)
    let b : W ⟶ Y := F.preimage (e.hom ≫ h)
    have hab : a ≫ b = f := by
      apply F.map_injective
      simp only [Functor.map_comp, a, b, Functor.map_preimage,
        Category.assoc, Iso.inv_hom_id_assoc, hcomp]
    rcases hf.2.2 W a b hab with ha | hb
    · left
      letI : IsIso a := ha
      haveI : IsIso (F.map a) := Functor.map_isIso F a
      have hg : g = F.map a ≫ e.hom := by
        simp [a, e, Category.assoc]
      rw [hg]
      infer_instance
    · right
      letI : IsIso b := hb
      haveI : IsIso (F.map b) := Functor.map_isIso F b
      have hh : h = e.inv ≫ F.map b := by
        simp [b, e]
      rw [hh]
      infer_instance

/-- A fully faithful functor reflects irreducibility.  Essential
surjectivity is not needed in this direction because a factorization of the
original morphism already maps to a factorization through an object in the
image. -/
theorem IsIrreducibleRayMorphism.of_map_of_fullyFaithful
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.Full] [F.Faithful]
    {X Y : C} {f : X ⟶ Y}
    (hf : IsIrreducibleRayMorphism (F.map f)) :
    IsIrreducibleRayMorphism f := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hf.1
    simpa [hzero]
  · intro hIso
    apply hf.2.1
    exact Functor.map_isIso F f
  · intro Z g h hcomp
    have hmap : F.map g ≫ F.map h = F.map f := by
      simpa only [← Functor.map_comp, hcomp]
    rcases hf.2.2 (F.obj Z) (F.map g) (F.map h) hmap with hg | hh
    · left
      exact isIso_of_reflects_iso g F
    · right
      exact isIso_of_reflects_iso h F

/-- Cotransit becomes transit after reversing a morphism into the opposite
category. -/
theorem AllowsCotransit.op
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {f : X ⟶ Y} (hf : AllowsCotransit f) :
    AllowsTransit f.op := by
  intro a
  obtain ⟨b, hb⟩ := hf (End.of a.asHom.unop)
  refine ⟨End.of b.asHom.op, ?_⟩
  apply Quiver.Hom.unop_inj
  simpa using hb

/-- Transit becomes cotransit after reversing a morphism into the opposite
category. -/
theorem AllowsTransit.op
    {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {f : X ⟶ Y} (hf : AllowsTransit f) :
    AllowsCotransit f.op := by
  intro b
  obtain ⟨a, ha⟩ := hf (End.of b.asHom.unop)
  refine ⟨End.of a.asHom.op, ?_⟩
  apply Quiver.Hom.unop_inj
  simpa using ha

end LargeIndecomposable

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable [Module.Finite k A]

/-- Membership in a principal two-sided Hom span is invariant under
categorical opposite.  The endpoint actions exchange sides under `op`. -/
theorem op_mem_twoSidedEndomorphismSpan_iff
    {X Y : S.ProjectiveCategory} (f g : X ⟶ Y) :
    g.op ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f.op ↔
      g ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f := by
  constructor
  · intro hg
    have unop_mem_span :
        ∀ {h : Opposite.op Y ⟶ Opposite.op X},
          h ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f.op →
            h.unop ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem h hh =>
          rcases hh with ⟨a, b, rfl⟩
          apply Submodule.subset_span
          refine ⟨End.of b.asHom.unop, End.of a.asHom.unop, ?_⟩
          simp
      | zero => simp
      | add h l _ _ hh hl =>
          simpa using
            (LargeIndecomposable.twoSidedEndomorphismSpan k f).add_mem hh hl
      | smul c h _ hh =>
          change c • h.unop ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f
          exact
            (LargeIndecomposable.twoSidedEndomorphismSpan k f).smul_mem c hh
    exact unop_mem_span hg
  · intro hg
    have op_mem_span : ∀ {h : X ⟶ Y},
        h ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f →
          h.op ∈ LargeIndecomposable.twoSidedEndomorphismSpan k f.op := by
      intro h hh
      induction hh using Submodule.span_induction with
      | mem h hh =>
          rcases hh with ⟨a, b, rfl⟩
          apply Submodule.subset_span
          refine ⟨End.of b.asHom.op, End.of a.asHom.op, ?_⟩
          simp
      | zero => simp
      | add h l _ _ hh hl =>
          simpa using
            (LargeIndecomposable.twoSidedEndomorphismSpan k f.op).add_mem hh hl
      | smul c h _ hh =>
          change c • h.op ∈
            LargeIndecomposable.twoSidedEndomorphismSpan k f.op
          exact
            (LargeIndecomposable.twoSidedEndomorphismSpan k f.op).smul_mem c hh
    exact op_mem_span hg

/-- Opposing a primitive-projective morphism preserves the property of
generating its whole Hom space as a two-sided endpoint-endomorphism
bimodule. -/
theorem twoSidedEndomorphismSpan_op_eq_top_iff
    {X Y : S.ProjectiveCategory} (f : X ⟶ Y) :
    LargeIndecomposable.twoSidedEndomorphismSpan k f.op = ⊤ ↔
      LargeIndecomposable.twoSidedEndomorphismSpan k f = ⊤ := by
  constructor
  · intro hop
    apply top_unique
    intro g _
    apply (S.op_mem_twoSidedEndomorphismSpan_iff f g).1
    rw [hop]
    exact Submodule.mem_top
  · intro h
    apply top_unique
    intro g _
    simpa using (S.op_mem_twoSidedEndomorphismSpan_iff f g.unop).2
      (by rw [h]; exact Submodule.mem_top)

def opUnitRay {X Y : S.ProjectiveCategory} :
    LargeIndecomposable.UnitRayOrbit X Y →
      LargeIndecomposable.UnitRayOrbit
        (show S.op.ProjectiveCategory from Y)
        (show S.op.ProjectiveCategory from X) :=
  fun r ↦ Quotient.liftOn' r
    (fun f ↦ LargeIndecomposable.unitRay
      (S.opProjectiveFunctor.map f.op))
    (fun f g hfg ↦ by
      apply Quotient.sound
      rcases hfg with ⟨a, b, rfl⟩
      refine ⟨S.opProjectiveFunctor.mapIso (asIso b.hom.op),
        S.opProjectiveFunctor.mapIso (asIso a.hom.op), ?_⟩
      simp [Category.assoc])

@[simp] theorem opUnitRay_unitRay {X Y : S.ProjectiveCategory}
    (f : X ⟶ Y) :
    S.opUnitRay (LargeIndecomposable.unitRay f) =
      LargeIndecomposable.unitRay (S.opProjectiveFunctor.map f.op) :=
  rfl

@[simp] theorem opUnitRay_zero {X Y : S.ProjectiveCategory} :
    S.opUnitRay (0 : LargeIndecomposable.UnitRayOrbit X Y) = 0 := by
  change LargeIndecomposable.unitRay
      (S.opProjectiveFunctor.map (0 : X ⟶ Y).op) =
    LargeIndecomposable.unitRay
      (0 : (show S.op.ProjectiveCategory from Y) ⟶
        (show S.op.ProjectiveCategory from X))
  simp

theorem opProjectiveFunctor_map_op_mem_jacobson_iff
    (X : S.ProjectiveCategory) (f : End X) :
    End.of (S.opProjectiveFunctor.map f.op) ∈
        Ring.jacobson
          (End (S.opProjectiveFunctor.obj (Opposite.op X))) ↔
      f ∈ Ring.jacobson (End X) := by
  rw [LargeIndecomposable.mem_ringJacobson_iff_not_isUnit,
    LargeIndecomposable.mem_ringJacobson_iff_not_isUnit]
  apply not_congr
  rw [isUnit_iff_isIso, isUnit_iff_isIso,
    isIso_iff_of_reflects_iso f.op S.opProjectiveFunctor,
    isIso_op_iff]

def unopProjectiveMap
    {i j : S.op.ProjectiveCategory} (g : i ⟶ j) :
    (show S.ProjectiveCategory from j) ⟶
      (show S.ProjectiveCategory from i) := by
  refine ⟨MulOpposite.unop g.1, ?_⟩
  obtain ⟨a, ha⟩ := g.2
  refine ⟨MulOpposite.unop a, ?_⟩
  apply MulOpposite.op_injective
  simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, MulOpposite.op_mul,
    MulOpposite.op_unop, op_idempotent, op_projectiveVertex,
    mul_assoc] using ha

@[simp] theorem opProjectiveFunctor_map_unopProjectiveMap
    {i j : S.op.ProjectiveCategory} (g : i ⟶ j) :
    S.opProjectiveFunctor.map (S.unopProjectiveMap g).op = g := by
  apply Subtype.ext
  rfl

theorem isBGRSSpecialZero_opProjectiveFunctor_iff
    {X Y Z : S.ProjectiveCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    LargeIndecomposable.IsBGRSSpecialZero
        (S.opProjectiveFunctor.map g.op)
        (S.opProjectiveFunctor.map f.op) ↔
      LargeIndecomposable.IsBGRSSpecialZero f g := by
  constructor
  · rintro ⟨rho, hrho⟩
    let tau : (Opposite.op Y : S.ProjectiveCategoryᵒᵖ) ⟶ Opposite.op Y :=
      S.opProjectiveFunctor.preimage rho.1.asHom
    have htauMap : S.opProjectiveFunctor.map tau = rho.1.asHom :=
      S.opProjectiveFunctor.map_preimage rho.1.asHom
    have htauJ : tau.unop ∈ Ring.jacobson (End Y) := by
      apply (S.opProjectiveFunctor_map_op_mem_jacobson_iff Y tau.unop).1
      simpa [tau] using rho.2
    refine ⟨⟨tau.unop, htauJ⟩, ?_⟩
    apply Quiver.Hom.op_inj
    apply S.opProjectiveFunctor.map_injective
    simpa [Functor.map_comp, Category.assoc, tau, htauMap] using hrho
  · rintro ⟨rho, hrho⟩
    let rhoOp : End
        (S.opProjectiveFunctor.obj (Opposite.op Y)) :=
      End.of (S.opProjectiveFunctor.map rho.1.asHom.op)
    have hrhoOp : rhoOp ∈ Ring.jacobson
        (End (S.opProjectiveFunctor.obj (Opposite.op Y))) := by
      exact (S.opProjectiveFunctor_map_op_mem_jacobson_iff Y rho.1).2 rho.2
    refine ⟨⟨rhoOp, hrhoOp⟩, ?_⟩
    have hop := congrArg Quiver.Hom.op hrho
    have hmap := congrArg S.opProjectiveFunctor.map hop
    simpa [rhoOp, Functor.map_comp, Category.assoc] using hmap

theorem opProjectiveFunctor_map_op_bgrsRayRepresentativeProduct
    {X Y Z : S.ProjectiveCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.opProjectiveFunctor.map
        (LargeIndecomposable.bgrsRayRepresentativeProduct f g).op =
      LargeIndecomposable.bgrsRayRepresentativeProduct
        (S.opProjectiveFunctor.map g.op)
        (S.opProjectiveFunctor.map f.op) := by
  by_cases hspecial : LargeIndecomposable.IsBGRSSpecialZero f g
  · have hspecialOp :=
      (S.isBGRSSpecialZero_opProjectiveFunctor_iff f g).2 hspecial
    rw [LargeIndecomposable.bgrsRayRepresentativeProduct_eq_zero_of_special
        hspecial,
      LargeIndecomposable.bgrsRayRepresentativeProduct_eq_zero_of_special
        hspecialOp]
    simp
  · have hspecialOp : ¬LargeIndecomposable.IsBGRSSpecialZero
        (S.opProjectiveFunctor.map g.op)
        (S.opProjectiveFunctor.map f.op) :=
      fun h ↦ hspecial
        ((S.isBGRSSpecialZero_opProjectiveFunctor_iff f g).1 h)
    rw [LargeIndecomposable.bgrsRayRepresentativeProduct_eq_comp_of_not_special
        hspecial,
      LargeIndecomposable.bgrsRayRepresentativeProduct_eq_comp_of_not_special
        hspecialOp]
    simp

variable [LargeIndecomposable.HasBGRSPairDichotomy S.ProjectiveCategory]
variable [LargeIndecomposable.HasBGRSPairDichotomy S.op.ProjectiveCategory]

theorem opUnitRay_bgrsRayComp {X Y Z : S.ProjectiveCategory}
    (f : LargeIndecomposable.UnitRayOrbit X Y)
    (g : LargeIndecomposable.UnitRayOrbit Y Z) :
    S.opUnitRay (LargeIndecomposable.bgrsRayComp f g) =
      LargeIndecomposable.bgrsRayComp (S.opUnitRay g) (S.opUnitRay f) := by
  induction f using Quotient.inductionOn' with
  | _ f =>
      induction g using Quotient.inductionOn' with
      | _ g =>
          change LargeIndecomposable.unitRay
              (S.opProjectiveFunctor.map
                (LargeIndecomposable.bgrsRayRepresentativeProduct f g).op) =
            LargeIndecomposable.unitRay
              (LargeIndecomposable.bgrsRayRepresentativeProduct
                (S.opProjectiveFunctor.map g.op)
                (S.opProjectiveFunctor.map f.op))
          rw [S.opProjectiveFunctor_map_op_bgrsRayRepresentativeProduct f g]

omit [LargeIndecomposable.HasBGRSPairDichotomy S.ProjectiveCategory]
    [LargeIndecomposable.HasBGRSPairDichotomy S.op.ProjectiveCategory] in
theorem opUnitRay_injective {X Y : S.ProjectiveCategory} :
    Function.Injective (S.opUnitRay :
      LargeIndecomposable.UnitRayOrbit X Y →
        LargeIndecomposable.UnitRayOrbit
          (show S.op.ProjectiveCategory from Y)
          (show S.op.ProjectiveCategory from X)) := by
  intro r s hrs
  induction r using Quotient.inductionOn' with
  | _ f =>
      induction s using Quotient.inductionOn' with
      | _ g =>
          apply (LargeIndecomposable.unitRay_eq_iff f g).2
          have hfg := (LargeIndecomposable.unitRay_eq_iff
            (S.opProjectiveFunctor.map f.op)
            (S.opProjectiveFunctor.map g.op)).1 hrs
          rcases hfg with ⟨a, b, hab⟩
          let aPre := S.opProjectiveFunctor.preimageIso a
          let bPre := S.opProjectiveFunctor.preimageIso b
          have hop : g.op = aPre.hom ≫ f.op ≫ bPre.hom := by
            apply S.opProjectiveFunctor.map_injective
            simpa [aPre, bPre, Functor.map_comp, Category.assoc] using hab
          refine ⟨asIso bPre.hom.unop, asIso aPre.hom.unop, ?_⟩
          have hunop := congrArg Quiver.Hom.unop hop
          simpa [Category.assoc] using hunop

/-- Every opposite unit ray is the opposite of a unique original unit ray. -/
theorem opUnitRay_surjective {X Y : S.op.ProjectiveCategory} :
    Function.Surjective (S.opUnitRay :
      LargeIndecomposable.UnitRayOrbit
          (show S.ProjectiveCategory from Y)
          (show S.ProjectiveCategory from X) →
        LargeIndecomposable.UnitRayOrbit X Y) := by
  intro r
  induction r using Quotient.inductionOn' with
  | _ f =>
      refine ⟨LargeIndecomposable.unitRay (S.unopProjectiveMap f), ?_⟩
      change LargeIndecomposable.unitRay
          (S.opProjectiveFunctor.map (S.unopProjectiveMap f).op) =
        LargeIndecomposable.unitRay f
      rw [S.opProjectiveFunctor_map_unopProjectiveMap]

/-- The inverse transport on unit rays. -/
noncomputable def unopUnitRay {X Y : S.op.ProjectiveCategory} :
    LargeIndecomposable.UnitRayOrbit X Y →
      LargeIndecomposable.UnitRayOrbit
        (show S.ProjectiveCategory from Y)
        (show S.ProjectiveCategory from X) :=
  Function.surjInv S.opUnitRay_surjective

@[simp] theorem opUnitRay_unopUnitRay
    {X Y : S.op.ProjectiveCategory}
    (r : LargeIndecomposable.UnitRayOrbit X Y) :
    S.opUnitRay (S.unopUnitRay r) = r :=
  Function.rightInverse_surjInv S.opUnitRay_surjective r

@[simp] theorem unopUnitRay_opUnitRay
    {X Y : S.ProjectiveCategory}
    (r : LargeIndecomposable.UnitRayOrbit X Y) :
    S.unopUnitRay (S.opUnitRay r) = r := by
  apply S.opUnitRay_injective
  rw [S.opUnitRay_unopUnitRay]

def opRayFunctor :
    (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)ᵒᵖ ⥤
      LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory where
  obj X := LargeIndecomposable.BGRSRayCategory.mk
    (show S.op.ProjectiveCategory from X.unop.as)
  map f := S.opUnitRay f.unop
  map_id X := by
    change S.opUnitRay
        (LargeIndecomposable.unitRay (𝟙 X.unop.as)) =
      LargeIndecomposable.unitRay
        (𝟙 (show S.op.ProjectiveCategory from X.unop.as))
    simp
  map_comp f g := by
    change S.opUnitRay
        (LargeIndecomposable.bgrsRayComp g.unop f.unop) =
      LargeIndecomposable.bgrsRayComp
        (S.opUnitRay f.unop) (S.opUnitRay g.unop)
    exact S.opUnitRay_bgrsRayComp g.unop f.unop

instance opRayFunctor_preservesZero :
    S.opRayFunctor.PreservesZeroMorphisms where
  map_zero {X Y} := by
    change S.opUnitRay
        (0 : LargeIndecomposable.UnitRayOrbit Y.unop.as X.unop.as) = 0
    exact S.opUnitRay_zero

instance opRayFunctor_faithful : S.opRayFunctor.Faithful where
  map_injective {X Y} f g h := by
    apply Opposite.unop_injective
    exact S.opUnitRay_injective h

instance opRayFunctor_full : S.opRayFunctor.Full where
  map_surjective {X Y} g := by
    induction g using Quotient.inductionOn' with
    | _ g =>
        let pre := S.unopProjectiveMap g
        refine ⟨Quiver.Hom.op (LargeIndecomposable.unitRay pre), ?_⟩
        change LargeIndecomposable.unitRay
            (S.opProjectiveFunctor.map pre.op) =
          LargeIndecomposable.unitRay g
        rw [S.opProjectiveFunctor_map_unopProjectiveMap]

instance opRayFunctor_essSurj : S.opRayFunctor.EssSurj :=
  Functor.essSurj_of_surj (by
    intro Y
    exact ⟨Opposite.op (LargeIndecomposable.BGRSRayCategory.mk
      (show S.ProjectiveCategory from Y.as)), rfl⟩)

instance opRayFunctor_isEquivalence : S.opRayFunctor.IsEquivalence := {}

noncomputable def opRayEquivalence :
    (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)ᵒᵖ ≌
      LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory :=
  S.opRayFunctor.asEquivalence

/-- The inverse opposite-ray functor, defined from the inverse transport on
unit rays. -/
def unopRayFunctor :
    (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)ᵒᵖ ⥤
      LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory where
  obj X := LargeIndecomposable.BGRSRayCategory.mk
    (show S.ProjectiveCategory from X.unop.as)
  map f := S.unopUnitRay f.unop
  map_id X := by
    apply S.opUnitRay_injective
    rw [S.opUnitRay_unopUnitRay]
    change S.opUnitRay
        (LargeIndecomposable.unitRay
          (𝟙 (show S.ProjectiveCategory from X.unop.as))) =
      LargeIndecomposable.unitRay (𝟙 X.unop.as)
    simp
  map_comp f g := by
    change S.unopUnitRay
        (LargeIndecomposable.bgrsRayComp g.unop f.unop) =
      LargeIndecomposable.bgrsRayComp
        (S.unopUnitRay f.unop) (S.unopUnitRay g.unop)
    apply S.opUnitRay_injective
    rw [S.opUnitRay_unopUnitRay,
      S.opUnitRay_bgrsRayComp,
      S.opUnitRay_unopUnitRay, S.opUnitRay_unopUnitRay]

instance unopRayFunctor_preservesZero :
    S.unopRayFunctor.PreservesZeroMorphisms where
  map_zero {X Y} := by
    change S.unopUnitRay
        (0 : LargeIndecomposable.UnitRayOrbit Y.unop.as X.unop.as) = 0
    apply S.opUnitRay_injective
    rw [S.opUnitRay_unopUnitRay]
    exact S.opUnitRay_zero

instance unopRayFunctor_faithful : S.unopRayFunctor.Faithful where
  map_injective {X Y} f g h := by
    change S.unopUnitRay f.unop = S.unopUnitRay g.unop at h
    apply Opposite.unop_injective
    have hmap := congrArg S.opUnitRay h
    rw [S.opUnitRay_unopUnitRay, S.opUnitRay_unopUnitRay] at hmap
    exact hmap

instance unopRayFunctor_full : S.unopRayFunctor.Full where
  map_surjective {X Y} g := by
    refine ⟨Quiver.Hom.op (S.opUnitRay g), ?_⟩
    exact S.unopUnitRay_opUnitRay g

instance unopRayFunctor_essSurj : S.unopRayFunctor.EssSurj :=
  Functor.essSurj_of_surj (by
    intro Y
    exact ⟨Opposite.op (LargeIndecomposable.BGRSRayCategory.mk
      (show S.op.ProjectiveCategory from Y.as)), rfl⟩)

instance unopRayFunctor_isEquivalence : S.unopRayFunctor.IsEquivalence := {}

def opRayVertex
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)) :
    LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory) :=
  ⟨S.opRayFunctor.obj (Opposite.op i.obj)⟩

/-- The objectwise inverse to `opRayVertex`.  Both chosen projective
categories have the same primitive-projective labels. -/
def unopRayVertex
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)) :
    LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory) :=
  ⟨S.unopRayFunctor.obj (Opposite.op i.obj)⟩

@[simp] theorem unopRayVertex_opRayVertex
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)) :
    S.unopRayVertex (S.opRayVertex i) = i := by
  apply LargeIndecomposable.RayVertex.ext
  apply LargeIndecomposable.BGRSRayCategory.ext
  rfl

@[simp] theorem opRayVertex_unopRayVertex
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)) :
    S.opRayVertex (S.unopRayVertex i) = i := by
  apply LargeIndecomposable.RayVertex.ext
  apply LargeIndecomposable.BGRSRayCategory.ext
  rfl

theorem opRayVertex_injective : Function.Injective S.opRayVertex := by
  rintro ⟨i⟩ ⟨j⟩ h
  apply LargeIndecomposable.RayVertex.ext
  apply LargeIndecomposable.BGRSRayCategory.ext
  exact congrArg
    (fun q : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory) ↦
        q.obj.as) h

def opRayArrow
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (a : i ⟶ j) : S.opRayVertex j ⟶ S.opRayVertex i :=
  ⟨S.opRayFunctor.map a.1.op,
    a.2.op.map_of_equivalence S.opRayFunctor⟩

theorem opRayArrow_injective
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)} :
    Function.Injective (S.opRayArrow : (i ⟶ j) →
      (S.opRayVertex j ⟶ S.opRayVertex i)) := by
  intro a b hab
  apply Subtype.ext
  apply Quiver.Hom.op_inj
  apply S.opRayFunctor.map_injective
  exact congrArg Subtype.val hab

/- The arrowwise inverse to `opRayArrow`. -/
set_option maxHeartbeats 1000000 in
def unopRayArrow
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (a : i ⟶ j) : S.unopRayVertex j ⟶ S.unopRayVertex i := by
  refine ⟨S.unopRayFunctor.map a.1.op, ?_⟩
  exact LargeIndecomposable.IsIrreducibleRayMorphism.map_of_equivalence
    S.unopRayFunctor a.2.op

@[simp] theorem opRayArrow_unopRayArrow
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (a : i ⟶ j) :
    S.opRayArrow (S.unopRayArrow a) = a := by
  apply Subtype.ext
  exact S.opUnitRay_unopUnitRay a.1

@[simp] theorem unopRayArrow_opRayArrow
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (a : i ⟶ j) :
    S.unopRayArrow (S.opRayArrow a) = a := by
  apply Subtype.ext
  exact S.unopUnitRay_opUnitRay a.1

@[simp] theorem opRayArrow_morphism
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (a : i ⟶ j) :
    LargeIndecomposable.rayArrowMorphism (S.opRayArrow a) =
      S.opRayFunctor.map a.1.op :=
  rfl

/-- Reverse a ray-quiver path through the opposite-algebra ray equivalence. -/
def opRayPath
    {i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)} :
    {j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)} →
      Quiver.Path i j →
        Quiver.Path (S.opRayVertex j) (S.opRayVertex i)
  | _, .nil => .nil
  | _, .cons p a =>
      (S.opRayArrow a).toPath.comp (opRayPath p)

@[simp] theorem opRayPath_nil
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)) :
    opRayPath S (Quiver.Path.nil : Quiver.Path i i) =
      Quiver.Path.nil :=
  rfl

@[simp] theorem opRayPath_cons
    {i j l : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) (a : j ⟶ l) :
    opRayPath S (p.cons a) =
      (S.opRayArrow a).toPath.comp (opRayPath S p) :=
  rfl

@[simp] theorem opRayPath_toPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (a : i ⟶ j) :
    opRayPath S a.toPath = (S.opRayArrow a).toPath := by
  simp [Quiver.Hom.toPath, opRayPath]

@[simp] theorem opRayPath_length
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    (opRayPath S p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simp [ih, Nat.add_comm]

theorem opRayPath_comp
    {i j l : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    opRayPath S (p.comp q) =
      (opRayPath S q).comp (opRayPath S p) := by
  induction q with
  | nil => simp
  | cons q a ih =>
      simp only [Quiver.Path.comp_cons, opRayPath_cons, ih]
      simp

/-- Reversal commutes with a literal power of a closed path. -/
@[simp] theorem opRayPath_loopPow
    {i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i i) (n : ℕ) :
    opRayPath S (Quiver.Path.loopPow p n) =
      Quiver.Path.loopPow (opRayPath S p) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Quiver.Path.loopPow_succ, opRayPath_comp, ih,
        Quiver.Path.loopPow_succ_left]

/-- Reversing a ray-quiver path sends its ray value to the opposite ray of
the original value. -/
theorem rayPathMap_opRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    LargeIndecomposable.rayPathMap (opRayPath S p) =
      S.opRayFunctor.map (LargeIndecomposable.rayPathMap p).op := by
  induction p with
  | nil =>
      rw [opRayPath_nil]
      calc
        LargeIndecomposable.rayPathMap
              (Quiver.Path.nil : Quiver.Path (S.opRayVertex i)
                (S.opRayVertex i)) = 𝟙 (S.opRayVertex i).obj := by
          exact LargeIndecomposable.LinearPathCategory.pathMap_nil
            (fun z : LargeIndecomposable.RayVertex S.op.RayCategory ↦ z.obj)
            (fun {z w} e ↦ LargeIndecomposable.rayArrowMorphism e)
            (S.opRayVertex i)
        _ = S.opRayFunctor.map (𝟙 (Opposite.op i.obj)) :=
          (S.opRayFunctor.map_id (Opposite.op i.obj)).symm
        _ = S.opRayFunctor.map
              (LargeIndecomposable.rayPathMap
                (Quiver.Path.nil : Quiver.Path i i)).op := by
          congr 1
          apply Quiver.Hom.unop_inj
          simpa using (LargeIndecomposable.LinearPathCategory.pathMap_nil
            (fun z : LargeIndecomposable.RayVertex S.RayCategory ↦ z.obj)
            (fun {z w} e ↦ LargeIndecomposable.rayArrowMorphism e) i).symm
  | cons p a ih =>
      calc
        LargeIndecomposable.rayPathMap (opRayPath S (p.cons a)) =
            LargeIndecomposable.rayPathMap (opRayPath S p) ≫
              LargeIndecomposable.rayPathMap (S.opRayArrow a).toPath := by
          rw [opRayPath_cons]
          simp only [LargeIndecomposable.rayPathMap,
            LargeIndecomposable.LinearPathCategory.pathMap_comp]
        _ = S.opRayFunctor.map
              (LargeIndecomposable.rayPathMap p).op ≫
            S.opRayFunctor.map
              (LargeIndecomposable.rayArrowMorphism a).op := by
          rw [ih, LargeIndecomposable.rayPathMap_toPath]
          rfl
        _ = S.opRayFunctor.map
              (LargeIndecomposable.rayArrowMorphism a ≫
                LargeIndecomposable.rayPathMap p).op := by
          rw [← Functor.map_comp]
          rfl
        _ = S.opRayFunctor.map
              (LargeIndecomposable.rayPathMap (p.cons a)).op := by
          have hcons : LargeIndecomposable.rayPathMap (p.cons a) =
              LargeIndecomposable.rayArrowMorphism a ≫
                LargeIndecomposable.rayPathMap p := by
            exact LargeIndecomposable.LinearPathCategory.pathMap_cons
              (fun z : LargeIndecomposable.RayVertex S.RayCategory ↦ z.obj)
              (fun {z w} e ↦ LargeIndecomposable.rayArrowMorphism e) p a
          rw [hcons]

/-- The path-evaluation formula stated directly with the inverse-compatible
unit-ray transport. -/
theorem rayPathMap_opRayPath_eq_opUnitRay
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    LargeIndecomposable.rayPathMap (opRayPath S p) =
      S.opUnitRay (LargeIndecomposable.rayPathMap p) := by
  rw [S.rayPathMap_opRayPath]
  rfl

/-- Reverse an opposite-algebra ray path back to the original ray quiver. -/
def unopRayPath
    {i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)} :
    {j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)} →
      Quiver.Path i j →
        Quiver.Path (S.unopRayVertex j) (S.unopRayVertex i)
  | _, .nil => .nil
  | _, .cons p a =>
      (S.unopRayArrow a).toPath.comp (unopRayPath p)

@[simp] theorem unopRayPath_nil
    (i : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)) :
    unopRayPath S (Quiver.Path.nil : Quiver.Path i i) =
      Quiver.Path.nil :=
  rfl

@[simp] theorem unopRayPath_cons
    {i j l : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (p : Quiver.Path i j) (a : j ⟶ l) :
    unopRayPath S (p.cons a) =
      (S.unopRayArrow a).toPath.comp (unopRayPath S p) :=
  rfl

@[simp] theorem unopRayPath_length
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    (unopRayPath S p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simp [ih, Nat.add_comm]

theorem unopRayPath_comp
    {i j l : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    unopRayPath S (p.comp q) =
      (unopRayPath S q).comp (unopRayPath S p) := by
  induction q with
  | nil => simp
  | cons q a ih =>
      simp only [Quiver.Path.comp_cons, unopRayPath_cons, ih]
      simp

@[simp] theorem unopRayPath_opRayArrow_toPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (a : i ⟶ j) :
    unopRayPath S (S.opRayArrow a).toPath = a.toPath := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  simp [Quiver.Hom.toPath, unopRayPath, unopRayVertex, opRayVertex,
    unopRayFunctor, opRayFunctor]

@[simp] theorem opRayPath_unopRayArrow_toPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (a : i ⟶ j) :
    opRayPath S (S.unopRayArrow a).toPath = a.toPath := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  simp [Quiver.Hom.toPath, opRayPath, unopRayVertex, opRayVertex,
    unopRayFunctor, opRayFunctor]

@[simp] theorem unopRayPath_opRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    unopRayPath S (opRayPath S p) = p := by
  induction p with
  | nil =>
      rcases i with ⟨⟨i⟩⟩
      rfl
  | @cons b c p a ih =>
      rcases i with ⟨⟨i⟩⟩
      rcases b with ⟨⟨b⟩⟩
      rcases c with ⟨⟨c⟩⟩
      rw [opRayPath_cons, unopRayPath_comp, ih]
      rw [unopRayPath_opRayArrow_toPath]
      rfl

@[simp] theorem opRayPath_unopRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (p : Quiver.Path i j) :
    opRayPath S (unopRayPath S p) = p := by
  induction p with
  | nil =>
      rcases i with ⟨⟨i⟩⟩
      rfl
  | @cons b c p a ih =>
      rcases i with ⟨⟨i⟩⟩
      rcases b with ⟨⟨b⟩⟩
      rcases c with ⟨⟨c⟩⟩
      rw [unopRayPath_cons, opRayPath_comp, ih]
      rw [opRayPath_unopRayArrow_toPath]
      rfl

/-- Contour-relatedness is invariant under opposite path reversal. -/
theorem rayPathContourRelation_related_opRayPath_iff
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p q : Quiver.Path i j) :
    (LargeIndecomposable.rayPathContourRelation
      (C := S.op.RayCategory)).related
        (opRayPath S p) (opRayPath S q) ↔
      (LargeIndecomposable.rayPathContourRelation
        (C := S.RayCategory)).related p q := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  constructor
  · rintro ⟨hpOp, hpqOp⟩
    constructor
    · intro hp
      apply hpOp
      rw [S.rayPathMap_opRayPath, hp]
      simp
    · apply Quiver.Hom.op_inj
      apply S.opRayFunctor.map_injective
      rw [S.rayPathMap_opRayPath p, S.rayPathMap_opRayPath q] at hpqOp
      exact hpqOp
  · rintro ⟨hp, hpq⟩
    constructor
    · intro hpOp
      apply hp
      apply Quiver.Hom.op_inj
      apply S.opRayFunctor.map_injective
      rw [S.rayPathMap_opRayPath p] at hpOp
      change S.opRayFunctor.map
        (LargeIndecomposable.rayPathMap p).op = 0 at hpOp
      simpa using hpOp
    · simpa only [S.rayPathMap_opRayPath, hpq]

/-- The inverse formulation of contour-relatedness invariance. -/
theorem rayPathContourRelation_related_unopRayPath_iff
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    (p q : Quiver.Path i j) :
    (LargeIndecomposable.rayPathContourRelation
      (C := S.RayCategory)).related
        (unopRayPath S p) (unopRayPath S q) ↔
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory)).related p q := by
  rcases i with ⟨⟨i⟩⟩
  rcases j with ⟨⟨j⟩⟩
  have h := (S.rayPathContourRelation_related_opRayPath_iff
    (unopRayPath S p) (unopRayPath S q)).symm
  rw [S.opRayPath_unopRayPath p, S.opRayPath_unopRayPath q] at h
  exact h

/-- A proper-whisker replacement reverses to a proper-whisker replacement
over the opposite algebra. -/
theorem properWhiskerInterlacementStep_opRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    {p q : Quiver.Path i j}
    (h : LargeIndecomposable.ProperWhiskerInterlacementStep
      (LargeIndecomposable.rayPathContourRelation
        (C := S.RayCategory)) p q) :
    LargeIndecomposable.ProperWhiskerInterlacementStep
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory))
      (opRayPath S p) (opRayPath S q) := by
  rcases h with ⟨a, b, s, v, w, t, hvw, houter, hproper, hp, hq⟩
  subst p
  subst q
  refine ⟨S.opRayVertex b, S.opRayVertex a,
    opRayPath S t, opRayPath S v, opRayPath S w, opRayPath S s,
    (S.rayPathContourRelation_related_opRayPath_iff v w).2 hvw,
    ?_, ?_, ?_, ?_⟩
  · have hopOuter :=
      (S.rayPathContourRelation_related_opRayPath_iff
        ((s.comp v).comp t) ((s.comp w).comp t)).2 houter
    simpa only [S.opRayPath_comp, Quiver.Path.comp_assoc] using hopOuter
  · simpa only [S.opRayPath_length, Nat.add_comm] using hproper
  · simp only [S.opRayPath_comp, Quiver.Path.comp_assoc]
  · simp only [S.opRayPath_comp, Quiver.Path.comp_assoc]

/-- The inverse proper-whisker transport. -/
theorem properWhiskerInterlacementStep_unopRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    {p q : Quiver.Path i j}
    (h : LargeIndecomposable.ProperWhiskerInterlacementStep
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory)) p q) :
    LargeIndecomposable.ProperWhiskerInterlacementStep
      (LargeIndecomposable.rayPathContourRelation
        (C := S.RayCategory))
      (unopRayPath S p) (unopRayPath S q) := by
  rcases h with ⟨a, b, s, v, w, t, hvw, houter, hproper, hp, hq⟩
  subst p
  subst q
  refine ⟨S.unopRayVertex b, S.unopRayVertex a,
    unopRayPath S t, unopRayPath S v, unopRayPath S w,
    unopRayPath S s,
    (S.rayPathContourRelation_related_unopRayPath_iff v w).2 hvw,
    ?_, ?_, ?_, ?_⟩
  · have hunopOuter :=
      (S.rayPathContourRelation_related_unopRayPath_iff
        ((s.comp v).comp t) ((s.comp w).comp t)).2 houter
    simpa only [S.unopRayPath_comp, Quiver.Path.comp_assoc] using hunopOuter
  · simpa only [S.unopRayPath_length, Nat.add_comm] using hproper
  · simp only [S.unopRayPath_comp, Quiver.Path.comp_assoc]
  · simp only [S.unopRayPath_comp, Quiver.Path.comp_assoc]

/-- Proper-whisker interlacement is preserved by opposite path reversal. -/
theorem properWhiskerInterlaced_opRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    {p q : Quiver.Path i j}
    (h : (LargeIndecomposable.properWhiskerInterlacementRelation
      (LargeIndecomposable.rayPathContourRelation
        (C := S.RayCategory))).interlaced p q) :
    (LargeIndecomposable.properWhiskerInterlacementRelation
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory))).interlaced
      (opRayPath S p) (opRayPath S q) := by
  change Relation.EqvGen _ p q at h
  change Relation.EqvGen _ (opRayPath S p) (opRayPath S q)
  induction h with
  | rel p q hpq =>
      exact Relation.EqvGen.rel _ _
        (S.properWhiskerInterlacementStep_opRayPath hpq)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q hpq ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r hpq hqr ihpq ihqr =>
      exact Relation.EqvGen.trans _ _ _ ihpq ihqr

/-- Proper-whisker interlacement is preserved by inverse path reversal. -/
theorem properWhiskerInterlaced_unopRayPath
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.op.ProjectiveCategory)}
    {p q : Quiver.Path i j}
    (h : (LargeIndecomposable.properWhiskerInterlacementRelation
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory))).interlaced p q) :
    (LargeIndecomposable.properWhiskerInterlacementRelation
      (LargeIndecomposable.rayPathContourRelation
        (C := S.RayCategory))).interlaced
      (unopRayPath S p) (unopRayPath S q) := by
  change Relation.EqvGen _ p q at h
  change Relation.EqvGen _ (unopRayPath S p) (unopRayPath S q)
  induction h with
  | rel p q hpq =>
      exact Relation.EqvGen.rel _ _
        (S.properWhiskerInterlacementStep_unopRayPath hpq)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q hpq ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r hpq hqr ihpq ihqr =>
      exact Relation.EqvGen.trans _ _ _ ihpq ihqr

/-- Proper-whisker interlacement is invariant under opposite path reversal. -/
theorem properWhiskerInterlaced_opRayPath_iff
    {i j : LargeIndecomposable.RayVertex
      (LargeIndecomposable.BGRSRayCategory S.ProjectiveCategory)}
    (p q : Quiver.Path i j) :
    (LargeIndecomposable.properWhiskerInterlacementRelation
      (LargeIndecomposable.rayPathContourRelation
        (C := S.op.RayCategory))).interlaced
        (opRayPath S p) (opRayPath S q) ↔
      (LargeIndecomposable.properWhiskerInterlacementRelation
        (LargeIndecomposable.rayPathContourRelation
          (C := S.RayCategory))).interlaced p q := by
  constructor
  · intro h
    have hunop := S.properWhiskerInterlaced_unopRayPath h
    rw [S.unopRayPath_opRayPath p, S.unopRayPath_opRayPath q] at hunop
    exact hunop
  · exact S.properWhiskerInterlaced_opRayPath

def opArrow
    (a : LargeIndecomposable.SingularPairNormalization.Arrow
      (C := S.ProjectiveCategory)) :
    LargeIndecomposable.SingularPairNormalization.Arrow
      (C := S.op.ProjectiveCategory) where
  source := S.opRayVertex a.target
  target := S.opRayVertex a.source
  hom := S.opRayArrow a.hom

theorem opArrow_injective : Function.Injective S.opArrow := by
  rintro ⟨aSource, aTarget, ah⟩ ⟨bSource, bTarget, bh⟩ hab
  have ht : aTarget = bTarget := S.opRayVertex_injective
    (congrArg LargeIndecomposable.SingularPairNormalization.Arrow.source hab)
  have hs : aSource = bSource := S.opRayVertex_injective
    (congrArg LargeIndecomposable.SingularPairNormalization.Arrow.target hab)
  subst bTarget
  subst bSource
  have hh : S.opRayArrow ah = S.opRayArrow bh := by
    injection hab
  have hab' : ah = bh := S.opRayArrow_injective hh
  subst bh
  rfl

def opRepresentative
    {a : LargeIndecomposable.SingularPairNormalization.Arrow
      (C := S.ProjectiveCategory)}
    (r : LargeIndecomposable.SingularPairNormalization.Representative a) :
    LargeIndecomposable.SingularPairNormalization.Representative
      (S.opArrow a) where
  hom := S.opProjectiveMap (Quiver.Hom.op r.hom)
  unitRay_hom := by
    change LargeIndecomposable.unitRay
        (S.opProjectiveFunctor.map r.hom.op) =
      S.opUnitRay a.hom.1
    rw [← r.unitRay_hom]
    rfl

def opComposablePair
    (p : LargeIndecomposable.SingularPairNormalization.ComposablePair
      (C := S.ProjectiveCategory)) :
    LargeIndecomposable.SingularPairNormalization.ComposablePair
      (C := S.op.ProjectiveCategory) where
  source := S.opRayVertex p.target
  middle := S.opRayVertex p.middle
  target := S.opRayVertex p.source
  first := S.opRayArrow p.second
  second := S.opRayArrow p.first

@[simp] theorem opComposablePair_firstArrow
    (p : LargeIndecomposable.SingularPairNormalization.ComposablePair
      (C := S.ProjectiveCategory)) :
    (S.opComposablePair p).firstArrow = S.opArrow p.secondArrow :=
  rfl

@[simp] theorem opComposablePair_secondArrow
    (p : LargeIndecomposable.SingularPairNormalization.ComposablePair
      (C := S.ProjectiveCategory)) :
    (S.opComposablePair p).secondArrow = S.opArrow p.firstArrow :=
  rfl

theorem opComposablePair_isSingular
    (p : LargeIndecomposable.SingularPairNormalization.ComposablePair
      (C := S.ProjectiveCategory))
    (hp : p.IsSingular) :
    (S.opComposablePair p).IsSingular := by
  refine ⟨?_, ?_⟩
  · have hzero : p.second.1 ≫ p.first.1 = 0 := by
      simpa only [LargeIndecomposable.SingularPairNormalization.ComposablePair.path,
        LargeIndecomposable.rayPathMap,
        LinearPathCategory.pathMap_comp,
        LargeIndecomposable.rayPathMap_toPath,
        LargeIndecomposable.rayArrowMorphism] using hp.1
    have hop := congrArg Quiver.Hom.op hzero
    have hmap := congrArg S.opRayFunctor.map hop
    have htarget : S.opRayFunctor.map p.first.1.op ≫
        S.opRayFunctor.map p.second.1.op = 0 := by
      simpa [Functor.map_comp] using hmap
    simp only [opComposablePair,
      LargeIndecomposable.SingularPairNormalization.ComposablePair.path,
      LargeIndecomposable.rayPathMap,
      LinearPathCategory.pathMap_comp,
      LargeIndecomposable.rayPathMap_toPath,
      LargeIndecomposable.rayArrowMorphism, opRayArrow,
      opRayVertex]
    convert htarget using 1
  · obtain ⟨rfirst, rsecond, hne⟩ := hp.2
    refine ⟨S.opRepresentative rsecond,
      S.opRepresentative rfirst, ?_⟩
    intro hzero
    apply hne
    apply Subtype.ext
    apply MulOpposite.op_injective
    have hval := congrArg (fun q ↦ q.1) hzero
    simp [opRepresentative, opProjectiveMap] at hval ⊢
    exact hval

def opSingularPair
    (p : LargeIndecomposable.SingularPairNormalization.SingularPair
      (C := S.ProjectiveCategory)) :
    LargeIndecomposable.SingularPairNormalization.SingularPair
      (C := S.op.ProjectiveCategory) :=
  ⟨S.opComposablePair p.1,
    S.opComposablePair_isSingular p.1 p.2⟩

@[simp] theorem opSingularPair_firstArrow
    (p : LargeIndecomposable.SingularPairNormalization.SingularPair
      (C := S.ProjectiveCategory)) :
    (S.opSingularPair p).1.firstArrow = S.opArrow p.1.secondArrow :=
  rfl

@[simp] theorem opSingularPair_secondArrow
    (p : LargeIndecomposable.SingularPairNormalization.SingularPair
      (C := S.ProjectiveCategory)) :
    (S.opSingularPair p).1.secondArrow = S.opArrow p.1.firstArrow :=
  rfl

end LargeIndecomposable.SplitBasicIdempotents
