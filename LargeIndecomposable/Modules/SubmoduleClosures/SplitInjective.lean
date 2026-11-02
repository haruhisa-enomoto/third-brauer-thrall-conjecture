module

public import LargeIndecomposable.Modules.SubmoduleClosures.AntiExchange
set_option backward.isDefEq.respectTransparency.types false

/-!
# Extremality and relative split injectivity

This file gives the direct submodule-side bridge between extreme points and
relative split injectives.  The proof uses common kernels and the nilpotent
Jacobson radical; it does not invoke categorical duality or
Krull--Schmidt multiplicity uniqueness.
-/

@[expose] public section

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace LargeIndecomposable.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- An indecomposable is relatively split injective in `C` when every
monomorphism from it to an explicitly presented object of `add C`
admits a retraction. -/
def IsRelativeSplitInjective (C : Set ι) (x : ι) : Prop :=
  ∀ P : σ.SubPresentation C (σ.obj x),
    Nonempty (SplitMono P.map)

omit [IsNoetherianRing R] in
private theorem fg_hom_hom_sum {J : Type*} [Fintype J]
    {X Y : FGModuleCat.{w} R} (f : J → (X ⟶ Y)) :
    (∑ j, f j).hom.hom = ∑ j, (f j).hom.hom := by
  have h :
      (∑ j, f j).hom = ∑ j, (f j).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h, ModuleCat.hom_sum]

omit [IsNoetherianRing R] in
private theorem biproduct_apply_eq_zero_of_components
    {J : Type*} [Fintype J]
    {X : FGModuleCat.{w} R} {Y : J → FGModuleCat.{w} R}
    (g : X ⟶ ⨁ Y) (x : X)
    (h : ∀ j, (g ≫ biproduct.π Y j).hom.hom x = 0) :
    g.hom.hom x = 0 := by
  classical
  let C : Submodule R X := R ∙ x
  letI : Module.Finite R C :=
    Module.Finite.of_fg (Submodule.fg_span_singleton x)
  let e : FGModuleCat.of R C ⟶ X :=
    FGModuleCat.ofHom C.subtype
  have he : e ≫ g = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, zero_comp]
    apply FGModuleCat.hom_ext
    ext z
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp z.2
    change (g ≫ biproduct.π Y j).hom.hom z.1 = 0
    rw [← hr, map_smul, h j, smul_zero]
  let z : C := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hz := congrArg
    (fun f : FGModuleCat.of R C ⟶ ⨁ Y ↦ f.hom.hom z) he
  change g.hom.hom (C.subtype z) = 0 at hz
  exact hz

/-- A split embedding of `X` into a sum of indecomposables all distinct
from `X` would put the identity in the endomorphism radical. -/
theorem not_splitMono_of_labels_ne
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (hne : ∀ t, x ≠ P.label t) :
    ¬ Nonempty (SplitMono P.map) := by
  classical
  rintro ⟨s⟩
  letI : Fintype P.index := FintypeCat.fintype
  let a (t : P.index) : σ.obj x ⟶ σ.obj (P.label t) :=
    P.map ≫
      biproduct.π
        (fun j : P.index ↦ σ.obj (P.label j)) t
  let b (t : P.index) : σ.obj (P.label t) ⟶ σ.obj x :=
    biproduct.ι
        (fun j : P.index ↦ σ.obj (P.label j)) t ≫
      s.retraction
  have hcat :
      (𝟙 (σ.obj x)) =
        ∑ t : P.index, a t ≫ b t := by
    rw [← s.id]
    calc
      P.map ≫ s.retraction =
          (P.map ≫ 𝟙 _) ≫ s.retraction := by simp
      _ =
          (P.map ≫
            (∑ t : P.index,
              biproduct.π
                  (fun j : P.index ↦ σ.obj (P.label j)) t ≫
                biproduct.ι
                  (fun j : P.index ↦ σ.obj (P.label j)) t)) ≫
            s.retraction := by rw [biproduct.total]
      _ = ∑ t : P.index, a t ≫ b t := by
        rw [Preadditive.comp_sum, Preadditive.sum_comp]
        simp only [a, b, Category.assoc]
  have hlinear := congrArg (fun q ↦ q.hom.hom) hcat
  simp only [FGModuleCat.hom_hom_id, fg_hom_hom_sum,
    FGModuleCat.hom_hom_comp] at hlinear
  let J := Ring.jacobson (Module.End R (σ.obj x))
  have hsum :
      (∑ t : P.index,
        (b t).hom.hom.comp (a t).hom.hom) ∈ J := by
    apply Ideal.sum_mem
    intro t _
    exact comp_mem_end_jacobson σ (hne t) (b t) (a t)
  have hone : (1 : Module.End R (σ.obj x)) ∈ J := by
    rw [Module.End.one_eq_id, hlinear]
    exact hsum
  have hnonunit :
      ¬ IsUnit (1 : Module.End R (σ.obj x)) :=
    (LargeIndecomposable.mem_end_jacobson_iff_not_isUnit
      (σ.indecomposable x) (σ.finiteLength x) 1).1 hone
  exact hnonunit isUnit_one

/-- If a component of a presentation is an invertible endomorphism of
the source representative, then the whole presentation map splits. -/
theorem splitMono_of_isUnit_component
    {S : Set ι} {x : ι}
    (P : σ.SubPresentation S (σ.obj x))
    (t : P.index) (ht : P.label t = x)
    (hunit :
      IsUnit
        ((P.map ≫
          biproduct.π
              (fun j : P.index ↦ σ.obj (P.label j)) t ≫
            eqToHom (congrArg σ.obj ht)).hom.hom)) :
    Nonempty (SplitMono P.map) := by
  let q : σ.obj (P.label t) ⟶ σ.obj x :=
    eqToHom (congrArg σ.obj ht)
  let a : σ.obj x ⟶ σ.obj x :=
    P.map ≫
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫ q
  have hbijective : Function.Bijective a.hom.hom :=
    (Module.End.isUnit_iff a.hom.hom).mp hunit
  let F := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (F.map a) := by
    change IsIso a.hom
    exact
      (ConcreteCategory.isIso_iff_bijective a.hom).mpr
        hbijective
  letI : IsIso a :=
    isIso_of_reflects_iso a F
  refine ⟨{
    retraction :=
      biproduct.π
          (fun j : P.index ↦ σ.obj (P.label j)) t ≫
        q ≫ inv a
    id := ?_ }⟩
  change a ≫ inv a = 𝟙 _
  exact IsIso.hom_inv_id a

end LargeIndecomposable.IndecomposableSkeleton
