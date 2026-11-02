module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteUniverse
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import LargeIndecomposable.Modules.SplitBasic.BasicReduction
public import LargeIndecomposable.Modules.Idempotents.IdempotentProjectiveCategory
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

def oppositeResidueAlgHom : Aᵐᵒᵖ →ₐ[k] (ι → k) :=
  let qA : A →ₐ[k] (ι → k) :=
    S.quotientEquiv.toAlgHom.comp
      (Ideal.Quotient.mkₐ k (Ring.jacobson A))
  qA.fromOpposite (fun x y => Commute.all (qA x) (qA y))

@[simp] theorem oppositeResidueAlgHom_op_apply (a : A) :
    S.oppositeResidueAlgHom (MulOpposite.op a) =
      S.quotientEquiv (Ideal.Quotient.mk (Ring.jacobson A) a) :=
  rfl

theorem oppositeResidueAlgHom_surjective :
    Function.Surjective S.oppositeResidueAlgHom := by
  intro y
  obtain ⟨z, rfl⟩ := S.quotientEquiv.surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨MulOpposite.op a, rfl⟩

theorem oppositeResidueAlgHom_ker_eq_jacobson [Module.Finite k A] :
    RingHom.ker S.oppositeResidueAlgHom.toRingHom =
      Ring.jacobson Aᵐᵒᵖ := by
  apply RingHom.ker_eq_jacobson_of_surjective_of_isNilpotent
    S.oppositeResidueAlgHom.toRingHom
    S.oppositeResidueAlgHom_surjective
  intro a ha
  have haJ : MulOpposite.unop a ∈ Ring.jacobson A := by
    rw [RingHom.mem_ker] at ha
    change S.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson A) (MulOpposite.unop a)) = 0 at ha
    rw [map_eq_zero_iff S.quotientEquiv S.quotientEquiv.injective] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ :=
    IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨n, ?_⟩
  apply MulOpposite.unop_injective
  have hn' : (Ring.jacobson A) ^ n = 0 := by
    simpa [Ideal.jacobson_bot] using hn
  have hpow : (MulOpposite.unop a) ^ n ∈
      (Ring.jacobson A) ^ n :=
    Ideal.pow_mem_pow haJ n
  rw [hn'] at hpow
  simpa using hpow

theorem opposite_complete :
    CompleteOrthogonalIdempotents
      (fun i => MulOpposite.op (S.idempotent i)) := by
  refine
    { toOrthogonalIdempotents :=
        { idem := ?_
          ortho := ?_ }
      complete := ?_ }
  · intro i
    apply MulOpposite.unop_injective
    simpa using S.complete.toOrthogonalIdempotents.idem i |>.eq
  · intro i j hij
    apply MulOpposite.unop_injective
    simpa using S.complete.toOrthogonalIdempotents.ortho hij.symm
  · apply MulOpposite.unop_injective
    simpa using S.complete.complete

def op [Module.Finite k A] :
    LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := Aᵐᵒᵖ) (ι := ι) := by
  let q := S.oppositeResidueAlgHom
  have hq := S.oppositeResidueAlgHom_surjective
  have hker := S.oppositeResidueAlgHom_ker_eq_jacobson
  let eKer : (Aᵐᵒᵖ ⧸ RingHom.ker q.toRingHom) ≃ₐ[k] (ι → k) :=
    Ideal.quotientKerAlgEquivOfSurjective hq
  let eJac : (Aᵐᵒᵖ ⧸ Ring.jacobson Aᵐᵒᵖ) ≃ₐ[k]
      (Aᵐᵒᵖ ⧸ RingHom.ker q.toRingHom) :=
    Ideal.quotientEquivAlgOfEq k hker.symm
  refine
    { idempotent := fun i => MulOpposite.op (S.idempotent i)
      complete := S.opposite_complete
      quotientEquiv := eJac.trans eKer
      quotientEquiv_mk_idempotent := ?_ }
  intro i j
  dsimp [eJac, eKer, q]
  exact S.quotientEquiv_mk_idempotent i j

@[simp] theorem op_idempotent [Module.Finite k A] (i : ι) :
    S.op.idempotent i = MulOpposite.op (S.idempotent i) :=
  rfl

@[simp] theorem op_projectiveVertex [Module.Finite k A]
    (i : S.ProjectiveIndex) :
    S.op.projectiveVertex i = S.projectiveVertex i :=
  rfl

def opProjectiveMap [Module.Finite k A]
    {i j : S.ProjectiveCategoryᵒᵖ}
    (f : i ⟶ j) :
    (show S.op.ProjectiveCategory from i.unop) ⟶
      (show S.op.ProjectiveCategory from j.unop) := by
  refine ⟨MulOpposite.op f.unop.1, ⟨MulOpposite.op f.unop.1, ?_⟩⟩
  apply MulOpposite.unop_injective
  simp only [op_idempotent, op_projectiveVertex]
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, MulOpposite.unop_mul,
    MulOpposite.unop_op]
  rw [ProjectiveCategory.val_mul_idempotent S f.unop]
  exact ProjectiveCategory.idempotent_mul_val S f.unop

@[simp] theorem opProjectiveMap_val [Module.Finite k A]
    {i j : S.ProjectiveCategoryᵒᵖ} (f : i ⟶ j) :
    (S.opProjectiveMap f).1 = MulOpposite.op f.unop.1 :=
  rfl

def opProjectiveFunctor [Module.Finite k A] :
    S.ProjectiveCategoryᵒᵖ ⥤ S.op.ProjectiveCategory where
  obj i := i.unop
  map f := S.opProjectiveMap f
  map_id i := by
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply Subtype.ext
    rfl

@[simp] theorem opProjectiveFunctor_obj [Module.Finite k A]
    (i : S.ProjectiveCategoryᵒᵖ) :
    S.opProjectiveFunctor.obj i = i.unop :=
  rfl

def projectiveOppositeHomAddEquiv [Module.Finite k A]
    (X Y : S.ProjectiveCategoryᵒᵖ) :
    (X ⟶ Y) ≃+ (Y.unop ⟶ X.unop) where
  toFun f := f.unop
  invFun f := f.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

instance projectiveCategoryOpposite_linear [Module.Finite k A] :
    Linear k S.ProjectiveCategoryᵒᵖ where
  homModule X Y := (S.projectiveOppositeHomAddEquiv X Y).module k
  smul_comp := by
    intro X Y Z c f g
    apply Quiver.Hom.unop_inj
    change g.unop ≫ (c • f.unop) = c • (g.unop ≫ f.unop)
    simp
  comp_smul := by
    intro X Y Z f c g
    apply Quiver.Hom.unop_inj
    change (c • g.unop) ≫ f.unop = c • (g.unop ≫ f.unop)
    simp

instance opProjectiveFunctor_additive [Module.Finite k A] :
    S.opProjectiveFunctor.Additive where
  map_add := by
    intro X Y f g
    apply Subtype.ext
    rfl

instance opProjectiveFunctor_linear [Module.Finite k A] :
    S.opProjectiveFunctor.Linear k where
  map_smul := by
    intro X Y f c
    apply Subtype.ext
    rfl

instance opProjectiveFunctor_faithful [Module.Finite k A] :
    S.opProjectiveFunctor.Faithful where
  map_injective {X Y} f g h := by
    apply Opposite.unop_injective
    apply Subtype.ext
    apply MulOpposite.op_injective
    exact congrArg Subtype.val h

instance opProjectiveFunctor_full [Module.Finite k A] :
    S.opProjectiveFunctor.Full where
  map_surjective {X Y} g := by
    let h : (show S.ProjectiveCategory from Y.unop) ⟶
        (show S.ProjectiveCategory from X.unop) := by
      refine ⟨MulOpposite.unop g.1, ?_⟩
      obtain ⟨a, ha⟩ := g.2
      refine ⟨MulOpposite.unop a, ?_⟩
      apply MulOpposite.op_injective
      simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply,
        LinearMap.mulLeft_apply, MulOpposite.op_mul,
        MulOpposite.op_unop, op_idempotent, op_projectiveVertex,
        opProjectiveFunctor_obj, mul_assoc] using ha
    refine ⟨h.op, ?_⟩
    apply Subtype.ext
    rfl

instance opProjectiveFunctor_essSurj [Module.Finite k A] :
    S.opProjectiveFunctor.EssSurj :=
  Functor.essSurj_of_surj (by
    intro Y
    exact ⟨Opposite.op Y, rfl⟩)

instance opProjectiveFunctor_isEquivalence [Module.Finite k A] :
    S.opProjectiveFunctor.IsEquivalence := {}

noncomputable def opProjectiveEquivalence [Module.Finite k A] :
    S.ProjectiveCategoryᵒᵖ ≌ S.op.ProjectiveCategory := by
  exact S.opProjectiveFunctor.asEquivalence

end LargeIndecomposable.SplitBasicIdempotents

