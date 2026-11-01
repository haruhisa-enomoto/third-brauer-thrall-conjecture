module

public import LargeIndecomposable.Foundations.CategoryTheory.LinearMat
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

/-!
# Linear transport of endomorphism algebras

Small utilities for passing endomorphism algebras through fully faithful
linear functors, additive matrix categories, object isomorphisms, and finite
reindexings.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

universe u₁ u₂ v w

variable {k : Type w} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Linear k C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D]
  [CategoryTheory.Linear k D]

/-- Applying an additive functor entrywise to finite Hom matrices is
additive. -/
instance mapMatAdditive (F : C ⥤ D) [F.Additive] : F.mapMat_.Additive where
  map_add := by
    intro M N f g
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    exact F.map_add

/-- Applying a linear functor entrywise to finite Hom matrices is linear. -/
instance mapMatLinear (F : C ⥤ D) [F.Additive] [F.Linear k] :
    F.mapMat_.Linear k where
  map_smul f r := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    exact F.map_smul r (f i j)

/-- Entrywise application of a full additive functor to finite Hom matrices
is full. -/
instance mapMatFull (F : C ⥤ D) [F.Additive] [F.Full] : F.mapMat_.Full where
  map_surjective {M N} f := by
    refine ⟨fun i j ↦ F.preimage (f i j), ?_⟩
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    exact F.map_preimage (f i j)

/-- Entrywise application of a faithful additive functor to finite Hom
matrices is faithful. -/
instance mapMatFaithful (F : C ⥤ D) [F.Additive] [F.Faithful] :
    F.mapMat_.Faithful where
  map_injective {M N} f g h := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    apply F.map_injective
    exact congrFun (congrFun h i) j

/-- A linear functor induces an algebra homomorphism on every endomorphism
algebra. -/
def endAlgHom (F : C ⥤ D) [F.Additive] [F.Linear k] (X : C) :
    CategoryTheory.End X →ₐ[k] CategoryTheory.End (F.obj X) where
  toFun := F.map
  map_zero' := F.map_zero X X
  map_one' := F.map_id X
  map_add' _ _ := F.map_add
  map_mul' f g := F.map_comp g f
  commutes' r := by
    change F.map (r • 𝟙 X) = r • 𝟙 (F.obj X)
    rw [F.map_smul, F.map_id]

@[simp]
theorem endAlgHom_apply (F : C ⥤ D) [F.Additive] [F.Linear k]
    (X : C) (f : CategoryTheory.End X) :
    endAlgHom (k := k) F X f = F.map f :=
  rfl

/-- A fully faithful additive linear functor gives a linear equivalence on
each Hom space. -/
def homLinearEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X Y : C) : (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' := fun _ _ ↦ F.map_add
  map_smul' := fun r f ↦ F.map_smul r f

@[simp]
theorem homLinearEquivOfFullyFaithful_apply
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X Y : C) (f : X ⟶ Y) :
    homLinearEquivOfFullyFaithful (k := k) F X Y f = F.map f :=
  rfl

/-- A fully faithful additive linear functor identifies the endomorphism
algebra of an object with that of its image. -/
def endAlgEquivOfFullyFaithful
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X : C) :
    CategoryTheory.End X ≃ₐ[k] CategoryTheory.End (F.obj X) := by
  let e : CategoryTheory.End X ≃ₗ[k] CategoryTheory.End (F.obj X) :=
    homLinearEquivOfFullyFaithful (k := k) F X X
  exact AlgEquiv.ofLinearEquiv e
    (by
      change homLinearEquivOfFullyFaithful (k := k) F X X (𝟙 X) =
        𝟙 (F.obj X)
      rw [homLinearEquivOfFullyFaithful_apply]
      exact F.map_id X)
    (fun f g ↦ by
      change homLinearEquivOfFullyFaithful (k := k) F X X (g ≫ f) =
        homLinearEquivOfFullyFaithful (k := k) F X X g ≫
          homLinearEquivOfFullyFaithful (k := k) F X X f
      rw [homLinearEquivOfFullyFaithful_apply,
        homLinearEquivOfFullyFaithful_apply,
        homLinearEquivOfFullyFaithful_apply]
      exact F.map_comp g f)

@[simp]
theorem endAlgEquivOfFullyFaithful_apply
    (F : C ⥤ D) [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (X : C) (f : CategoryTheory.End X) :
    endAlgEquivOfFullyFaithful (k := k) F X f = F.map f :=
  by
    rfl

end CategoryTheory.Functor

namespace CategoryTheory.Iso

universe u v w

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {X Y : C}

/-- Conjugation by an isomorphism is linear on endomorphism spaces. -/
def conjLinearEquiv (e : X ≅ Y) :
    CategoryTheory.End X ≃ₗ[k] CategoryTheory.End Y :=
  CategoryTheory.Linear.homCongr k e e

@[simp]
theorem conjLinearEquiv_apply (e : X ≅ Y) (f : CategoryTheory.End X) :
    conjLinearEquiv (k := k) e f = e.conj f := by
  unfold conjLinearEquiv
  apply CategoryTheory.End.ext
  simp only [Iso.conj_apply]
  dsimp only [CategoryTheory.End.asHom]
  convert CategoryTheory.Linear.homCongr_apply k e e f using 1
  · exact (Category.assoc _ _ _).symm

/-- Conjugation by an isomorphism is an equivalence of endomorphism
algebras in a linear category. -/
def conjAlgEquiv (e : X ≅ Y) :
    CategoryTheory.End X ≃ₐ[k] CategoryTheory.End Y :=
  AlgEquiv.ofLinearEquiv (conjLinearEquiv (k := k) e)
    (by
      rw [conjLinearEquiv_apply]
      exact e.conj_id)
    (fun f g ↦ by
      rw [conjLinearEquiv_apply, conjLinearEquiv_apply,
        conjLinearEquiv_apply]
      exact map_mul e.conj f g)

@[simp]
theorem conjAlgEquiv_apply (e : X ≅ Y) (f : CategoryTheory.End X) :
    conjAlgEquiv (k := k) e f = e.inv ≫ f ≫ e.hom :=
  by
    change conjLinearEquiv (k := k) e f = _
    rw [conjLinearEquiv_apply, Iso.conj_apply]

end CategoryTheory.Iso

namespace CategoryTheory.Mat_

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Two finite tuples which differ by an equivalence of their index types and
objectwise isomorphisms are isomorphic in the additive matrix category. -/
def isoOfEquiv (M N : Mat_ C) (e : M.ι ≃ N.ι)
    (w : ∀ i, M.X i ≅ N.X (e i)) : M ≅ N :=
  M.isoBiproductEmbedding ≪≫
    Limits.biproduct.whiskerEquiv e
      (fun i ↦ ((CategoryTheory.Mat_.embedding C).mapIso (w i)).symm) ≪≫
    N.isoBiproductEmbedding.symm

end CategoryTheory.Mat_
