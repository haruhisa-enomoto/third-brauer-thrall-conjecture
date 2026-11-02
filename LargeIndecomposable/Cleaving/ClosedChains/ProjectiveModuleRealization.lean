module

public import LargeIndecomposable.Modules.Idempotents.IdempotentProjectiveCategory
public import LargeIndecomposable.Foundations.CategoryTheory.LinearMat
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import LargeIndecomposable.Modules.Idempotents.OrthogonalIdempotentModule
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.RingHom

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x z

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

variable (F : CategoryTheory.Functor S.ProjectiveCategory (ModuleCat.{z} k))
variable [F.Additive] [F.Linear k]

/-- The direct sum of all values of a representation of the primitive-
projective category.  Since the index is finite, a dependent product is the
same finite biproduct on underlying vector spaces. -/
abbrev realizedCarrier := ∀ i : S.ProjectiveIndex, F.obj i

/-- A matrix endomorphism of the projective generator acts on the direct sum
of the values of `F`. -/
def projectiveEndAction (q : S.ProjectiveEndAlgebra) :
    Module.End k (realizedCarrier S F) where
  toFun m j := ∑ i : S.ProjectiveIndex, F.map (q i j) (m i)
  map_add' m n := by
    funext j
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c m := by
    funext j
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]
    rfl

/-- Applying a linear primitive-projective representation to matrix
endomorphisms is an algebra homomorphism. -/
def projectiveEndActionAlgHom :
    S.ProjectiveEndAlgebra →ₐ[k] Module.End k (realizedCarrier S F) where
  toFun := projectiveEndAction S F
  map_zero' := by
    apply LinearMap.ext
    intro m
    funext j
    change (∑ i : S.ProjectiveIndex,
      F.map (0 : i ⟶ j) (m i)) = 0
    simp
  map_one' := by
    apply LinearMap.ext
    intro m
    funext j
    classical
    change (∑ i : S.ProjectiveIndex,
      F.map ((𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra) i j)
        (m i)) = m j
    rw [Finset.sum_eq_single j]
    · rw [CategoryTheory.Mat_.id_apply_self, F.map_id]
      rfl
    · intro i _ hij
      rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ hij, F.map_zero]
      rfl
    · simp
  map_add' q r := by
    apply LinearMap.ext
    intro m
    funext j
    classical
    change (∑ i : S.ProjectiveIndex,
      F.map (q i j + r i j) (m i)) =
        (∑ i : S.ProjectiveIndex, F.map (q i j) (m i)) +
          ∑ i : S.ProjectiveIndex, F.map (r i j) (m i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [F.map_add]
    rfl
  map_mul' q r := by
    apply LinearMap.ext
    intro m
    funext j
    classical
    rw [CategoryTheory.End.mul_def]
    change
      (∑ i : S.ProjectiveIndex, F.map ((r ≫ q) i j) (m i)) =
        ∑ z : S.ProjectiveIndex, F.map (q z j)
          (∑ i : S.ProjectiveIndex, F.map (r i z) (m i))
    have hcomp (i : S.ProjectiveIndex) :
        ((show S.projectiveGenerator ⟶ S.projectiveGenerator from r) ≫
          (show S.projectiveGenerator ⟶ S.projectiveGenerator from q)) i j =
            ∑ z : S.ProjectiveIndex, r i z ≫ q z j := by
      exact CategoryTheory.Mat_.comp_apply _ _ _ _
    simp_rw [hcomp, F.map_sum, F.map_comp]
    have happ (i : S.ProjectiveIndex) :
        (∑ z : S.ProjectiveIndex, F.map (r i z) ≫ F.map (q z j))
            (m i) =
          ∑ z : S.ProjectiveIndex,
            F.map (q z j) (F.map (r i z) (m i)) := by
      change ((∑ z : S.ProjectiveIndex,
        F.map (r i z) ≫ F.map (q z j)) :
          F.obj i ⟶ F.obj j).hom (m i) = _
      rw [ModuleCat.hom_sum]
      simp only [LinearMap.coe_sum, Finset.sum_apply, ModuleCat.hom_comp,
        LinearMap.coe_comp, Function.comp_apply]
    simp_rw [happ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_sum]
  commutes' c := by
    apply LinearMap.ext
    intro m
    funext j
    classical
    change (∑ i : S.ProjectiveIndex,
      F.map ((c • (𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra)) i j)
        (m i)) = c • m j
    rw [Finset.sum_eq_single j]
    · change F.map
          (c • ((𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra) j j))
            (m j) = c • m j
      rw [CategoryTheory.Mat_.id_apply_self,
        F.map_smul, F.map_id]
      rfl
    · intro i _ hij
      change F.map
          (c • ((𝟙 S.projectiveGenerator : S.ProjectiveEndAlgebra) i j))
            (m i) = 0
      rw [CategoryTheory.Mat_.id_apply_of_ne _ _ _ hij,
        smul_zero, F.map_zero]
      rfl
    · simp

/-- The algebra action induced by a linear primitive-projective
representation. -/
def realizedActionAlgHom :
    A →ₐ[k] Module.End k (realizedCarrier S F) :=
  (projectiveEndActionAlgHom S F).comp S.projectiveEndAlgEquiv.toAlgHom

/-- The induced left `A`-module structure. -/
abbrev realizedModuleA : Module A (realizedCarrier S F) :=
  Module.compHom _ (realizedActionAlgHom S F).toRingHom

/-- The induced `A`-module attached to a linear representation of the
primitive-projective category. -/
@[reducible] def realizedModule : ModuleCat.{z} A := by
  letI : Module A (realizedCarrier S F) := realizedModuleA S F
  exact ModuleCat.of A (realizedCarrier S F)

theorem realizedModule_scalarTower :
    letI : Module A (realizedCarrier S F) := realizedModuleA S F
    IsScalarTower k A (realizedCarrier S F) := by
  letI : Module A (realizedCarrier S F) := realizedModuleA S F
  constructor
  intro c a m
  change (realizedActionAlgHom S F) (c • a) m =
    c • (realizedActionAlgHom S F a) m
  rw [map_smul]
  rfl

/-- The original coefficient-space structure on the direct sum agrees with
the one obtained by restricting the realized `A`-module along `k → A`. -/
def realizedCarrierToModuleLinearEquiv :
    realizedCarrier S F ≃ₗ[k] realizedModule S F where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c m := by
    rfl

/-- Pointwise finite-dimensionality makes the realized module
finite-dimensional over the coefficient field. -/
theorem realizedModule_finite
    [∀ i : S.ProjectiveIndex, Module.Finite k (F.obj i)] :
    Module.Finite k (realizedModule S F) := by
  letI : Module.Finite k (realizedCarrier S F) := by infer_instance
  exact Module.Finite.equiv (realizedCarrierToModuleLinearEquiv S F)

@[simp]
theorem projectiveComponentMatrix_idempotent_apply_self
    (i : S.ProjectiveIndex) :
    S.projectiveComponentMatrix
        (S.idempotent (S.projectiveVertex i)) i i =
      (𝟙 i : i ⟶ i) := by
  apply Subtype.ext
  change S.idempotent (S.projectiveVertex i) *
      S.idempotent (S.projectiveVertex i) *
        S.idempotent (S.projectiveVertex i) =
      S.idempotent (S.projectiveVertex i)
  rw [S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex i) |>.eq,
    S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex i) |>.eq]

@[simp]
theorem projectiveComponentMatrix_idempotent_apply_zero_of_target_ne
    (i l j : S.ProjectiveIndex) (hji : j ≠ i) :
    S.projectiveComponentMatrix
        (S.idempotent (S.projectiveVertex i)) l j = 0 := by
  apply Subtype.ext
  change S.idempotent (S.projectiveVertex j) *
      S.idempotent (S.projectiveVertex i) *
        S.idempotent (S.projectiveVertex l) = 0
  rw [S.complete.toOrthogonalIdempotents.ortho
      (fun h ↦ hji (S.projectiveVertex_injective h)),
    zero_mul]

@[simp]
theorem projectiveComponentMatrix_idempotent_apply_zero_of_source_ne
    (i l j : S.ProjectiveIndex) (hli : l ≠ i) :
    S.projectiveComponentMatrix
        (S.idempotent (S.projectiveVertex i)) l j = 0 := by
  apply Subtype.ext
  change S.idempotent (S.projectiveVertex j) *
      S.idempotent (S.projectiveVertex i) *
        S.idempotent (S.projectiveVertex l) = 0
  rw [mul_assoc,
    S.complete.toOrthogonalIdempotents.ortho
      (fun h ↦ hli (S.projectiveVertex_injective h).symm),
    mul_zero]

/-- The selected primitive idempotent acts on the realized direct sum as
the coordinate projector. -/
theorem realizedActionAlgHom_idempotent_apply
    (i : S.ProjectiveIndex) (m : realizedCarrier S F)
    (j : S.ProjectiveIndex) :
    (realizedActionAlgHom S F (S.idempotent (S.projectiveVertex i))) m j =
      if h : j = i then h ▸ m i else 0 := by
  classical
  unfold realizedActionAlgHom
  change (∑ l : S.ProjectiveIndex,
    F.map (S.projectiveComponentMatrix
      (S.idempotent (S.projectiveVertex i)) l j) (m l)) = _
  by_cases hji : j = i
  · subst j
    simp only [dite_true]
    rw [Finset.sum_eq_single i]
    · rw [projectiveComponentMatrix_idempotent_apply_self, F.map_id]
      rfl
    · intro l _ hli
      rw [projectiveComponentMatrix_idempotent_apply_zero_of_source_ne
        S i l i hli, F.map_zero]
      rfl
    · simp
  · simp only [dite_false, hji]
    apply Finset.sum_eq_zero
    intro l _
    rw [projectiveComponentMatrix_idempotent_apply_zero_of_target_ne
      S i l j hji, F.map_zero]
    rfl

/-- A primitive-corner algebra element acts on the target coordinate by the
given morphism of the representation. -/
theorem realizedActionAlgHom_corner_apply
    {i j : S.ProjectiveIndex} (f : i ⟶ j)
    (m : realizedCarrier S F) :
    (realizedActionAlgHom S F f.1) m j = F.map f (m i) := by
  classical
  unfold realizedActionAlgHom
  change (∑ l : S.ProjectiveIndex,
    F.map (S.projectiveComponentMatrix f.1 l j) (m l)) = _
  rw [Finset.sum_eq_single i]
  · have hentry : S.projectiveComponentMatrix f.1 i j = f := by
      apply Subtype.ext
      change S.idempotent (S.projectiveVertex j) * f.1 *
        S.idempotent (S.projectiveVertex i) = f.1
      rw [ProjectiveCategory.idempotent_mul_val,
        ProjectiveCategory.val_mul_idempotent]
    rw [hentry]
  · intro l _ hli
    have hentry : S.projectiveComponentMatrix f.1 l j = 0 := by
      apply Subtype.ext
      change S.idempotent (S.projectiveVertex j) * f.1 *
        S.idempotent (S.projectiveVertex l) = 0
      rw [ProjectiveCategory.idempotent_mul_val,
        ProjectiveCategory.val_mul_idempotent_eq_zero_of_ne
          S (Ne.symm hli)]
    rw [hentry, F.map_zero]
    rfl
  · simp

section Restriction

variable (M : ModuleCat.{z} A)

/-- The primitive-idempotent component of an `A`-module. -/
abbrev projectiveRestrictionComponent (i : S.ProjectiveCategory) :=
  LargeIndecomposable.idempotentModuleComponent
    (k := k) (M := M)
    (fun j : S.ProjectiveIndex ↦ S.idempotent (S.projectiveVertex j)) i

/-- A primitive-corner morphism acts between the corresponding idempotent
components of an `A`-module. -/
def projectiveRestrictionMap {i j : S.ProjectiveCategory} (f : i ⟶ j) :
    projectiveRestrictionComponent S M i →ₗ[k]
      projectiveRestrictionComponent S M j :=
  ((LargeIndecomposable.algebraElementAction
      (k := k) (M := M) f.1).comp
        (projectiveRestrictionComponent S M i).subtype).codRestrict
    (projectiveRestrictionComponent S M j) (fun m ↦ by
      refine ⟨f.1 • (m : M), ?_⟩
      change S.idempotent (S.projectiveVertex j) •
          (f.1 • (m : M)) = f.1 • (m : M)
      rw [← mul_smul, ProjectiveCategory.idempotent_mul_val])

@[simp]
theorem projectiveRestrictionMap_coe {i j : S.ProjectiveCategory}
    (f : i ⟶ j) (m : projectiveRestrictionComponent S M i) :
    ((projectiveRestrictionMap S M f m :
      projectiveRestrictionComponent S M j) : M) = f.1 • (m : M) :=
  rfl

/-- Restriction of an `A`-module to the chosen primitive-projective
category. -/
def projectiveRestrictionObj :
    S.ProjectiveCategory ⥤ ModuleCat.{z} k where
  obj i := ModuleCat.of k (projectiveRestrictionComponent S M i)
  map f := ModuleCat.ofHom (projectiveRestrictionMap S M f)
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change S.idempotent (S.projectiveVertex i) • (m : M) = (m : M)
    obtain ⟨x, hx⟩ := m.2
    change S.idempotent (S.projectiveVertex i) • x = (m : M) at hx
    rw [← hx, ← mul_smul,
      S.complete.toOrthogonalIdempotents.idem (S.projectiveVertex i) |>.eq]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change
      ((projectiveRestrictionMap S M (f ≫ g) m :
        projectiveRestrictionComponent S M _) : M) =
      ((projectiveRestrictionMap S M g
        (projectiveRestrictionMap S M f m) :
          projectiveRestrictionComponent S M _) : M)
    rw [projectiveRestrictionMap_coe, projectiveRestrictionMap_coe,
      projectiveRestrictionMap_coe, ProjectiveCategory.comp_val]
    rw [mul_smul]

instance projectiveRestrictionObj_additive :
    (projectiveRestrictionObj S M).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change projectiveRestrictionComponent S M X at m
    apply Subtype.ext
    change (f.1 + g.1) • (m : M) =
      f.1 • (m : M) + g.1 • (m : M)
    exact add_smul _ _ _

instance projectiveRestrictionObj_linear :
    (projectiveRestrictionObj S M).Linear k where
  map_smul f c := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change projectiveRestrictionComponent S M _ at m
    apply Subtype.ext
    change (c • f.1) • (m : M) = c • (f.1 • (m : M))
    rw [Algebra.smul_def, mul_smul]
    rfl

end Restriction

section RestrictionFunctor

variable {M N P : ModuleCat.{z} A}

/-- An `A`-linear map restricts to every primitive-idempotent component. -/
def projectiveRestrictionHomApp (φ : M ⟶ N)
    (i : S.ProjectiveCategory) :
    projectiveRestrictionComponent S M i →ₗ[k]
      projectiveRestrictionComponent S N i :=
  (((φ.hom.restrictScalars k).comp
      (projectiveRestrictionComponent S M i).subtype).codRestrict
    (projectiveRestrictionComponent S N i) (fun m ↦ by
      obtain ⟨x, hx⟩ := m.2
      refine ⟨φ x, ?_⟩
      change S.idempotent (S.projectiveVertex i) • φ x = φ (m : M)
      change S.idempotent (S.projectiveVertex i) • x = (m : M) at hx
      rw [← hx]
      exact (φ.hom.map_smul _ _).symm))

@[simp]
theorem projectiveRestrictionHomApp_coe (φ : M ⟶ N)
    (i : S.ProjectiveCategory)
    (m : projectiveRestrictionComponent S M i) :
    ((projectiveRestrictionHomApp S φ i m :
      projectiveRestrictionComponent S N i) : N) = φ (m : M) :=
  rfl

/-- Restriction on a module morphism, as a natural transformation between
primitive-projective representations. -/
def projectiveRestrictionHom (φ : M ⟶ N) :
    projectiveRestrictionObj S M ⟶ projectiveRestrictionObj S N where
  app i := ModuleCat.ofHom (projectiveRestrictionHomApp S φ i)
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change projectiveRestrictionComponent S M i at m
    apply Subtype.ext
    change φ (f.1 • (m : M)) = f.1 • φ (m : M)
    exact φ.hom.map_smul f.1 (m : M)

/-- Restriction from `A`-modules to linear representations of the chosen
primitive-projective category. -/
def projectiveRestriction :
    ModuleCat.{z} A ⥤
      (S.ProjectiveCategory ⥤ ModuleCat.{z} k) where
  obj M := projectiveRestrictionObj S M
  map φ := projectiveRestrictionHom S φ
  map_id M := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    rfl
  map_comp φ ψ := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    rfl

instance projectiveRestriction_additive :
    (projectiveRestriction (k := k) S).Additive where
  map_add := by
    intro M N φ ψ
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    rfl

end RestrictionFunctor

section RealizationRestriction

/-- Evaluation at a primitive coordinate on the corresponding idempotent
component of the realized module. -/
def realizedRestrictionEval (i : S.ProjectiveIndex) :
    projectiveRestrictionComponent S (realizedModule S F) i →ₗ[k]
      F.obj i where
  toFun m := (m.1 : realizedCarrier S F) i
  map_add' _ _ := rfl
  map_smul' c m := by
    change (realizedActionAlgHom S F (algebraMap k A c))
        (m.1 : realizedCarrier S F) i =
      (RingHom.id k) c • (m.1 : realizedCarrier S F) i
    rw [(realizedActionAlgHom S F).commutes]
    rfl

/-- Insert a vector as the single nonzero coordinate of the realized module;
it lies in the matching primitive-idempotent component. -/
def realizedRestrictionSingle (i : S.ProjectiveIndex) :
    F.obj i →ₗ[k]
      projectiveRestrictionComponent S (realizedModule S F) i := by
  classical
  refine
    { toFun := fun x ↦ ⟨Pi.single i x, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · refine ⟨Pi.single i x, ?_⟩
    change (realizedActionAlgHom S F
        (S.idempotent (S.projectiveVertex i))) (Pi.single i x) =
      Pi.single i x
    funext j
    rw [realizedActionAlgHom_idempotent_apply]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  · intro x y
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  · intro c x
    apply Subtype.ext
    change (Pi.single i (c • x) : realizedCarrier S F) =
      (realizedActionAlgHom S F (algebraMap k A c)) (Pi.single i x)
    rw [(realizedActionAlgHom S F).commutes]
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

/-- The primitive-idempotent component of the module realizing `F` is
canonically the value of `F` at that primitive projective. -/
def realizedRestrictionComponentLinearEquiv (i : S.ProjectiveIndex) :
    projectiveRestrictionComponent S (realizedModule S F) i ≃ₗ[k]
      F.obj i where
  toFun := realizedRestrictionEval S F i
  invFun := realizedRestrictionSingle S F i
  left_inv m := by
    apply Subtype.ext
    change (Pi.single i ((m : realizedCarrier S F) i) :
      realizedCarrier S F) = (m : realizedCarrier S F)
    funext j
    obtain ⟨w, hw⟩ := m.2
    change (realizedActionAlgHom S F
      (S.idempotent (S.projectiveVertex i))) w =
        (m : realizedCarrier S F) at hw
    by_cases hji : j = i
    · subst j
      simp
    · simp
      have hj := congrFun hw j
      rw [realizedActionAlgHom_idempotent_apply] at hj
      simpa [hji] using hj
  right_inv x := by
    change (Pi.single i x : realizedCarrier S F) i = x
    simp
  map_add' x y := (realizedRestrictionEval S F i).map_add x y
  map_smul' c x := (realizedRestrictionEval S F i).map_smul c x

/-- Realizing a linear representation and restricting it back to the chosen
primitive projectives recovers the original representation. -/
def realizedRestrictionNatIso :
    projectiveRestrictionObj S (realizedModule S F) ≅ F :=
  NatIso.ofComponents
    (fun i ↦ (realizedRestrictionComponentLinearEquiv S F i).toModuleIso)
    (fun {i j} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change projectiveRestrictionComponent S (realizedModule S F) i at m
      change (realizedActionAlgHom S F f.1)
          (m : realizedCarrier S F) j =
        F.map f ((m : realizedCarrier S F) i)
      exact realizedActionAlgHom_corner_apply S F f
        (m : realizedCarrier S F))

/-- The realization--restriction comparison remains an isomorphism after
precomposition by any source functor. -/
def realizedRestrictionWhiskerLeftNatIso
    {K : Type*} [Category K]
    (D : K ⥤ S.ProjectiveCategory) :
    D ⋙ projectiveRestrictionObj S (realizedModule S F) ≅ D ⋙ F :=
  NatIso.ofComponents
    (fun X ↦ (realizedRestrictionNatIso S F).app (D.obj X))
    (fun {_ _} f ↦
      (realizedRestrictionNatIso S F).hom.naturality (D.map f))

end RealizationRestriction

end LargeIndecomposable.SplitBasicIdempotents
