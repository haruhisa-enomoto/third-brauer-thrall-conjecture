module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteUniverse
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

def dualSMul (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ)
    (f : Module.Dual k M) : Module.Dual k M :=
  f.comp
    (Algebra.lsmul k k M (MulOpposite.unop a))

instance dualSMulInstance (M : ModuleCat.{w} A) :
    SMul Aᵐᵒᵖ (Module.Dual k M) :=
  ⟨dualSMul M⟩

theorem dual_one_smul (M : ModuleCat.{w} A)
    (f : Module.Dual k M) : (1 : Aᵐᵒᵖ) • f = f := by
  change dualSMul M 1 f = f
  ext x
  simp [dualSMul]

theorem dual_mul_smul (M : ModuleCat.{w} A)
    (a b : Aᵐᵒᵖ) (f : Module.Dual k M) :
    (a * b) • f = a • b • f := by
  change dualSMul M (a * b) f = dualSMul M a (dualSMul M b f)
  ext x
  simp [dualSMul]

theorem dual_smul_zero (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ) :
    a • (0 : Module.Dual k M) = 0 := by
  change dualSMul M a 0 = 0
  ext x
  simp [dualSMul]

theorem dual_smul_add (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ)
    (f g : Module.Dual k M) : a • (f + g) = a • f + a • g := by
  change dualSMul M a (f + g) = dualSMul M a f + dualSMul M a g
  ext x
  simp [dualSMul]

theorem dual_zero_smul (M : ModuleCat.{w} A)
    (f : Module.Dual k M) : (0 : Aᵐᵒᵖ) • f = 0 := by
  change dualSMul M 0 f = 0
  ext x
  simp [dualSMul]

theorem dual_add_smul (M : ModuleCat.{w} A)
    (a b : Aᵐᵒᵖ) (f : Module.Dual k M) :
    (a + b) • f = a • f + b • f := by
  change dualSMul M (a + b) f = dualSMul M a f + dualSMul M b f
  ext x
  simp [dualSMul]

instance dualModule (M : ModuleCat.{w} A) :
    Module Aᵐᵒᵖ (Module.Dual k M) where
  one_smul := dual_one_smul M
  mul_smul := dual_mul_smul M
  smul_zero := dual_smul_zero M
  smul_add := dual_smul_add M
  zero_smul := dual_zero_smul M
  add_smul := dual_add_smul M

def dualModuleObj (M : ModuleCat.{w} A) : ModuleCat.{max u w} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (Module.Dual k M)

@[simp] theorem dualModuleObj_smul_apply
    (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ) (f : dualModuleObj M) (x : M) :
    (show Module.Dual k M from a • f) x =
      (show Module.Dual k M from f) (MulOpposite.unop a • x) := by
  change (dualSMul M a (show Module.Dual k M from f)) x =
    (show Module.Dual k M from f) (MulOpposite.unop a • x)
  rfl

def dualMap {M N : ModuleCat.{w} A} (f : M ⟶ N) :
    dualModuleObj (k := k) N ⟶ dualModuleObj (k := k) M :=
  ModuleCat.ofHom
    { toFun := fun phi =>
        phi.comp (f.hom.restrictScalars k)
      map_add' := by
        intro phi psi
        ext x
        rfl
      map_smul' := by
        intro a phi
        ext x
        change phi (MulOpposite.unop a • f x) =
          phi (f (MulOpposite.unop a • x))
        rw [f.hom.map_smul] }

@[simp] theorem dualMap_apply {M N : ModuleCat.{w} A}
    (f : M ⟶ N) (phi : dualModuleObj (k := k) N) (x : M) :
    (show Module.Dual k M from dualMap (k := k) f phi) x =
      (show Module.Dual k N from phi) (f x) :=
  rfl

def dualFunctor : (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max u w} Aᵐᵒᵖ where
  obj M := dualModuleObj (k := k) M.unop
  map f := dualMap (k := k) f.unop
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change (show Module.Dual k M.unop from _) = _
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change (show Module.Dual k _ from _) = _
    apply LinearMap.ext
    intro x
    rfl

def dualModuleObjLinearEquiv (M : ModuleCat.{w} A) :
    Module.Dual k M ≃ₗ[k] dualModuleObj (k := k) M where
  toFun phi := phi
  invFun phi := phi
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r phi := by
    change (show Module.Dual k M from _) = _
    apply LinearMap.ext
    intro x
    change (r • phi) x =
      (show Module.Dual k M from
        (algebraMap k Aᵐᵒᵖ r) •
          (show dualModuleObj (k := k) M from phi)) x
    rw [dualModuleObj_smul_apply]
    simp

theorem dualModuleObj_moduleFinite (M : ModuleCat.{w} A)
    [Module.Finite k M] : Module.Finite k (dualModuleObj (k := k) M) := by
  exact (Module.Finite.equiv_iff (dualModuleObjLinearEquiv (k := k) M)).mp
    inferInstance

universe z y

/-- Universe-resized copy of a module. -/
def resizedModule (R : Type v) [Ring R] (M : ModuleCat.{w} R)
    [Small.{y} M] : ModuleCat.{y} R :=
  ModuleCat.of R (Shrink.{y} M)

def resizedModuleLinearEquiv (R : Type v) [Ring R]
    (M : ModuleCat.{w} R) [Small.{y} M] :
    resizedModule R M ≃ₗ[R] M :=
  Shrink.linearEquiv R M

theorem resizedModule_moduleFinite (R : Type v) [Ring R]
    (M : ModuleCat.{w} R) [Small.{y} M]
    {K : Type u} [Field K] [Algebra K R] [Module.Finite K M] :
    Module.Finite K (resizedModule R M) := by
  exact (Module.Finite.equiv_iff
    ((resizedModuleLinearEquiv R M).restrictScalars K)).mpr
      inferInstance

/-- Dualization of a cross-universe module equivalence. -/
def dualLinearEquiv {M : ModuleCat.{w} A} {N : ModuleCat.{z} A}
    (e : M ≃ₗ[A] N) :
    dualModuleObj (k := k) N ≃ₗ[Aᵐᵒᵖ] dualModuleObj (k := k) M where
  toFun phi := (e.restrictScalars k).dualMap phi
  invFun phi := (e.symm.restrictScalars k).dualMap phi
  left_inv phi := by
    apply LinearMap.ext
    intro x
    change (show Module.Dual k N from phi) (e (e.symm x)) =
      (show Module.Dual k N from phi) x
    rw [e.apply_symm_apply]
  right_inv phi := by
    apply LinearMap.ext
    intro x
    change (show Module.Dual k M from phi) (e.symm (e x)) =
      (show Module.Dual k M from phi) x
    rw [e.symm_apply_apply]
  map_add' phi psi := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a phi := by
    apply LinearMap.ext
    intro x
    change
      (show Module.Dual k N from a • phi) (e x) =
        (show Module.Dual k N from phi)
          (e (MulOpposite.unop a • x))
    rw [dualModuleObj_smul_apply, e.map_smul]

@[simp] theorem dualLinearEquiv_apply
    {M : ModuleCat.{w} A} {N : ModuleCat.{z} A}
    (e : M ≃ₗ[A] N) (phi : dualModuleObj (k := k) N) (x : M) :
    (show Module.Dual k M from dualLinearEquiv (k := k) e phi) x =
      (show Module.Dual k N from phi) (e x) :=
  rfl

/-- Over a field, dualization is faithful on linear maps once the codomain is
finite-dimensional. -/
theorem dualMap_injective {M N : ModuleCat.{w} A} [Module.Finite k N] :
    Function.Injective (dualMap (k := k) : (M ⟶ N) →
      (dualModuleObj (k := k) N ⟶ dualModuleObj (k := k) M)) := by
  intro f g hfg
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (Module.bijective_dual_eval k N).injective
  apply LinearMap.ext
  intro phi
  have hpoint := congrArg
    (fun h : dualModuleObj (k := k) N ⟶ dualModuleObj (k := k) M =>
      h (show dualModuleObj (k := k) N from phi)) hfg
  have hvalue := congrArg
    (fun psi : dualModuleObj (k := k) M =>
      (show Module.Dual k M from psi) x) hpoint
  exact hvalue

/-- The dual of a left `Aᵐᵒᵖ`-module, regarded again as a left `A`-module
through the canonical equivalence `A ≃ Aᵐᵒᵖᵐᵒᵖ`. -/
def dualBackObj (N : ModuleCat.{w} Aᵐᵒᵖ) : ModuleCat.{max u w} A :=
  (ModuleCat.restrictScalars
    (AlgEquiv.opOp k A).toRingEquiv.toRingHom).obj
      (dualModuleObj (k := k) N)

def dualBackMap {M N : ModuleCat.{w} Aᵐᵒᵖ} (f : M ⟶ N) :
    dualBackObj (k := k) N ⟶ dualBackObj (k := k) M :=
  (ModuleCat.restrictScalars
    (AlgEquiv.opOp k A).toRingEquiv.toRingHom).map
      (dualMap (k := k) f)

@[simp] theorem dualBackMap_zero (M N : ModuleCat.{w} Aᵐᵒᵖ) :
    dualBackMap (k := k) (0 : M ⟶ N) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (show Module.Dual k M from _) = 0
  apply LinearMap.ext
  intro x
  change
    (show Module.Dual k M from
      dualMap (k := k) (0 : M ⟶ N)
        (show dualModuleObj (k := k) N from phi)) x = 0
  change (show Module.Dual k N from phi) ((0 : M ⟶ N) x) = 0
  have hzero : (0 : M ⟶ N) x = 0 := rfl
  rw [hzero]
  exact map_zero (show Module.Dual k N from phi)

@[simp] theorem dualBackMap_id (M : ModuleCat.{w} Aᵐᵒᵖ) :
    dualBackMap (k := k) (𝟙 M) = 𝟙 (dualBackObj (k := k) M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (show Module.Dual k M from _) =
    (show Module.Dual k M from phi)
  apply LinearMap.ext
  intro x
  rfl

theorem dualBackMap_comp {L M N : ModuleCat.{w} Aᵐᵒᵖ}
    (f : L ⟶ M) (g : M ⟶ N) :
    dualBackMap (k := k) (f ≫ g) =
      dualBackMap (k := k) g ≫ dualBackMap (k := k) f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change (show Module.Dual k L from _) = _
  apply LinearMap.ext
  intro x
  rfl

theorem dualBackMap_injective {M N : ModuleCat.{w} Aᵐᵒᵖ}
    [Module.Finite k N] :
    Function.Injective (dualBackMap (k := k) : (M ⟶ N) →
      (dualBackObj (k := k) N ⟶ dualBackObj (k := k) M)) := by
  intro f g hfg
  apply dualMap_injective (k := k)
  apply (ModuleCat.restrictScalars
    (AlgEquiv.opOp k A).toRingEquiv.toRingHom).map_injective
  exact hfg

@[simp] theorem dualBackObj_smul_apply
    (N : ModuleCat.{w} Aᵐᵒᵖ) (a : A) (f : dualBackObj (k := k) N)
    (x : N) :
    (show Module.Dual k N from a • f) x =
      (show Module.Dual k N from f) (MulOpposite.op a • x) := by
  change
    (show Module.Dual k N from
      (MulOpposite.op (MulOpposite.op a) : Aᵐᵒᵖᵐᵒᵖ) •
        (show dualModuleObj (k := k) N from f)) x = _
  rw [dualModuleObj_smul_apply]
  rfl

def dualBackObjLinearEquiv (N : ModuleCat.{w} Aᵐᵒᵖ) :
    Module.Dual k N ≃ₗ[k] dualBackObj (k := k) N where
  toFun phi := phi
  invFun phi := phi
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r phi := by
    change (show Module.Dual k N from r • phi) =
      (show Module.Dual k N from
        (algebraMap k A r) •
          (show dualBackObj (k := k) N from phi))
    apply LinearMap.ext
    intro x
    rw [dualBackObj_smul_apply]
    rw [show MulOpposite.op (algebraMap k A r) =
      algebraMap k Aᵐᵒᵖ r from rfl]
    rw [algebraMap_smul, map_smul]
    rfl

theorem dualBackObj_moduleFinite (N : ModuleCat.{w} Aᵐᵒᵖ)
    [Module.Finite k N] : Module.Finite k (dualBackObj (k := k) N) := by
  exact (Module.Finite.equiv_iff (dualBackObjLinearEquiv (k := k) N)).mp
    inferInstance

/-- The same module carrier placed in the universe of its double dual. -/
def largeModuleObj (_k : Type u) (M : ModuleCat.{w} A) :
    ModuleCat.{max u w} A :=
  ModuleCat.of A (Shrink.{max u w} M)

def largeModuleObjLinearEquiv (M : ModuleCat.{w} A) :
    largeModuleObj k M ≃ₗ[A] M :=
  Shrink.linearEquiv A M

/-- Evaluation as a functional on the dual object equipped with the scalar
structure restricted from `Aᵐᵒᵖ`. -/
def evalFunctional (M : ModuleCat.{w} A) (x : M) :
    Module.Dual k (dualModuleObj (k := k) M) :=
  (dualModuleObjLinearEquiv (k := k) M).dualMap.symm
    (Module.Dual.eval k M x)

@[simp] theorem evalFunctional_apply (M : ModuleCat.{w} A) (x : M)
    (phi : dualModuleObj (k := k) M) :
    evalFunctional (k := k) M x phi =
      (show Module.Dual k M from phi) x :=
  rfl

/-- Evaluation into the double dual is linear over the original algebra. -/
def evalHom (M : ModuleCat.{w} A) :
    largeModuleObj k M ⟶
      dualBackObj (k := k) (dualModuleObj (k := k) M) :=
  ModuleCat.ofHom
    (X := largeModuleObj k M)
    (Y := dualBackObj (k := k) (dualModuleObj (k := k) M))
    { toFun := fun x =>
        evalFunctional (k := k) M
          (largeModuleObjLinearEquiv (k := k) M x)
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro phi
        change
          (show Module.Dual k M from phi)
              (largeModuleObjLinearEquiv (k := k) M (x + y)) =
            (evalFunctional (k := k) M
                (largeModuleObjLinearEquiv (k := k) M x) +
              evalFunctional (k := k) M
                (largeModuleObjLinearEquiv (k := k) M y)) phi
        rw [(largeModuleObjLinearEquiv (k := k) M).map_add]
        exact map_add (show Module.Dual k M from phi) _ _
      map_smul' := by
        intro a x
        change
          (show Module.Dual k (dualModuleObj (k := k) M) from
            evalFunctional (k := k) M
              (largeModuleObjLinearEquiv (k := k) M (a • x))) =
          (show Module.Dual k (dualModuleObj (k := k) M) from
            a • (show dualBackObj (k := k)
              (dualModuleObj (k := k) M) from
                evalFunctional (k := k) M
                  (largeModuleObjLinearEquiv (k := k) M x)))
        apply LinearMap.ext
        intro phi
        change
          (show Module.Dual k M from phi)
              (largeModuleObjLinearEquiv (k := k) M (a • x)) =
          (show Module.Dual k (dualModuleObj (k := k) M) from
            a • (show dualBackObj (k := k)
              (dualModuleObj (k := k) M) from
                evalFunctional (k := k) M
                  (largeModuleObjLinearEquiv (k := k) M x))) phi
        rw [dualBackObj_smul_apply]
        rw [(largeModuleObjLinearEquiv (k := k) M).map_smul]
        rw [evalFunctional_apply, dualModuleObj_smul_apply]
        simp }

@[simp] theorem evalHom_apply (M : ModuleCat.{w} A) (x : largeModuleObj k M)
    (phi : dualModuleObj (k := k) M) :
    (show Module.Dual k (dualModuleObj (k := k) M) from
      evalHom (k := k) M x) phi =
      (show Module.Dual k M from phi)
        (largeModuleObjLinearEquiv (k := k) M x) :=
  by
    change (evalFunctional (k := k) M
      (largeModuleObjLinearEquiv (k := k) M x)) phi = _
    rfl

theorem evalHom_bijective (M : ModuleCat.{w} A) [Module.Finite k M] :
    Function.Bijective (evalHom (k := k) M) := by
  change Function.Bijective (fun x =>
    evalFunctional (k := k) M
      (largeModuleObjLinearEquiv (k := k) M x))
  exact (dualModuleObjLinearEquiv (k := k) M).dualMap.symm.bijective.comp
    ((Module.bijective_dual_eval k M).comp
      (largeModuleObjLinearEquiv (k := k) M).bijective)

/-- Finite-dimensional modules are canonically isomorphic, as `A`-modules,
to their double duals. -/
def evalIso (M : ModuleCat.{w} A) [Module.Finite k M] :
    largeModuleObj k M ≅
      dualBackObj (k := k) (dualModuleObj (k := k) M) :=
  (LinearEquiv.ofBijective (evalHom (k := k) M).hom
    (evalHom_bijective (k := k) M)).toModuleIso

/-- Finite-dimensional duality preserves indecomposability. -/
theorem dualModuleObj_indecomposable (M : ModuleCat.{w} A)
    [Module.Finite k M] (hM : Indecomposable M) :
    Indecomposable (dualModuleObj (k := k) M) := by
  let E := largeModuleObjLinearEquiv (k := k) M
  have hlarge : Indecomposable (largeModuleObj k M) :=
    (indecomposable_iff_of_crossUniverse_linearEquiv E).mpr hM
  have hdouble : Indecomposable
      (dualBackObj (k := k) (dualModuleObj (k := k) M)) :=
    (indecomposable_iff_of_iso (evalIso (k := k) M)).mp hlarge
  letI : Module.Finite k (dualModuleObj (k := k) M) :=
    dualModuleObj_moduleFinite (k := k) M
  apply indecomposable_of_idempotent_eq_zero_or_id_preadditive
  · intro hdualZero
    have hdualSub : Subsingleton (dualModuleObj (k := k) M) :=
      ModuleCat.subsingleton_of_isZero hdualZero
    have hbackSub : Subsingleton
        (dualBackObj (k := k) (dualModuleObj (k := k) M)) := by
      constructor
      intro f g
      change (show Module.Dual k (dualModuleObj (k := k) M) from f) =
        (show Module.Dual k (dualModuleObj (k := k) M) from g)
      apply LinearMap.ext
      intro x
      have hx : x = 0 := hdualSub.elim x 0
      subst x
      change
        (show Module.Dual k (dualModuleObj (k := k) M) from f) 0 =
          (show Module.Dual k (dualModuleObj (k := k) M) from g) 0
      rw [map_zero, map_zero]
    letI : Subsingleton
        (dualBackObj (k := k) (dualModuleObj (k := k) M)) := hbackSub
    have hbackZero : IsZero
        (dualBackObj (k := k) (dualModuleObj (k := k) M)) :=
      ModuleCat.isZero_of_subsingleton _
    exact hlarge.1 ((evalIso (k := k) M).isZero_iff.mpr hbackZero)
  · intro p hp
    let q := dualBackMap (k := k) p
    have hq : q ≫ q = q := by
      calc
        q ≫ q = dualBackMap (k := k) (p ≫ p) :=
          (dualBackMap_comp (k := k) p p).symm
        _ = q := congrArg (dualBackMap (k := k)) hp
    rcases idempotent_eq_zero_or_id_of_indecomposable_preadditive hdouble q hq with
      hq0 | hq1
    · left
      apply dualBackMap_injective (k := k)
      simpa [q] using hq0
    · right
      apply dualBackMap_injective (k := k)
      simpa [q] using hq1

/-- Finite-dimensional duality followed by the canonical double-opposite
restriction preserves indecomposability. -/
theorem dualBackObj_indecomposable (N : ModuleCat.{w} Aᵐᵒᵖ)
    [Module.Finite k N] (hN : Indecomposable N) :
    Indecomposable (dualBackObj (k := k) N) := by
  let E : ModuleCat.{max u w} Aᵐᵒᵖᵐᵒᵖ ≌ ModuleCat.{max u w} A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (AlgEquiv.opOp k A).toRingEquiv
  have hdual : Indecomposable (dualModuleObj (k := k) N) :=
    dualModuleObj_indecomposable (k := k) N hN
  exact (indecomposable_functor_obj_iff E
    (dualModuleObj (k := k) N)).mpr hdual

/-- Evaluation as a functional on the dual whose double-opposite scalar
structure has already been restricted back to `A`. -/
def backEvalFunctional (N : ModuleCat.{w} Aᵐᵒᵖ) (x : N) :
    Module.Dual k (dualBackObj (k := k) N) :=
  (dualBackObjLinearEquiv (k := k) N).dualMap.symm
    (Module.Dual.eval k N x)

@[simp] theorem backEvalFunctional_apply (N : ModuleCat.{w} Aᵐᵒᵖ)
    (x : N) (phi : dualBackObj (k := k) N) :
    backEvalFunctional (k := k) N x phi =
      (show Module.Dual k N from phi) x :=
  rfl

/-- Direct `Aᵐᵒᵖ`-linear evaluation from a module to the dual of its
dual restricted along `A ≃ Aᵐᵒᵖᵐᵒᵖ`. -/
def backEvalHom (N : ModuleCat.{w} Aᵐᵒᵖ) :
    largeModuleObj k N ⟶
      dualModuleObj (k := k) (dualBackObj (k := k) N) :=
  ModuleCat.ofHom
    (X := largeModuleObj k N)
    (Y := dualModuleObj (k := k) (dualBackObj (k := k) N))
    { toFun := fun x =>
        backEvalFunctional (k := k) N
          (largeModuleObjLinearEquiv (k := k) N x)
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro phi
        change
          (show Module.Dual k N from phi)
              (largeModuleObjLinearEquiv (k := k) N (x + y)) =
            (backEvalFunctional (k := k) N
                (largeModuleObjLinearEquiv (k := k) N x) +
              backEvalFunctional (k := k) N
                (largeModuleObjLinearEquiv (k := k) N y)) phi
        rw [(largeModuleObjLinearEquiv (k := k) N).map_add]
        exact map_add (show Module.Dual k N from phi) _ _
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro phi
        change
          (show Module.Dual k N from phi)
              (largeModuleObjLinearEquiv (k := k) N (a • x)) =
          (show Module.Dual k (dualBackObj (k := k) N) from
            a • (show dualModuleObj (k := k)
              (dualBackObj (k := k) N) from
                backEvalFunctional (k := k) N
                  (largeModuleObjLinearEquiv (k := k) N x))) phi
        rw [dualModuleObj_smul_apply]
        rw [(largeModuleObjLinearEquiv (k := k) N).map_smul]
        simp }

theorem backEvalHom_bijective (N : ModuleCat.{w} Aᵐᵒᵖ)
    [Module.Finite k N] : Function.Bijective (backEvalHom (k := k) N) := by
  change Function.Bijective (fun x =>
    backEvalFunctional (k := k) N
      (largeModuleObjLinearEquiv (k := k) N x))
  exact (dualBackObjLinearEquiv (k := k) N).dualMap.symm.bijective.comp
    ((Module.bijective_dual_eval k N).comp
      (largeModuleObjLinearEquiv (k := k) N).bijective)

def backEvalIso (N : ModuleCat.{w} Aᵐᵒᵖ) [Module.Finite k N] :
    largeModuleObj k N ≅
      dualModuleObj (k := k) (dualBackObj (k := k) N) :=
  (LinearEquiv.ofBijective (backEvalHom (k := k) N).hom
    (backEvalHom_bijective (k := k) N)).toModuleIso

/-- A nontrivial representation-finite algebra has representation-finite
opposite algebra. -/
theorem IsRepresentationFinite.op [Nontrivial A]
    (hA : IsRepresentationFinite k A) :
    IsRepresentationFinite k Aᵐᵒᵖ := by
  letI : Small.{v} k :=
    small_of_injective (FaithfulSMul.algebraMap_injective k A)
  obtain ⟨n, X, hX, hcover⟩ := hA
  let DX : Fin n → ModuleCat.{max u v} Aᵐᵒᵖ := fun i =>
    dualModuleObj (k := k) (X i)
  have hDXfinite (i : Fin n) : Module.Finite k (DX i) := by
    letI : Module.Finite k (X i) := (hX i).1
    exact dualModuleObj_moduleFinite (k := k) (X i)
  let Y : Fin n → ModuleCat.{v} Aᵐᵒᵖ := fun i =>
    letI : Module.Finite k (DX i) := hDXfinite i
    letI : Small.{v} (DX i) := Module.Finite.small.{v} k (DX i)
    resizedModule Aᵐᵒᵖ (DX i)
  refine ⟨n, Y, ?_, ?_⟩
  · intro i
    letI : Module.Finite k (X i) := (hX i).1
    letI : Module.Finite k (DX i) := hDXfinite i
    letI : Small.{v} (DX i) := Module.Finite.small.{v} k (DX i)
    have hDXind : Indecomposable (DX i) :=
      dualModuleObj_indecomposable (k := k) (X i) (hX i).2
    exact
      ⟨resizedModule_moduleFinite Aᵐᵒᵖ (DX i),
        (indecomposable_iff_of_crossUniverse_linearEquiv
          (resizedModuleLinearEquiv Aᵐᵒᵖ (DX i))).mpr hDXind⟩
  · intro M hM
    letI : Module.Finite k M := hM.1
    let D : ModuleCat.{max u v} A := dualBackObj (k := k) M
    have hDfinite : Module.Finite k D :=
      dualBackObj_moduleFinite (k := k) M
    letI : Module.Finite k D := hDfinite
    letI : Small.{v} D := Module.Finite.small.{v} k D
    let T : ModuleCat.{v} A := resizedModule A D
    have hTfinite : Module.Finite k T :=
      resizedModule_moduleFinite A D
    have hDind : Indecomposable D :=
      dualBackObj_indecomposable (k := k) M hM.2
    have hTind : Indecomposable T :=
      (indecomposable_iff_of_crossUniverse_linearEquiv
        (resizedModuleLinearEquiv A D)).mpr hDind
    obtain ⟨i, ⟨e⟩⟩ := hcover T ⟨hTfinite, hTind⟩
    letI : Module.Finite k (X i) := (hX i).1
    letI : Module.Finite k (DX i) := hDXfinite i
    letI : Small.{v} (DX i) := Module.Finite.small.{v} k (DX i)
    let eDouble : M ≃ₗ[Aᵐᵒᵖ] dualModuleObj (k := k) D :=
      (largeModuleObjLinearEquiv (k := k) M).symm.trans
        (backEvalIso (k := k) M).toLinearEquiv
    let eResizeDual : dualModuleObj (k := k) D ≃ₗ[Aᵐᵒᵖ]
        dualModuleObj (k := k) T :=
      dualLinearEquiv (k := k) (resizedModuleLinearEquiv A D)
    let eCoverDual : dualModuleObj (k := k) T ≃ₗ[Aᵐᵒᵖ] DX i :=
      (dualLinearEquiv (k := k) e.toLinearEquiv).symm
    let eFinal : M ≃ₗ[Aᵐᵒᵖ] Y i :=
      ((eDouble.trans eResizeDual).trans eCoverDual).trans
        (resizedModuleLinearEquiv Aᵐᵒᵖ (DX i)).symm
    exact ⟨i, ⟨eFinal.toModuleIso⟩⟩

end LargeIndecomposable
