module

public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteIdeals
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The outward affine-D4 star is representation-infinite

The radical-square-zero algebra with one central vertex and four outward
arrows has an explicit one-parameter family of pairwise nonisomorphic
six-dimensional indecomposable modules.  Consequently it cannot occur as an
algebra quotient of a representation-finite algebra over an infinite field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra RightActions

namespace LargeIndecomposable
namespace OutwardFourStar

universe u

variable (k : Type u) [Field k]

abbrev Diagonal := Fin 5 → k
abbrev ArrowSpace := Fin 4 → k

instance arrowLeftSMul : SMul (Diagonal k) (ArrowSpace k) where
  smul d r i := d i.succ * r i

instance arrowLeftModule : Module (Diagonal k) (ArrowSpace k) where
  smul_zero d := by
    funext i
    change d i.succ * (0 : k) = 0
    simp
  smul_add d r s := by
    funext i
    change d i.succ * (r i + s i) = d i.succ * r i + d i.succ * s i
    exact mul_add _ _ _
  one_smul r := by
    funext i
    change (1 : k) * r i = r i
    exact one_mul _
  mul_smul d e r := by
    funext i
    change (d i.succ * e i.succ) * r i = d i.succ * (e i.succ * r i)
    exact mul_assoc _ _ _
  add_smul d e r := by
    funext i
    change (d i.succ + e i.succ) * r i = d i.succ * r i + e i.succ * r i
    exact add_mul _ _ _
  zero_smul r := by
    funext i
    change (0 : k) * r i = 0
    simp

instance arrowRightSMul : SMul (Diagonal k)ᵐᵒᵖ (ArrowSpace k) where
  smul d r i := r i * d.unop 0

instance arrowRightModule : Module (Diagonal k)ᵐᵒᵖ (ArrowSpace k) where
  smul_zero d := by
    funext i
    change (0 : k) * d.unop 0 = 0
    simp
  smul_add d r s := by
    funext i
    change (r i + s i) * d.unop 0 = r i * d.unop 0 + s i * d.unop 0
    exact add_mul _ _ _
  one_smul r := by
    funext i
    change r i * (1 : k) = r i
    exact mul_one _
  mul_smul d e r := by
    funext i
    change r i * (e.unop 0 * d.unop 0) = (r i * e.unop 0) * d.unop 0
    exact (mul_assoc _ _ _).symm
  add_smul d e r := by
    funext i
    change r i * (d.unop 0 + e.unop 0) = r i * d.unop 0 + r i * e.unop 0
    exact mul_add _ _ _
  zero_smul r := by
    funext i
    change r i * (0 : k) = 0
    simp

instance arrowActionsCommute :
    SMulCommClass (Diagonal k) (Diagonal k)ᵐᵒᵖ (ArrowSpace k) :=
  ⟨fun d e r ↦ by
    funext i
    change d i.succ * (r i * e.unop 0) = (d i.succ * r i) * e.unop 0
    exact (mul_assoc _ _ _).symm⟩

instance arrowIsScalarTowerLeft :
    IsScalarTower k (Diagonal k) (ArrowSpace k) :=
  ⟨fun c d r ↦ by
    funext i
    change (c * d i.succ) * r i = c * (d i.succ * r i)
    exact mul_assoc _ _ _⟩

instance arrowIsScalarTowerRight :
    IsScalarTower k (Diagonal k)ᵐᵒᵖ (ArrowSpace k) :=
  ⟨fun c d r ↦ by
    funext i
    change r i * (c * d.unop 0) = c * (r i * d.unop 0)
    ring⟩

/-- The radical-square-zero path algebra of the outward-oriented affine
`D₄` star: one central vertex, four leaves, and one arrow to each leaf. -/
abbrev StarAlgebra := TrivSqZeroExt (Diagonal k) (ArrowSpace k)

instance starAlgebraAlgebra : _root_.Algebra k (StarAlgebra k) :=
  TrivSqZeroExt.algebra' k (Diagonal k) (ArrowSpace k)

/-- The outward four-star algebra is finite-dimensional over its ground
field. -/
noncomputable instance starAlgebraModuleFinite :
    Module.Finite k (StarAlgebra k) := by
  change Module.Finite k ((Fin 5 → k) × (Fin 4 → k))
  infer_instance


abbrev Carrier := (Fin 2 → k) × (Fin 4 → k)

/-- The four linear forms `x`, `y`, `x+y`, and `x+t*y` whose projective
cross-ratio is the parameter `t`. -/
def forkForm (t : k) (i : Fin 4) (c : Fin 2 → k) : k :=
  if i = 0 then c 0
  else if i = 1 then c 1
  else if i = 2 then c 0 + c 1
  else c 0 + t * c 1

@[simp]
private theorem forkForm_zero (t : k) (i : Fin 4) :
    forkForm k t i 0 = 0 := by
  fin_cases i <;> simp [forkForm]

@[simp]
private theorem forkForm_add (t : k) (i : Fin 4) (c d : Fin 2 → k) :
    forkForm k t i (c + d) = forkForm k t i c + forkForm k t i d := by
  fin_cases i <;> simp [forkForm] <;> ring

@[simp]
private theorem forkForm_smul (t s : k) (i : Fin 4) (c : Fin 2 → k) :
    forkForm k t i (s • c) = s * forkForm k t i c := by
  fin_cases i <;> simp [forkForm] <;> ring

@[reducible]
def carrierSMul (t : k) :
    SMul (StarAlgebra k) (Carrier k) where
  smul a v :=
    (fun j ↦ a.fst 0 * v.1 j,
      fun i ↦ a.fst i.succ * v.2 i + a.snd i * forkForm k t i v.1)

@[reducible]
def carrierModule (t : k) :
    Module (StarAlgebra k) (Carrier k) where
  smul := (carrierSMul k t).smul
  smul_zero a := by
    apply Prod.ext
    · funext j
      change a.fst 0 * (0 : k) = 0
      simp
    · funext i
      change a.fst i.succ * (0 : k) + a.snd i * forkForm k t i 0 = 0
      simp
  smul_add a v w := by
    apply Prod.ext
    · funext j
      change a.fst 0 * (v.1 j + w.1 j) =
        a.fst 0 * v.1 j + a.fst 0 * w.1 j
      ring
    · funext i
      change
        a.fst i.succ * (v.2 i + w.2 i) +
            a.snd i * forkForm k t i (v.1 + w.1) =
          (a.fst i.succ * v.2 i + a.snd i * forkForm k t i v.1) +
            (a.fst i.succ * w.2 i + a.snd i * forkForm k t i w.1)
      rw [forkForm_add]
      ring
  one_smul v := by
    apply Prod.ext
    · funext j
      change (1 : k) * v.1 j = v.1 j
      simp
    · funext i
      change (1 : k) * v.2 i + 0 * forkForm k t i v.1 = v.2 i
      simp
  mul_smul a b v := by
    apply Prod.ext
    · funext j
      change (a.fst 0 * b.fst 0) * v.1 j =
        a.fst 0 * (b.fst 0 * v.1 j)
      ring
    · funext i
      change
        (a.fst i.succ * b.fst i.succ) * v.2 i +
            (a.fst i.succ * b.snd i + a.snd i * b.fst 0) *
              forkForm k t i v.1 =
          a.fst i.succ *
              (b.fst i.succ * v.2 i +
                b.snd i * forkForm k t i v.1) +
            a.snd i * forkForm k t i (fun j ↦ b.fst 0 * v.1 j)
      rw [show (fun j ↦ b.fst 0 * v.1 j) = b.fst 0 • v.1 by
        funext j
        rfl]
      rw [forkForm_smul]
      ring
  add_smul a b v := by
    apply Prod.ext
    · funext j
      change (a.fst 0 + b.fst 0) * v.1 j =
        a.fst 0 * v.1 j + b.fst 0 * v.1 j
      ring
    · funext i
      change
        (a.fst i.succ + b.fst i.succ) * v.2 i +
            (a.snd i + b.snd i) * forkForm k t i v.1 =
          (a.fst i.succ * v.2 i + a.snd i * forkForm k t i v.1) +
            (b.fst i.succ * v.2 i + b.snd i * forkForm k t i v.1)
      ring
  zero_smul v := by
    apply Prod.ext
    · funext j
      change (0 : k) * v.1 j = 0
      simp
    · funext i
      change (0 : k) * v.2 i + 0 * forkForm k t i v.1 = 0
      simp

/-- The affine-`D₄` module with dimension vector `(2,1,1,1,1)` and
cross-ratio parameter `t`. -/
def forkModule (t : k) : ModuleCat.{u} (StarAlgebra k) := by
  letI : Module (StarAlgebra k) (Carrier k) := carrierModule k t
  exact ModuleCat.of (StarAlgebra k) (Carrier k)

@[simp]
theorem forkModule_smul_fst (t c : k) (v : forkModule k t) (j : Fin 2) :
    (c • v).1 j = c * v.1 j := by
  rfl

@[simp]
theorem forkModule_smul_snd (t c : k) (v : forkModule k t) (i : Fin 4) :
    (c • v).2 i = c * v.2 i := by
  change c * v.2 i + 0 * forkForm k t i v.1 = c * v.2 i
  simp

@[simp]
private theorem forkModule_zero_fst (t : k) (j : Fin 2) :
    (0 : forkModule k t).1 j = 0 := by
  rfl

@[simp]
private theorem forkModule_zero_snd (t : k) (i : Fin 4) :
    (0 : forkModule k t).2 i = 0 := by
  rfl

def centerCoord (t : k) (j : Fin 2) : forkModule k t →ₗ[k] k where
  toFun v := v.1 j
  map_add' _ _ := rfl
  map_smul' c v := forkModule_smul_fst k t c v j

def leafCoord (t : k) (i : Fin 4) : forkModule k t →ₗ[k] k where
  toFun v := v.2 i
  map_add' _ _ := rfl
  map_smul' c v := forkModule_smul_snd k t c v i

def centerGenerator (t : k) (j : Fin 2) : forkModule k t :=
  (Pi.single j 1, 0)

def leafGenerator (t : k) (i : Fin 4) : forkModule k t :=
  (0, Pi.single i 1)

def forkGenerator (t : k) : Fin 2 ⊕ Fin 4 → forkModule k t
  | Sum.inl j => centerGenerator k t j
  | Sum.inr i => leafGenerator k t i

private theorem forkGenerator_sum (t : k) (v : forkModule k t) :
    ∑ q : Fin 2 ⊕ Fin 4,
        (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          forkGenerator k t q = v := by
  classical
  rw [Fintype.sum_sum_type]
  apply Prod.ext
  · funext j
    change centerCoord k t j
        (∑ q : Fin 2, v.1 q • centerGenerator k t q) +
          centerCoord k t j
            (∑ q : Fin 4, v.2 q • leafGenerator k t q) = v.1 j
    rw [map_sum, map_sum]
    simp [centerCoord, centerGenerator, leafGenerator]
    fin_cases j <;> simp
  · funext i
    change leafCoord k t i
        (∑ q : Fin 2, v.1 q • centerGenerator k t q) +
          leafCoord k t i
            (∑ q : Fin 4, v.2 q • leafGenerator k t q) = v.2 i
    rw [map_sum, map_sum]
    simp [leafCoord, centerGenerator, leafGenerator, Pi.single_apply]

private theorem forkModule_finite (t : k) : Module.Finite k (forkModule k t) := by
  apply Module.Finite.of_fg_top
  rw [← show Submodule.span k (Set.range (forkGenerator k t)) = ⊤ by
    apply top_unique
    intro v _
    exact (Submodule.mem_span_range_iff_exists_fun k).2
      ⟨Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i), forkGenerator_sum k t v⟩]
  exact Submodule.fg_span (Set.finite_range _)

def centerIdempotent : StarAlgebra k :=
  (Pi.single 0 1, 0)

def leafIdempotent (i : Fin 4) : StarAlgebra k :=
  (Pi.single i.succ 1, 0)

def arrowElement (i : Fin 4) : StarAlgebra k :=
  (0, Pi.single i 1)

@[simp]
private theorem centerIdempotent_smul (t : k) (v : forkModule k t) :
    centerIdempotent k • v = (v.1, 0) := by
  classical
  apply Prod.ext
  · funext j
    change ((Pi.single (0 : Fin 5) (1 : k) : Fin 5 → k) 0) * v.1 j = v.1 j
    simp
  · funext i
    change ((Pi.single (0 : Fin 5) (1 : k) : Fin 5 → k) i.succ) * v.2 i +
      0 * forkForm k t i v.1 = 0
    simp

@[simp]
private theorem leafIdempotent_smul (t : k) (i : Fin 4) (v : forkModule k t) :
    leafIdempotent k i • v = (0, Pi.single i (v.2 i)) := by
  classical
  apply Prod.ext
  · funext j
    change ((Pi.single i.succ (1 : k) : Fin 5 → k) 0) * v.1 j = 0
    simp
  · funext q
    change ((Pi.single i.succ (1 : k) : Fin 5 → k) q.succ) * v.2 q +
      0 * forkForm k t q v.1 =
        ((Pi.single i (v.2 i) : Fin 4 → k) q)
    by_cases h : q = i
    · subst q
      simp
    · have hs : q.succ ≠ i.succ := fun hs ↦ h (Fin.succ_injective _ hs)
      simp [h, hs]

@[simp]
private theorem arrowElement_smul (t : k) (i : Fin 4) (v : forkModule k t) :
    arrowElement k i • v =
      (0, Pi.single i (forkForm k t i v.1)) := by
  classical
  apply Prod.ext
  · funext j
    change (0 : k) * v.1 j = 0
    simp
  · funext q
    change (0 : k) * v.2 q +
      ((Pi.single i (1 : k) : Fin 4 → k) q) * forkForm k t q v.1 =
        ((Pi.single i (forkForm k t i v.1) : Fin 4 → k) q)
    by_cases h : q = i
    · subst q
      simp
    · simp [h]

@[simp]
private theorem forkForm_centerGenerator_zero (t : k) :
    forkForm k t 0 (centerGenerator k t 0).1 = 1 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_centerGenerator_one (t : k) :
    forkForm k t 0 (centerGenerator k t 1).1 = 0 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_one_centerGenerator_zero (t : k) :
    forkForm k t 1 (centerGenerator k t 0).1 = 0 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_one_centerGenerator_one (t : k) :
    forkForm k t 1 (centerGenerator k t 1).1 = 1 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_two_centerGenerator_zero (t : k) :
    forkForm k t 2 (centerGenerator k t 0).1 = 1 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_two_centerGenerator_one (t : k) :
    forkForm k t 2 (centerGenerator k t 1).1 = 1 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_three_centerGenerator_zero (t : k) :
    forkForm k t 3 (centerGenerator k t 0).1 = 1 := by
  simp [forkForm, centerGenerator]

@[simp]
private theorem forkForm_three_centerGenerator_one (t : k) :
    forkForm k t 3 (centerGenerator k t 1).1 = t := by
  simp [forkForm, centerGenerator]

/-- Every homomorphism in the affine-`D₄` family is scalar on the
two-dimensional central vertex; that scalar also annihilates the difference
of the two cross-ratio parameters. -/
private theorem forkModule_hom_center_scalar
    (s t : k) (f : forkModule k s ⟶ forkModule k t) :
    ∃ a : k,
      f (centerGenerator k s 0) = a • centerGenerator k t 0 ∧
      f (centerGenerator k s 1) = a • centerGenerator k t 1 ∧
      s * a = t * a := by
  classical
  let x₀ : forkModule k s := centerGenerator k s 0
  let x₁ : forkModule k s := centerGenerator k s 1
  let y₀ : forkModule k t := centerGenerator k t 0
  let y₁ : forkModule k t := centerGenerator k t 1
  let a : k := (f x₀).1 0
  have hxcenter₀ : centerIdempotent k • x₀ = x₀ := by
    rw [centerIdempotent_smul]
    rfl
  have hxcenter₁ : centerIdempotent k • x₁ = x₁ := by
    rw [centerIdempotent_smul]
    rfl
  have hcenter₀ : centerIdempotent k • f x₀ = f x₀ := by
    calc
      centerIdempotent k • f x₀ = f (centerIdempotent k • x₀) :=
        (map_smul f.hom (centerIdempotent k) x₀).symm
      _ = f x₀ := congrArg f.hom hxcenter₀
  have hcenter₁ : centerIdempotent k • f x₁ = f x₁ := by
    calc
      centerIdempotent k • f x₁ = f (centerIdempotent k • x₁) :=
        (map_smul f.hom (centerIdempotent k) x₁).symm
      _ = f x₁ := congrArg f.hom hxcenter₁
  have hleaf₀ (i : Fin 4) : (f x₀).2 i = 0 := by
    have h := congrArg (fun v : forkModule k t ↦ v.2 i) hcenter₀
    simpa using h.symm
  have hleaf₁ (i : Fin 4) : (f x₁).2 i = 0 := by
    have h := congrArg (fun v : forkModule k t ↦ v.2 i) hcenter₁
    simpa using h.symm
  have hb : (f x₀).1 1 = 0 := by
    have hsource : arrowElement k 1 • x₀ = 0 := by
      rw [arrowElement_smul]
      apply Prod.ext
      · funext j
        simp
      · funext i
        simp [x₀, forkForm, centerGenerator]
    have htarget : arrowElement k 1 • f x₀ = 0 := by
      rw [← map_smul f.hom, hsource]
      exact map_zero f.hom
    have h := congrArg (fun v : forkModule k t ↦ v.2 1) htarget
    simpa [arrowElement_smul, forkForm] using h
  have hc : (f x₁).1 0 = 0 := by
    have hsource : arrowElement k 0 • x₁ = 0 := by
      rw [arrowElement_smul]
      apply Prod.ext
      · funext j
        simp
      · funext i
        simp [x₁, forkForm, centerGenerator]
    have htarget : arrowElement k 0 • f x₁ = 0 := by
      rw [← map_smul f.hom, hsource]
      exact map_zero f.hom
    have h := congrArg (fun v : forkModule k t ↦ v.2 0) htarget
    simpa [arrowElement_smul, forkForm] using h
  have had : a = (f x₁).1 1 := by
    have hsource : arrowElement k 2 • x₀ = arrowElement k 2 • x₁ := by
      simp [x₀, x₁, arrowElement_smul, forkForm, centerGenerator]
    have htarget : arrowElement k 2 • f x₀ = arrowElement k 2 • f x₁ := by
      rw [← map_smul f.hom, ← map_smul f.hom, hsource]
    have h := congrArg (fun v : forkModule k t ↦ v.2 2) htarget
    dsimp [a]
    simpa [arrowElement_smul, forkForm, hb, hc] using h
  have hfx₀ : f x₀ = a • y₀ := by
    apply Prod.ext
    · funext j
      fin_cases j
      · simp [a, y₀, centerGenerator]
      · simpa [y₀, centerGenerator] using hb
    · funext i
      simpa [y₀, centerGenerator] using hleaf₀ i
  have hfx₁ : f x₁ = a • y₁ := by
    apply Prod.ext
    · funext j
      fin_cases j
      · simpa [y₁, centerGenerator] using hc
      · simpa [y₁, centerGenerator] using had.symm
    · funext i
      simpa [y₁, centerGenerator] using hleaf₁ i
  have hsource₃ :
      arrowElement k 3 • x₁ = s • (arrowElement k 3 • x₀) := by
    apply Prod.ext
    · funext j
      simp [x₀, x₁, arrowElement_smul, forkForm, centerGenerator]
    · funext i
      fin_cases i <;>
        simp [x₀, x₁, arrowElement_smul, forkForm, centerGenerator]
  have htarget₃ :
      arrowElement k 3 • f x₁ =
        s • (arrowElement k 3 • f x₀) := by
    calc
      arrowElement k 3 • f x₁ = f (arrowElement k 3 • x₁) :=
        (map_smul f.hom (arrowElement k 3) x₁).symm
      _ = f (s • (arrowElement k 3 • x₀)) := congrArg f.hom hsource₃
      _ = s • f (arrowElement k 3 • x₀) := by
        exact map_smul (f.hom.restrictScalars k) s _
      _ = s • (arrowElement k 3 • f x₀) := by
        rw [map_smul f.hom]
  have hparam := congrArg (fun v : forkModule k t ↦ v.2 3) htarget₃
  refine ⟨a, hfx₀, hfx₁, ?_⟩
  rw [hfx₀, hfx₁] at hparam
  have hleft :
      (arrowElement k 3 • (a • y₁)).2 3 = t * a := by
    rw [arrowElement_smul]
    simp [forkForm, y₁, centerGenerator]
  have hright :
      (s • (arrowElement k 3 • (a • y₀))).2 3 = s * a := by
    rw [forkModule_smul_snd, arrowElement_smul]
    simp [forkForm, y₀, centerGenerator]
  rw [hleft, hright] at hparam
  exact hparam.symm

/-- Distinct parameters in the affine-`D₄` family give nonisomorphic
modules. -/
private theorem forkModule_iso_parameter_eq
    {s t : k} (e : forkModule k s ≅ forkModule k t) : s = t := by
  obtain ⟨a, h₀, -, hparam⟩ :=
    forkModule_hom_center_scalar k s t e.hom
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_smul] at h₀
    have hgen : centerGenerator k s 0 = 0 :=
      e.toLinearEquiv.injective (by simpa using h₀)
    have hcoord := congrArg (fun v : forkModule k s ↦ v.1 0) hgen
    simp [centerGenerator] at hcoord
  exact mul_right_cancel₀ ha hparam

def forkSourceIndex (i : Fin 4) : Fin 2 :=
  if i = 1 then 1 else 0

@[simp]
private theorem arrowElement_smul_forkSource (t : k) (i : Fin 4) :
    arrowElement k i • centerGenerator k t (forkSourceIndex i) =
      leafGenerator k t i := by
  fin_cases i <;>
    simp [forkSourceIndex, arrowElement_smul, leafGenerator, forkForm,
      centerGenerator]

/-- Every endomorphism of a member of the affine-`D₄` family is scalar. -/
private theorem forkModule_end_scalar (t : k)
    (f : forkModule k t ⟶ forkModule k t) :
    ∃ a : k, ∀ v : forkModule k t, f v = a • v := by
  classical
  obtain ⟨a, h₀, h₁, -⟩ := forkModule_hom_center_scalar k t t f
  have hcenter (j : Fin 2) :
      f (centerGenerator k t j) = a • centerGenerator k t j := by
    fin_cases j
    · exact h₀
    · exact h₁
  have hleaf (i : Fin 4) :
      f (leafGenerator k t i) = a • leafGenerator k t i := by
    calc
      f (leafGenerator k t i) =
          f (arrowElement k i • centerGenerator k t (forkSourceIndex i)) := by
            rw [arrowElement_smul_forkSource]
      _ = arrowElement k i •
          f (centerGenerator k t (forkSourceIndex i)) :=
            map_smul f.hom _ _
      _ = arrowElement k i •
          (a • centerGenerator k t (forkSourceIndex i)) := by rw [hcenter]
      _ = a • leafGenerator k t i := by
        rw [smul_comm (arrowElement k i) a,
          arrowElement_smul_forkSource]
  have hgenerator (q : Fin 2 ⊕ Fin 4) :
      f (forkGenerator k t q) = a • forkGenerator k t q := by
    cases q with
    | inl j => exact hcenter j
    | inr i => exact hleaf i
  refine ⟨a, fun v ↦ ?_⟩
  calc
    f v = f (∑ q : Fin 2 ⊕ Fin 4,
        (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          forkGenerator k t q) := by rw [forkGenerator_sum]
    _ = ∑ q : Fin 2 ⊕ Fin 4,
        f ((Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          forkGenerator k t q) := map_sum f.hom _ _
    _ = ∑ q : Fin 2 ⊕ Fin 4,
        (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          f (forkGenerator k t q) := by
            apply Finset.sum_congr rfl
            intro q _
            exact map_smul (f.hom.restrictScalars k) _ _
    _ = ∑ q : Fin 2 ⊕ Fin 4,
        (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          (a • forkGenerator k t q) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [hgenerator]
    _ = a • ∑ q : Fin 2 ⊕ Fin 4,
        (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
          forkGenerator k t q := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro q _
            simp only [smul_smul]
            rw [mul_comm]
    _ = a • v := by rw [forkGenerator_sum]

/-- Idempotent endomorphisms of a member of the affine-`D₄` family are
trivial. -/
private theorem forkModule_idempotent_eq_zero_or_id (t : k)
    (f : forkModule k t ⟶ forkModule k t) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  obtain ⟨a, ha⟩ := forkModule_end_scalar k t f
  let x := centerGenerator k t 0
  have hpoint : f (f x) = f x := by
    have h := congrArg (fun g : forkModule k t ⟶ forkModule k t ↦ g x) hf
    simpa using h
  rw [ha (f x), ha x] at hpoint
  have hcoord := congrArg (fun v : forkModule k t ↦ v.1 0) hpoint
  have haa : a * a = a := by
    simpa [x, centerGenerator, smul_smul] using hcoord
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using haa) with ha0 | ha1
  · left
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simpa [ha0] using ha v
  · right
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simpa [ha1] using ha v

private theorem forkModule_not_isZero (t : k) : ¬IsZero (forkModule k t) := by
  intro hzero
  have hid : (𝟙 (forkModule k t) : forkModule k t ⟶ forkModule k t) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have hpoint := congrArg
    (fun f : forkModule k t ⟶ forkModule k t ↦
      (f (centerGenerator k t 0)).1 0) hid
  simp [centerGenerator] at hpoint

/-- Each module in the affine-`D₄` family is indecomposable. -/
private theorem forkModule_indecomposable (t : k) :
    Indecomposable (forkModule k t) := by
  refine ⟨forkModule_not_isZero k t, ?_⟩
  intro Y Z e
  let p : forkModule k t ⟶ forkModule k t :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by
    dsimp [p]
    simp
  rcases forkModule_idempotent_eq_zero_or_id k t p hp with hp0 | hp1
  · left
    apply (IsZero.iff_id_eq_zero Y).mpr
    calc
      𝟙 Y =
          (biprod.inl ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.fst) := by
            dsimp [p]
            simp
      _ = 0 := by rw [hp0]; simp
  · right
    apply (IsZero.iff_id_eq_zero Z).mpr
    calc
      𝟙 Z =
          (biprod.inr ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.snd) := by
            rw [hp1]
            simp
      _ = 0 := by
            dsimp [p]
            simp

/-- Over an infinite field, the radical-square-zero outward four-star is
representation-infinite. -/
theorem not_isRepresentationFinite [Infinite k] :
    ¬IsRepresentationFinite k (StarAlgebra k) := by
  intro hfinite
  let parameter : ℕ ↪ k := Infinite.natEmbedding k
  apply hfinite.not_infiniteFiniteIndecomposableFamily.false
  exact
    { module := fun n ↦ forkModule k (parameter n)
      finite := fun n ↦ forkModule_finite k (parameter n)
      indecomposable := fun n ↦ forkModule_indecomposable k (parameter n)
      eq_of_iso := fun h ↦ by
        obtain ⟨e⟩ := h
        exact parameter.injective (forkModule_iso_parameter_eq k e) }

/-- A representation-finite algebra cannot have the outward affine-`D₄`
star as an algebra quotient. -/
theorem forbids_quotient [Infinite k]
    {A : Type u} [Ring A] [Algebra k A]
    (hA : IsRepresentationFinite k A) (I : TwoSidedIdeal A)
    (e : (A ⧸ I.asIdeal) ≃ₐ[k] StarAlgebra k) : False :=
  not_isRepresentationFinite k ((hA.quotient I).of_algEquiv e)

end OutwardFourStar

end LargeIndecomposable
