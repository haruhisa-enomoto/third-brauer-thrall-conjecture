module

public import LargeIndecomposable.RepresentationType.Obstructions.RepresentationInfiniteFourArrow
public import Mathlib.Tactic

@[expose] public section

/-!
# The radical-square-zero one-loop three-leaf star is representation-infinite

The four arrows are indexed so that arrow `0` is the loop at the central
vertex, while arrows `1`, `2`, and `3` go from the center to the three leaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra RightActions

namespace LargeIndecomposable
namespace LoopThreeStar

universe u

variable (k : Type u) [Field k]

abbrev Diagonal := Fin 4 → k
abbrev ArrowSpace := Fin 4 → k

instance arrowLeftSMul : SMul (Diagonal k) (ArrowSpace k) where
  smul d r i := d i * r i

instance arrowLeftModule : Module (Diagonal k) (ArrowSpace k) where
  smul_zero d := by
    funext i
    change d i * (0 : k) = 0
    simp
  smul_add d r s := by
    funext i
    change d i * (r i + s i) = d i * r i + d i * s i
    exact mul_add _ _ _
  one_smul r := by
    funext i
    change (1 : k) * r i = r i
    exact one_mul _
  mul_smul d e r := by
    funext i
    change (d i * e i) * r i = d i * (e i * r i)
    exact mul_assoc _ _ _
  add_smul d e r := by
    funext i
    change (d i + e i) * r i = d i * r i + e i * r i
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
    change d i * (r i * e.unop 0) = (d i * r i) * e.unop 0
    exact (mul_assoc _ _ _).symm⟩

instance arrowIsScalarTowerLeft :
    IsScalarTower k (Diagonal k) (ArrowSpace k) :=
  ⟨fun c d r ↦ by
    funext i
    change (c * d i) * r i = c * (d i * r i)
    exact mul_assoc _ _ _⟩

instance arrowIsScalarTowerRight :
    IsScalarTower k (Diagonal k)ᵐᵒᵖ (ArrowSpace k) :=
  ⟨fun c d r ↦ by
    funext i
    change r i * (c * d.unop 0) = c * (r i * d.unop 0)
    ring⟩

/-- The radical-square-zero algebra of one central loop and three arrows from
the center to distinct leaves. -/
abbrev StarAlgebra := TrivSqZeroExt (Diagonal k) (ArrowSpace k)

instance starAlgebraAlgebra : _root_.Algebra k (StarAlgebra k) :=
  TrivSqZeroExt.algebra' k (Diagonal k) (ArrowSpace k)

noncomputable instance starAlgebraModuleFinite :
    Module.Finite k (StarAlgebra k) := by
  change Module.Finite k ((Fin 4 → k) × (Fin 4 → k))
  infer_instance

abbrev Carrier := (Fin 2 → k) × (Fin 4 → k)

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
      fun i ↦ a.fst i * v.2 i + a.snd i * forkForm k t i v.1)

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
      change a.fst i * (0 : k) + a.snd i * forkForm k t i 0 = 0
      simp
  smul_add a v w := by
    apply Prod.ext
    · funext j
      change a.fst 0 * (v.1 j + w.1 j) =
        a.fst 0 * v.1 j + a.fst 0 * w.1 j
      ring
    · funext i
      change
        a.fst i * (v.2 i + w.2 i) +
            a.snd i * forkForm k t i (v.1 + w.1) =
          (a.fst i * v.2 i + a.snd i * forkForm k t i v.1) +
            (a.fst i * w.2 i + a.snd i * forkForm k t i w.1)
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
        (a.fst i * b.fst i) * v.2 i +
            (a.fst i * b.snd i + a.snd i * b.fst 0) *
              forkForm k t i v.1 =
          a.fst i *
              (b.fst i * v.2 i + b.snd i * forkForm k t i v.1) +
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
        (a.fst i + b.fst i) * v.2 i +
            (a.snd i + b.snd i) * forkForm k t i v.1 =
          (a.fst i * v.2 i + a.snd i * forkForm k t i v.1) +
            (b.fst i * v.2 i + b.snd i * forkForm k t i v.1)
      ring
  zero_smul v := by
    apply Prod.ext
    · funext j
      change (0 : k) * v.1 j = 0
      simp
    · funext i
      change (0 : k) * v.2 i + 0 * forkForm k t i v.1 = 0
      simp

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

def centerGenerator (t : k) (j : Fin 2) : forkModule k t :=
  (Pi.single j 1, 0)

def targetGenerator (t : k) (i : Fin 4) : forkModule k t :=
  (0, Pi.single i 1)

def centerCoord (t : k) (j : Fin 2) : forkModule k t →ₗ[k] k where
  toFun v := v.1 j
  map_add' _ _ := rfl
  map_smul' c v := forkModule_smul_fst k t c v j

def targetCoord (t : k) (i : Fin 4) : forkModule k t →ₗ[k] k where
  toFun v := v.2 i
  map_add' _ _ := rfl
  map_smul' c v := forkModule_smul_snd k t c v i

def forkGenerator (t : k) : Fin 2 ⊕ Fin 4 → forkModule k t
  | Sum.inl j => centerGenerator k t j
  | Sum.inr i => targetGenerator k t i

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
            (∑ q : Fin 4, v.2 q • targetGenerator k t q) = v.1 j
    rw [map_sum, map_sum]
    simp [centerCoord, centerGenerator, targetGenerator]
    fin_cases j <;> simp
  · funext i
    change targetCoord k t i
        (∑ q : Fin 2, v.1 q • centerGenerator k t q) +
          targetCoord k t i
            (∑ q : Fin 4, v.2 q • targetGenerator k t q) = v.2 i
    rw [map_sum, map_sum]
    simp [targetCoord, centerGenerator, targetGenerator, Pi.single_apply]

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

def arrowElement (i : Fin 4) : StarAlgebra k :=
  (0, Pi.single i 1)

@[simp]
private theorem centerIdempotent_smul (t : k) (v : forkModule k t) :
    centerIdempotent k • v = (v.1, Pi.single 0 (v.2 0)) := by
  classical
  apply Prod.ext
  · funext j
    change ((Pi.single (0 : Fin 4) (1 : k) : Fin 4 → k) 0) * v.1 j = v.1 j
    simp
  · funext i
    change
      ((Pi.single (0 : Fin 4) (1 : k) : Fin 4 → k) i) * v.2 i +
          0 * forkForm k t i v.1 =
        (Pi.single 0 (v.2 0) : Fin 4 → k) i
    by_cases h : i = 0
    · subst i
      simp
    · simp [h]

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
    change
      (0 : k) * v.2 q +
          ((Pi.single i (1 : k) : Fin 4 → k) q) * forkForm k t q v.1 =
        ((Pi.single i (forkForm k t i v.1) : Fin 4 → k) q)
    by_cases h : q = i
    · subst q
      simp
    · simp [h]

def forkSourceIndex (i : Fin 4) : Fin 2 :=
  if i = 1 then 1 else 0

@[simp]
private theorem arrowElement_smul_forkSource (t : k) (i : Fin 4) :
    arrowElement k i • centerGenerator k t (forkSourceIndex i) =
      targetGenerator k t i := by
  fin_cases i <;>
    simp [forkSourceIndex, arrowElement_smul, targetGenerator, forkForm,
      centerGenerator]

/-- On the two-dimensional top, every homomorphism in the family is scalar;
that scalar also annihilates the difference of the two parameters.  Unlike the
loop-free four-star, the full images of the top generators may additionally
have a component in the target of the loop. -/
private theorem forkModule_hom_center_top_scalar
    (s t : k) (f : forkModule k s ⟶ forkModule k t) :
    ∃ a : k,
      (f (centerGenerator k s 0)).1 =
          a • (centerGenerator k t 0).1 ∧
      (f (centerGenerator k s 1)).1 =
          a • (centerGenerator k t 1).1 ∧
      s * a = t * a := by
  classical
  let x₀ : forkModule k s := centerGenerator k s 0
  let x₁ : forkModule k s := centerGenerator k s 1
  let y₀ : forkModule k t := centerGenerator k t 0
  let y₁ : forkModule k t := centerGenerator k t 1
  let a : k := (f x₀).1 0
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
  have htop₀ : (f x₀).1 = a • y₀.1 := by
    funext j
    fin_cases j
    · simp [a, y₀, centerGenerator]
    · simpa [y₀, centerGenerator] using hb
  have htop₁ : (f x₁).1 = a • y₁.1 := by
    funext j
    fin_cases j
    · simpa [y₁, centerGenerator] using hc
    · simpa [y₁, centerGenerator] using had.symm
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
  refine ⟨a, htop₀, htop₁, ?_⟩
  rw [arrowElement_smul, forkModule_smul_snd, arrowElement_smul] at hparam
  change forkForm k t 3 (f x₁).1 =
    s * forkForm k t 3 (f x₀).1 at hparam
  have hleft : forkForm k t 3 (f x₁).1 = t * a := by
    rw [htop₁]
    simp [forkForm, y₁, centerGenerator]
  have hright : s * forkForm k t 3 (f x₀).1 = s * a := by
    rw [htop₀]
    simp [forkForm, y₀, centerGenerator]
  rw [hleft, hright] at hparam
  exact hparam.symm

private theorem forkModule_hom_target_top_zero
    (s t : k) (f : forkModule k s ⟶ forkModule k t) (i : Fin 4) :
    (f (targetGenerator k s i)).1 = 0 := by
  have h :
      f (targetGenerator k s i) =
        arrowElement k i •
          f (centerGenerator k s (forkSourceIndex i)) := by
    calc
      f (targetGenerator k s i) =
          f (arrowElement k i •
            centerGenerator k s (forkSourceIndex i)) := by
              rw [arrowElement_smul_forkSource]
      _ = arrowElement k i •
          f (centerGenerator k s (forkSourceIndex i)) :=
            map_smul f.hom _ _
  rw [h, arrowElement_smul]

/-- Every homomorphism in the family induces a scalar map on the full top
quotient. -/
private theorem forkModule_hom_top_scalar
    (s t : k) (f : forkModule k s ⟶ forkModule k t) :
    ∃ a : k, (∀ v : forkModule k s, (f v).1 = a • v.1) ∧
      s * a = t * a := by
  classical
  obtain ⟨a, h₀, h₁, hparam⟩ :=
    forkModule_hom_center_top_scalar k s t f
  have hgen (q : Fin 2 ⊕ Fin 4) :
      (f (forkGenerator k s q)).1 =
        a • (forkGenerator k s q).1 := by
    cases q with
    | inl j =>
        fin_cases j
        · simpa [forkGenerator, centerGenerator] using h₀
        · simpa [forkGenerator, centerGenerator] using h₁
    | inr i =>
        change (f (targetGenerator k s i)).1 =
          a • (targetGenerator k s i).1
        rw [forkModule_hom_target_top_zero]
        simp [targetGenerator]
  refine ⟨a, ?_, hparam⟩
  intro v
  funext j
  calc
    (f v).1 j =
        centerCoord k t j
          (f (∑ q : Fin 2 ⊕ Fin 4,
            (Sum.elim (fun q ↦ v.1 q) (fun q ↦ v.2 q) q) •
              forkGenerator k s q)) := by
                rw [forkGenerator_sum]
                rfl
    _ = centerCoord k t j
          (∑ q : Fin 2 ⊕ Fin 4,
            (Sum.elim (fun q ↦ v.1 q) (fun q ↦ v.2 q) q) •
              f (forkGenerator k s q)) := by
                congr 1
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro q _
                exact map_smul (f.hom.restrictScalars k) _ _
    _ = ∑ q : Fin 2 ⊕ Fin 4,
          (Sum.elim (fun q ↦ v.1 q) (fun q ↦ v.2 q) q) *
            (f (forkGenerator k s q)).1 j := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro q _
              simp [centerCoord]
    _ = ∑ q : Fin 2 ⊕ Fin 4,
          (Sum.elim (fun q ↦ v.1 q) (fun q ↦ v.2 q) q) *
            (a • (forkGenerator k s q).1) j := by
              apply Finset.sum_congr rfl
              intro q _
              rw [hgen q]
    _ = (a • v.1) j := by
      rw [Fintype.sum_sum_type]
      fin_cases j <;>
        simp [forkGenerator, centerGenerator, targetGenerator, Pi.single_apply]
      <;> ring

private theorem forkModule_iso_parameter_eq
    {s t : k} (e : forkModule k s ≅ forkModule k t) : s = t := by
  obtain ⟨a, ha, hparam⟩ := forkModule_hom_top_scalar k s t e.hom
  obtain ⟨b, hb, -⟩ := forkModule_hom_top_scalar k t s e.inv
  have hane : a ≠ 0 := by
    intro ha0
    let x : forkModule k s := centerGenerator k s 0
    have hcomp : e.inv (e.hom x) = x := by
      change (e.hom ≫ e.inv) x = x
      rw [e.hom_inv_id]
      rfl
    have hcoord := congrArg (fun v : forkModule k s ↦ v.1 0) hcomp
    rw [hb, ha] at hcoord
    simp [ha0, x, centerGenerator] at hcoord
  exact mul_right_cancel₀ hane hparam

private theorem centerIdempotent_fixes_centerGenerator
    (t : k) (j : Fin 2) :
    centerIdempotent k • centerGenerator k t j = centerGenerator k t j := by
  rw [centerIdempotent_smul]
  apply Prod.ext
  · rfl
  · funext i
    simp [centerGenerator]

private theorem forkModule_end_target_eq_scalar
    (t : k) (f : forkModule k t ⟶ forkModule k t)
    (a : k) (htop : ∀ v : forkModule k t, (f v).1 = a • v.1)
    (i : Fin 4) :
    f (targetGenerator k t i) = a • targetGenerator k t i := by
  calc
    f (targetGenerator k t i) =
        f (arrowElement k i •
          centerGenerator k t (forkSourceIndex i)) := by
            rw [arrowElement_smul_forkSource]
    _ = arrowElement k i •
        f (centerGenerator k t (forkSourceIndex i)) :=
          map_smul f.hom _ _
    _ = a • targetGenerator k t i := by
      rw [arrowElement_smul]
      apply Prod.ext
      · funext j
        simp [targetGenerator]
      · funext q
        rw [htop]
        fin_cases i <;> fin_cases q <;>
          simp [forkSourceIndex, forkForm, centerGenerator, targetGenerator]

private theorem forkModule_end_center_eq_top_add_loopTarget
    (t : k) (f : forkModule k t ⟶ forkModule k t)
    (a : k) (htop : ∀ v : forkModule k t, (f v).1 = a • v.1)
    (j : Fin 2) :
    f (centerGenerator k t j) =
      a • centerGenerator k t j +
        (f (centerGenerator k t j)).2 0 • targetGenerator k t 0 := by
  let x := centerGenerator k t j
  have hfixed : centerIdempotent k • f x = f x := by
    calc
      centerIdempotent k • f x =
          f (centerIdempotent k • x) :=
            (map_smul f.hom (centerIdempotent k) x).symm
      _ = f x := by rw [centerIdempotent_fixes_centerGenerator]
  rw [centerIdempotent_smul] at hfixed
  apply Prod.ext
  · funext q
    change (f x).1 q =
      (a • x).1 q +
        ((f x).2 0 • targetGenerator k t 0).1 q
    rw [htop, forkModule_smul_fst, forkModule_smul_fst]
    simp [targetGenerator]
  · funext i
    have hsupp := congrArg (fun v : forkModule k t ↦ v.2 i) hfixed
    change (f x).2 i =
      (a • x).2 i +
        ((f x).2 0 • targetGenerator k t 0).2 i
    rw [forkModule_smul_snd, forkModule_smul_snd]
    fin_cases i
    · simp [x, centerGenerator, targetGenerator]
    · simpa [x, centerGenerator, targetGenerator] using hsupp.symm
    · simpa [x, centerGenerator, targetGenerator] using hsupp.symm
    · simpa [x, centerGenerator, targetGenerator] using hsupp.symm

/-- An endomorphism inducing zero on the top has square zero.  These are
exactly the possible extra shears into the target of the loop. -/
private theorem forkModule_end_sq_zero_of_top_zero
    (t : k) (f : forkModule k t ⟶ forkModule k t)
    (htop : ∀ v : forkModule k t, (f v).1 = 0) :
    f ≫ f = 0 := by
  classical
  have htarget (i : Fin 4) : f (targetGenerator k t i) = 0 := by
    have h := forkModule_end_target_eq_scalar k t f 0 (fun v ↦ by
      simpa using htop v) i
    simpa using h
  have hcenter (j : Fin 2) :
      f (centerGenerator k t j) =
        (f (centerGenerator k t j)).2 0 • targetGenerator k t 0 := by
    have h := forkModule_end_center_eq_top_add_loopTarget k t f 0
      (fun v ↦ by simpa using htop v) j
    simpa using h
  have hgen (q : Fin 2 ⊕ Fin 4) :
      f (f (forkGenerator k t q)) = 0 := by
    cases q with
    | inl j =>
        rw [forkGenerator]
        calc
          f (f (centerGenerator k t j)) =
              f ((f (centerGenerator k t j)).2 0 •
                targetGenerator k t 0) := congrArg f.hom (hcenter j)
          _ = (f (centerGenerator k t j)).2 0 •
              f (targetGenerator k t 0) := by
                exact map_smul (f.hom.restrictScalars k) _ _
          _ = 0 := by rw [htarget]; simp
    | inr i =>
        rw [forkGenerator, htarget]
        exact map_zero f.hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change f (f v) = 0
  calc
    f (f v) =
        f (f (∑ q : Fin 2 ⊕ Fin 4,
          (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
            forkGenerator k t q)) := by rw [forkGenerator_sum]
    _ = f (∑ q : Fin 2 ⊕ Fin 4,
          (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
            f (forkGenerator k t q)) := by
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact map_smul (f.hom.restrictScalars k) _ _
    _ = ∑ q : Fin 2 ⊕ Fin 4,
          (Sum.elim (fun j ↦ v.1 j) (fun i ↦ v.2 i) q) •
            f (f (forkGenerator k t q)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact map_smul (f.hom.restrictScalars k) _ _
    _ = 0 := by simp [hgen]

private theorem forkModule_idempotent_eq_zero_or_id (t : k)
    (f : forkModule k t ⟶ forkModule k t) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  obtain ⟨a, htop, -⟩ := forkModule_hom_top_scalar k t t f
  let x : forkModule k t := centerGenerator k t 0
  have hpoint : f (f x) = f x := by
    have h := congrArg (fun g : forkModule k t ⟶ forkModule k t ↦ g x) hf
    simpa using h
  have hcoord := congrArg (fun v : forkModule k t ↦ v.1 0) hpoint
  rw [htop, htop] at hcoord
  have haa : a * a = a := by
    simpa [x, centerGenerator, smul_smul] using hcoord
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using haa) with ha0 | ha1
  · left
    have hzeroTop : ∀ v : forkModule k t, (f v).1 = 0 := by
      intro v
      rw [htop, ha0]
      simp
    calc
      f = f ≫ f := hf.symm
      _ = 0 := forkModule_end_sq_zero_of_top_zero k t f hzeroTop
  · right
    let g : forkModule k t ⟶ forkModule k t := f - 𝟙 _
    have hgTop : ∀ v : forkModule k t, (g v).1 = 0 := by
      intro v
      change (f v).1 - v.1 = 0
      rw [htop, ha1, one_smul, sub_self]
    have hgsq : g ≫ g = 0 :=
      forkModule_end_sq_zero_of_top_zero k t g hgTop
    have hgcalc : g ≫ g = 𝟙 _ - f := by
      dsimp [g]
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub,
        Category.comp_id, Category.id_comp, Category.id_comp, hf]
      abel
    have hz : 𝟙 _ - f = 0 := hgcalc.symm.trans hgsq
    exact (sub_eq_zero.mp hz).symm

private theorem forkModule_not_isZero (t : k) : ¬IsZero (forkModule k t) := by
  intro hzero
  have hid : (𝟙 (forkModule k t) : forkModule k t ⟶ forkModule k t) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have hpoint := congrArg
    (fun f : forkModule k t ⟶ forkModule k t ↦
      (f (centerGenerator k t 0)).1 0) hid
  simp [centerGenerator] at hpoint

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

/-- Over an infinite field, the radical-square-zero algebra of one central
loop and three outward leaves is representation-infinite. -/
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

/-- A representation-finite algebra cannot have the one-loop three-leaf star
as an algebra quotient. -/
theorem forbids_quotient [Infinite k]
    {A : Type u} [Ring A] [Algebra k A]
    (hA : IsRepresentationFinite k A) (I : TwoSidedIdeal A)
    (e : (A ⧸ I.asIdeal) ≃ₐ[k] StarAlgebra k) : False :=
  not_isRepresentationFinite k ((hA.quotient I).of_algEquiv e)

end LoopThreeStar
end LargeIndecomposable
