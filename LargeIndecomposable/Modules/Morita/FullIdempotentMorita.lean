module

public import LargeIndecomposable.Modules.SplitBasic.BasicReduction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Morita.Basic
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFinite
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

/-!
# Morita equivalence for a full idempotent

Mathlib's current Morita API does not yet contain the full-idempotent
criterion.  This file supplies the needed construction for a finite
dimensional algebra.  Since Mathlib's `TensorProduct` is over a commutative
base, the relative tensor product is constructed as the quotient of the
ordinary `k`-tensor product by the balancing relations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace LargeIndecomposable

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u v

section FullnessCertificate

variable {R : Type*} [Ring R]

/-- A finite expression witnessing that `e` generates the unit two-sided
ideal. -/
structure FullnessCertificate (e : R) where
  terms : List (R × R)
  sum_mul : (terms.map fun p ↦ p.1 * (e * p.2)).sum = 1

private theorem sum_neg_left (e : R) (xs : List (R × R)) :
    (xs.map fun p ↦ (-p.1) * (e * p.2)).sum =
      -(xs.map fun p ↦ p.1 * (e * p.2)).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, neg_mul]
      have ih' := ih
      simp only [neg_mul] at ih'
      rw [ih', neg_add_rev, add_comm]

private theorem sum_mul_left (a e : R) (xs : List (R × R)) :
    (xs.map fun p ↦ (a * p.1) * (e * p.2)).sum =
      a * (xs.map fun p ↦ p.1 * (e * p.2)).sum := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, mul_add, mul_assoc]

private theorem sum_mul_right (e a : R) (xs : List (R × R)) :
    (xs.map fun p ↦ p.1 * (e * (p.2 * a))).sum =
      (xs.map fun p ↦ p.1 * (e * p.2)).sum * a := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, add_mul]
      simp only [mul_assoc]

/-- A full element admits a finite two-sided expression for `1`. -/
theorem IsFull.exists_fullnessCertificate {e : R} (he : IsFull e) :
    Nonempty (FullnessCertificate e) := by
  have hone : (1 : R) ∈ TwoSidedIdeal.span ({e} : Set R) := by
    rw [he]
    exact Set.mem_univ 1
  have hrepr {x : R} (hx : x ∈ TwoSidedIdeal.span ({e} : Set R)) :
      ∃ terms : List (R × R),
        (terms.map fun p ↦ p.1 * (e * p.2)).sum = x := by
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨[(1, 1)], by simp⟩
    | zero => exact ⟨[], by simp⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨xs, hxs⟩ := ihx
        obtain ⟨ys, hys⟩ := ihy
        exact ⟨xs ++ ys, by simp [hxs, hys]⟩
    | neg x hx ih =>
        obtain ⟨xs, hxs⟩ := ih
        refine ⟨xs.map fun p ↦ (-p.1, p.2), ?_⟩
        rw [List.map_map]
        change (xs.map fun p ↦ (-p.1) * (e * p.2)).sum = -x
        exact (sum_neg_left e xs).trans (congrArg Neg.neg hxs)
    | left_absorb a x hx ih =>
        obtain ⟨xs, hxs⟩ := ih
        refine ⟨xs.map fun p ↦ (a * p.1, p.2), ?_⟩
        rw [List.map_map]
        change (xs.map fun p ↦ (a * p.1) * (e * p.2)).sum = a * x
        exact (sum_mul_left a e xs).trans (congrArg (fun z : R ↦ a * z) hxs)
    | right_absorb a x hx ih =>
        obtain ⟨xs, hxs⟩ := ih
        refine ⟨xs.map fun p ↦ (p.1, p.2 * a), ?_⟩
        rw [List.map_map]
        change (xs.map fun p ↦ p.1 * (e * (p.2 * a))).sum = x * a
        exact (sum_mul_right e a xs).trans (congrArg (fun z : R ↦ z * a) hxs)
  obtain ⟨terms, hterms⟩ := hrepr hone
  exact ⟨⟨terms, hterms⟩⟩

end FullnessCertificate

section Modules

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he

/-- The left ideal `A e`, as a `k`-submodule of `A`. -/
def IsIdempotentElem.leftIdeal : Submodule k A :=
  { carrier := {x | x * e = x}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change x * e = x at hx
      change y * e = y at hy
      change (x + y) * e = x + y
      rw [add_mul, hx, hy]
    smul_mem' := by
      intro c x hx
      change x * e = x at hx
      change (c • x) * e = c • x
      simp only [Algebra.smul_def]
      rw [mul_assoc, hx] }

namespace IsIdempotentElem

instance leftIdealSMul : SMul A (leftIdeal (k := k) (e := e)) where
  smul a x := ⟨a * x.1, by
    change (a * x.1) * e = a * x.1
    rw [mul_assoc, x.2]⟩

@[simp]
theorem leftIdeal_smul_val (a : A) (x : leftIdeal (k := k) (e := e)) :
    ((a • x : leftIdeal (k := k) (e := e)) : A) = a * x.1 :=
  rfl

instance leftIdealModule : Module A (leftIdeal (k := k) (e := e)) where
  smul_zero a := Subtype.ext (mul_zero a)
  smul_add a x y := Subtype.ext (mul_add a x.1 y.1)
  one_smul x := Subtype.ext (one_mul x.1)
  mul_smul a b x := Subtype.ext (mul_assoc a b x.1)
  add_smul a b x := Subtype.ext (add_mul a b x.1)
  zero_smul x := Subtype.ext (zero_mul x.1)

instance leftIdealIsScalarTower : IsScalarTower k A (leftIdeal (k := k) (e := e)) :=
  ⟨fun c a x ↦ Subtype.ext <| by
    change (c • a : A) * x.1 = c • (a * x.1)
    simp only [Algebra.smul_def, mul_assoc]⟩

instance leftIdealSMulCommClass : SMulCommClass k A (leftIdeal (k := k) (e := e)) :=
  ⟨fun c a x ↦ Subtype.ext <| by
    change c • (a * x.1) = a * (c • x.1)
    simp only [Algebra.smul_def]
    rw [← mul_assoc, Algebra.commutes c a, mul_assoc]⟩

/-- Right multiplication makes `A e` a right `eAe`-module. -/
instance leftIdealCornerOppSMul : SMul Bᵐᵒᵖ (leftIdeal (k := k) (e := e)) where
  smul b x := ⟨x.1 * b.unop.1, by
    change (x.1 * b.unop.1) * e = x.1 * b.unop.1
    obtain ⟨_, hb_right⟩ := (Subsemigroup.mem_corner_iff he).mp b.unop.2
    rw [mul_assoc, hb_right]⟩

@[simp]
theorem leftIdeal_cornerOpp_smul_val (b : Bᵐᵒᵖ) (x : leftIdeal (k := k) (e := e)) :
    ((b • x : leftIdeal (k := k) (e := e)) : A) = x.1 * b.unop.1 :=
  rfl

instance leftIdealCornerOppModule : Module Bᵐᵒᵖ (leftIdeal (k := k) (e := e)) where
  smul_zero b := Subtype.ext <| by change 0 * b.unop.1 = 0; rw [zero_mul]
  smul_add b x y := Subtype.ext <| by
    change (x.1 + y.1) * b.unop.1 = x.1 * b.unop.1 + y.1 * b.unop.1
    rw [add_mul]
  one_smul x := by
    apply Subtype.ext
    change x.1 * e = x.1
    exact x.2
  mul_smul b c x := by
    apply Subtype.ext
    change x.1 * (c.unop.1 * b.unop.1) =
      (x.1 * c.unop.1) * b.unop.1
    rw [mul_assoc]
  add_smul b c x := Subtype.ext <| by
    change x.1 * (b.unop.1 + c.unop.1) =
      x.1 * b.unop.1 + x.1 * c.unop.1
    rw [mul_add]
  zero_smul x := Subtype.ext <| by change x.1 * 0 = 0; rw [mul_zero]

instance leftIdeal_actions_commute : SMulCommClass A Bᵐᵒᵖ (leftIdeal (k := k) (e := e)) :=
  ⟨fun a b x ↦ Subtype.ext <| by simp [mul_assoc]⟩

instance leftIdeal_cornerOpp_k_commute : SMulCommClass k Bᵐᵒᵖ (leftIdeal (k := k) (e := e)) :=
  ⟨fun c b x ↦ by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc]⟩

/-- The image `eM` of the idempotent on a left `A`-module. -/
def cornerPart (M : ModuleCat.{v} A) : Submodule k M :=
  { carrier := {m | e • m = m}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change e • x = x at hx
      change e • y = y at hy
      change e • (x + y) = x + y
      rw [smul_add, hx, hy]
    smul_mem' := by
      intro c m hm
      change e • (c • m) = c • m
      rw [smul_comm e c m, hm] }

instance cornerPartSMul (M : ModuleCat.{v} A) : SMul B (cornerPart (k := k) (e := e) M) where
  smul b m := ⟨b.1 • m.1, by
    obtain ⟨hb_left, _⟩ := (Subsemigroup.mem_corner_iff he).mp b.2
    change e • b.1 • m.1 = b.1 • m.1
    rw [← mul_smul, hb_left]⟩

@[simp]
theorem cornerPart_smul_val (M : ModuleCat.{v} A) (b : B)
    (m : cornerPart (k := k) (e := e) M) :
    ((b • m : cornerPart (k := k) (e := e) M) : M) = b.1 • m.1 :=
  rfl

instance cornerPartModule (M : ModuleCat.{v} A) : Module B (cornerPart (k := k) (e := e) M) where
  smul_zero b := Subtype.ext (smul_zero b.1)
  smul_add b x y := Subtype.ext (smul_add b.1 x.1 y.1)
  one_smul x := by
    apply Subtype.ext
    change e • x.1 = x.1
    exact x.2
  mul_smul b c x := Subtype.ext <| by
    change (b.1 * c.1) • x.1 = b.1 • c.1 • x.1
    rw [mul_smul]
  add_smul b c x := Subtype.ext (add_smul b.1 c.1 x.1)
  zero_smul x := Subtype.ext (zero_smul A x.1)

instance cornerPartIsScalarTower (M : ModuleCat.{v} A) :
    IsScalarTower k B (cornerPart (k := k) (e := e) M) :=
  ⟨fun c b m ↦ Subtype.ext <| by
    change (algebraMap k A c * e * b.1) • m.1 =
      algebraMap k A c • b.1 • m.1
    obtain ⟨hb_left, _⟩ := (Subsemigroup.mem_corner_iff he).mp b.2
    simp only [← mul_smul]
    exact congrArg (fun a : A ↦ a • m.1) (by rw [mul_assoc, hb_left])⟩

instance cornerPartSMulCommClass (M : ModuleCat.{v} A) :
    SMulCommClass k B (cornerPart (k := k) (e := e) M) :=
  ⟨fun c b m ↦ Subtype.ext <| by
    change algebraMap k A c • b.1 • m.1 =
      b.1 • algebraMap k A c • m.1
    simp only [← mul_smul]
    exact congrArg (fun a : A ↦ a • m.1) (Algebra.commutes c b.1)⟩

/-- The fixed submodule bundled with its corner-algebra module structure. -/
def cornerPartObj (M : ModuleCat.{v} A) : ModuleCat.{v} B := by
  letI : Module B (cornerPart (k := k) (e := e) M) := cornerPartModule he M
  exact ModuleCat.of B (cornerPart (k := k) (e := e) M)

/-- The inherited `k`-module on the fixed submodule agrees with the
restriction of its corner-module structure. -/
def cornerPartLinearEquiv (M : ModuleCat.{v} A) :
    cornerPart (k := k) (e := e) M ≃ₗ[k] cornerPartObj (k := k) he M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c m := by
    apply Subtype.ext
    change algebraMap k A c • m.1 = (algebraMap k A c * e) • m.1
    exact (congrArg (fun y : M ↦ algebraMap k A c • y) m.2.symm).trans
      (mul_smul (algebraMap k A c) e m.1).symm

end IsIdempotentElem

end Modules

section BalancedTensor

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

/-- The elementary balancing relations in `Ae ⊗[k] N`. -/
def IsIdempotentElem.balanceSet (N : ModuleCat.{v} B) :
    Set (TensorProduct k P N) :=
  {z | ∃ (x : P) (b : B) (n : N),
    z = (MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n)}

/-- The `A`-submodule generated by the balancing relations. -/
def IsIdempotentElem.balanceSubmodule (N : ModuleCat.{v} B) :
    Submodule k (TensorProduct k P N) :=
  Submodule.span k (balanceSet (k := k) (he := he) N)

/-- The relative tensor product `Ae ⊗_{eAe} N`, constructed as a quotient
of the ordinary tensor product over `k`. -/
abbrev IsIdempotentElem.relativeTensor (N : ModuleCat.{v} B) :=
  (TensorProduct k P N) ⧸
    (balanceSubmodule (k := k) (he := he) N).toAddSubgroup

instance IsIdempotentElem.relativeTensorSMulK (N : ModuleCat.{v} B) :
    SMul k (relativeTensor (k := k) (he := he) N) where
  smul c := by
    letI : Module k (TensorProduct k P N) := TensorProduct.instModule
    exact Quotient.map' (fun z : TensorProduct k P N ↦ c • z) (by
      intro x y hxy
      rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
      change -x + y ∈ balanceSubmodule (k := k) (he := he) N at hxy
      change -(c • x) + c • y ∈ balanceSubmodule (k := k) (he := he) N
      have h := (balanceSubmodule (k := k) (he := he) N).smul_mem c hxy
      rw [smul_add] at h
      rw [← smul_neg c x]
      exact h)

@[simp]
theorem IsIdempotentElem.relativeTensor_smul_mk (N : ModuleCat.{v} B)
    (c : k) (z : TensorProduct k P N) :
    @SMul.smul k (relativeTensor (k := k) (he := he) N)
        (relativeTensorSMulK he N) c (Quotient.mk'' z) =
      (Quotient.mk'' (c • z) : relativeTensor (k := k) (he := he) N) :=
  rfl

instance IsIdempotentElem.relativeTensorModuleK (N : ModuleCat.{v} B) :
    Module k (relativeTensor (k := k) (he := he) N) where
  smul_zero c := by
    change Quotient.map' (fun z : TensorProduct k P N ↦ c • z) _
        (Quotient.mk'' 0) = Quotient.mk'' 0
    exact congrArg Quotient.mk'' (smul_zero c)
  smul_add c x y := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y => exact congrArg Quotient.mk'' (smul_add c x y)
  one_smul x := by
    induction x using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (one_smul k x)
  mul_smul c d x := by
    induction x using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (mul_smul c d x)
  add_smul c d x := by
    induction x using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (add_smul c d x)
  zero_smul x := by
    induction x using Quotient.inductionOn' with
    | _ x => exact congrArg Quotient.mk'' (zero_smul k x)

/-- The quotient map from the ordinary tensor product to the balanced
relative tensor product, regarded as a `k`-linear map. -/
def IsIdempotentElem.relativeQuotientMapK (N : ModuleCat.{v} B) :
    TensorProduct k P N →ₗ[k] relativeTensor (k := k) (he := he) N where
  toFun := Quotient.mk''
  map_add' _ _ := rfl
  map_smul' c x := congrArg Quotient.mk'' (rfl : c • x = c • x)

theorem IsIdempotentElem.relativeQuotientMapK_surjective
    (N : ModuleCat.{v} B) :
    Function.Surjective (relativeQuotientMapK (k := k) he N) := by
  intro z
  induction z using Quotient.inductionOn' with
  | _ z => exact ⟨z, rfl⟩

/-- A relative tensor product of finite-dimensional modules is
finite-dimensional over the coefficient field. -/
theorem IsIdempotentElem.relativeTensor_moduleFinite
    (N : ModuleCat.{v} B) [Module.Finite k P] [Module.Finite k N] :
    Module.Finite k (relativeTensor (k := k) (he := he) N) := by
  letI : Module.Finite k (TensorProduct k P N) := by infer_instance
  exact Module.Finite.of_surjective (relativeQuotientMapK (k := k) he N)
    (relativeQuotientMapK_surjective (k := k) he N)

/-- Left multiplication on the ordinary tensor product, as a `k`-linear
map. -/
def IsIdempotentElem.leftIdealLeftAction (a : A) : P →ₗ[k] P where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' := fun c x ↦ smul_comm a c x

/-- Left multiplication on the first tensor factor. -/
def IsIdempotentElem.tensorLeftAction (N : ModuleCat.{v} B) (a : A) :
    TensorProduct k P N →ₗ[k] TensorProduct k P N :=
  TensorProduct.map (leftIdealLeftAction (k := k) (e := e) a) LinearMap.id

@[simp]
theorem IsIdempotentElem.tensorLeftAction_tmul (N : ModuleCat.{v} B)
    (a : A) (x : P) (n : N) :
    tensorLeftAction (k := k) (he := he) N a (x ⊗ₜ[k] n) =
      (a • x) ⊗ₜ[k] n :=
  rfl

theorem IsIdempotentElem.tensorLeftAction_one (N : ModuleCat.{v} B)
    (z : TensorProduct k P N) :
    tensorLeftAction (k := k) (he := he) N 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp
  | add x y ihx ihy => simp [ihx, ihy]

theorem IsIdempotentElem.tensorLeftAction_mul (N : ModuleCat.{v} B)
    (a b : A) (z : TensorProduct k P N) :
    tensorLeftAction (k := k) (he := he) N (a * b) z =
      tensorLeftAction (k := k) (he := he) N a
        (tensorLeftAction (k := k) (he := he) N b z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp [mul_smul]
  | add x y ihx ihy => simp [ihx, ihy]

theorem IsIdempotentElem.tensorLeftAction_add (N : ModuleCat.{v} B)
    (a b : A) (z : TensorProduct k P N) :
    tensorLeftAction (k := k) (he := he) N (a + b) z =
      tensorLeftAction (k := k) (he := he) N a z +
        tensorLeftAction (k := k) (he := he) N b z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp [add_smul, TensorProduct.add_tmul]
  | add x y ihx ihy => simp [ihx, ihy, add_add_add_comm]

theorem IsIdempotentElem.tensorLeftAction_zero (N : ModuleCat.{v} B)
    (z : TensorProduct k P N) :
    tensorLeftAction (k := k) (he := he) N 0 z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp
  | add x y ihx ihy => simp [ihx, ihy]

theorem IsIdempotentElem.tensorLeftAction_algebra_smul (N : ModuleCat.{v} B)
    (c : k) (a : A) (z : TensorProduct k P N) :
    tensorLeftAction (k := k) (he := he) N (c • a) z =
      c • tensorLeftAction (k := k) (he := he) N a z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x n =>
      simp only [tensorLeftAction_tmul]
      rw [IsScalarTower.smul_assoc, TensorProduct.smul_tmul']
  | add x y ihx ihy => simp [ihx, ihy, smul_add]

/-- The balancing submodule is stable under left multiplication by `A`. -/
theorem IsIdempotentElem.tensorLeftAction_mem_balanceSubmodule
    (N : ModuleCat.{v} B) (a : A) {z : TensorProduct k P N}
    (hz : z ∈ balanceSubmodule (k := k) (he := he) N) :
    tensorLeftAction (k := k) (he := he) N a z ∈
      balanceSubmodule (k := k) (he := he) N := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, b, n, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨a • x, b, n, ?_⟩
      simp only [map_sub, tensorLeftAction_tmul]
      rw [smul_comm a (MulOpposite.op b) x]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using
        (balanceSubmodule (k := k) (he := he) N).add_mem ihx ihy
  | smul c z hz ih =>
      rw [map_smul]
      exact (balanceSubmodule (k := k) (he := he) N).smul_mem c ih

/-- Left multiplication induced on the balanced quotient. -/
def IsIdempotentElem.relativeTensorAction (N : ModuleCat.{v} B) (a : A) :
    relativeTensor (k := k) (he := he) N →ₗ[k]
      relativeTensor (k := k) (he := he) N where
  toFun := Quotient.map' (tensorLeftAction (k := k) (he := he) N a) (by
    intro x y hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
    change -x + y ∈ balanceSubmodule (k := k) (he := he) N at hxy
    change -(tensorLeftAction (k := k) (he := he) N a x) +
        tensorLeftAction (k := k) (he := he) N a y ∈
      balanceSubmodule (k := k) (he := he) N
    have h := tensorLeftAction_mem_balanceSubmodule he N a hxy
    rw [map_add] at h
    rw [← map_neg (tensorLeftAction (k := k) (he := he) N a) x]
    exact h)
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        exact congrArg Quotient.mk''
          (map_add (tensorLeftAction (k := k) (he := he) N a) x y)
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      change (Quotient.mk''
          (tensorLeftAction (k := k) (he := he) N a (c • x)) :
            relativeTensor (k := k) (he := he) N) =
        Quotient.mk'' (c • tensorLeftAction (k := k) (he := he) N a x)
      exact congrArg Quotient.mk''
        (map_smul (tensorLeftAction (k := k) (he := he) N a) c x)

@[simp]
theorem IsIdempotentElem.relativeTensorAction_mk (N : ModuleCat.{v} B)
    (a : A) (z : TensorProduct k P N) :
    relativeTensorAction he N a
        (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
      (Quotient.mk'' (tensorLeftAction (k := k) (he := he) N a z) :
        relativeTensor (k := k) (he := he) N) :=
  rfl

instance IsIdempotentElem.relativeTensorSMul (N : ModuleCat.{v} B) :
    SMul A (relativeTensor (k := k) (he := he) N) where
  smul a z := relativeTensorAction he N a z

instance IsIdempotentElem.relativeTensorModule (N : ModuleCat.{v} B) :
    Module A (relativeTensor (k := k) (he := he) N) where
  smul_zero a := map_zero (relativeTensorAction he N a)
  smul_add a x y := map_add (relativeTensorAction he N a) x y
  one_smul z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorAction he N 1
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
          (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)
        rw [relativeTensorAction_mk, tensorLeftAction_one]
  mul_smul a b z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorAction he N (a * b)
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
          relativeTensorAction he N a
            (relativeTensorAction he N b
              (Quotient.mk'' z : relativeTensor (k := k) (he := he) N))
        simp only [relativeTensorAction_mk]
        exact congrArg Quotient.mk'' (tensorLeftAction_mul he N a b z)
  add_smul a b z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorAction he N (a + b)
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
          relativeTensorAction he N a
              (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) +
            relativeTensorAction he N b
              (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)
        simp only [relativeTensorAction_mk]
        exact congrArg Quotient.mk'' (tensorLeftAction_add he N a b z)
  zero_smul z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorAction he N 0
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) = 0
        rw [relativeTensorAction_mk, tensorLeftAction_zero]
        rfl

instance IsIdempotentElem.relativeTensorIsScalarTower (N : ModuleCat.{v} B) :
    IsScalarTower k A (relativeTensor (k := k) (he := he) N) :=
  ⟨fun c a z ↦ by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorAction he N (c • a)
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
          c • relativeTensorAction he N a
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)
        simp only [relativeTensorAction_mk]
        exact congrArg Quotient.mk''
          (tensorLeftAction_algebra_smul he N c a z)⟩

instance IsIdempotentElem.relativeTensorSMulCommClass (N : ModuleCat.{v} B) :
    SMulCommClass k A (relativeTensor (k := k) (he := he) N) :=
  ⟨fun c a z ↦ by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change @SMul.smul k (relativeTensor (k := k) (he := he) N)
              (relativeTensorSMulK he N) c (relativeTensorAction he N a
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)) =
          relativeTensorAction he N a
            (@SMul.smul k (relativeTensor (k := k) (he := he) N)
              (relativeTensorSMulK he N) c (Quotient.mk'' z))
        simp only [relativeTensorAction_mk, relativeTensor_smul_mk,
          map_smul]⟩

/-- The class of a pure tensor in the relative tensor product. -/
def IsIdempotentElem.relativeTmul (N : ModuleCat.{v} B) (x : P) (n : N) :
    relativeTensor (k := k) (he := he) N :=
  Quotient.mk'' (x ⊗ₜ[k] n)

namespace IsIdempotentElem

@[simp]
theorem relativeTmul_add_left (N : ModuleCat.{v} B) (x y : P) (n : N) :
    relativeTmul (k := k) (he := he) N (x + y) n =
      relativeTmul (k := k) (he := he) N x n +
        relativeTmul (k := k) (he := he) N y n := by
  simp [relativeTmul, TensorProduct.add_tmul]

@[simp]
theorem relativeTmul_add_right (N : ModuleCat.{v} B) (x : P) (m n : N) :
    relativeTmul (k := k) (he := he) N x (m + n) =
      relativeTmul (k := k) (he := he) N x m +
        relativeTmul (k := k) (he := he) N x n := by
  simp [relativeTmul, TensorProduct.tmul_add]

@[simp]
theorem relativeTmul_zero_right (N : ModuleCat.{v} B) (x : P) :
    relativeTmul (k := k) (he := he) N x 0 = 0 := by
  apply Quotient.sound
  rw [TensorProduct.tmul_zero]

@[simp]
theorem relativeTmul_balance (N : ModuleCat.{v} B) (x : P) (b : B) (n : N) :
    relativeTmul (k := k) (he := he) N (MulOpposite.op b • x) n =
      relativeTmul (k := k) (he := he) N x (b • n) := by
  apply Quotient.sound
  change QuotientAddGroup.leftRel
    (balanceSubmodule (k := k) (he := he) N).toAddSubgroup
    ((MulOpposite.op b • x) ⊗ₜ[k] n) (x ⊗ₜ[k] (b • n))
  rw [QuotientAddGroup.leftRel_apply]
  change -((MulOpposite.op b • x) ⊗ₜ[k] n) + x ⊗ₜ[k] (b • n) ∈
    balanceSubmodule (k := k) (he := he) N
  have h : (MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n) ∈
      balanceSubmodule (k := k) (he := he) N := Submodule.subset_span (R := k)
    (show (MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n) ∈
      balanceSet (k := k) (he := he) N from ⟨x, b, n, rfl⟩)
  have hneg : -((MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n)) ∈
      balanceSubmodule (k := k) (he := he) N :=
    by
      have h' : (MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n) ∈
          (balanceSubmodule (k := k) (he := he) N).toAddSubgroup := h
      exact @AddSubgroup.neg_mem (TensorProduct k P N) _
        (balanceSubmodule (k := k) (he := he) N).toAddSubgroup _ h'
  convert hneg using 1
  · abel

/-- Multiplication evaluates a pure tensor in `Ae ⊗ eM` in `M`. -/
def relativeEvalBilinear (M : ModuleCat.{v} A) :
    P →ₗ[A] cornerPartObj (k := k) he M →ₗ[k] M where
  toFun x :=
    { toFun := fun m ↦ x.1 • m.1
      map_add' := fun m n ↦ by
        change x.1 • (m.1 + n.1) = x.1 • m.1 + x.1 • n.1
        rw [smul_add]
      map_smul' := fun c m ↦ by
        change x.1 • ((algebraMap k A c * e) • m.1) =
          algebraMap k A c • (x.1 • m.1)
        simp only [← mul_smul]
        exact congrArg (fun a : A ↦ a • m.1) (by
          calc
            x.1 * (algebraMap k A c * e) =
                (x.1 * algebraMap k A c) * e := by rw [mul_assoc]
            _ = (algebraMap k A c * x.1) * e := by
              exact congrArg (fun z : A ↦ z * e) (Algebra.commutes c x.1).symm
            _ = algebraMap k A c * x.1 := by rw [mul_assoc, x.2]) }
  map_add' x y := by
    ext m
    change (x.1 + y.1) • m.1 = x.1 • m.1 + y.1 • m.1
    rw [add_smul]
  map_smul' a x := by
    ext m
    change (a * x.1) • m.1 = a • x.1 • m.1
    rw [mul_smul]

/-- Evaluation before imposing the balancing relations. -/
def relativeEvalTensor (M : ModuleCat.{v} A) :
    TensorProduct k P (cornerPartObj (k := k) he M) →ₗ[A] M :=
  TensorProduct.AlgebraTensorModule.lift
    (relativeEvalBilinear (k := k) he M)

@[simp]
theorem relativeEvalTensor_tmul (M : ModuleCat.{v} A) (x : P)
    (m : cornerPart (k := k) (e := e) M) :
    relativeEvalTensor (k := k) he M (x ⊗ₜ[k] m) = x.1 • m.1 :=
  rfl

/-- Evaluation vanishes on all balancing relations. -/
theorem balanceSubmodule_le_ker_relativeEvalTensor (M : ModuleCat.{v} A) :
    balanceSubmodule (k := k) (he := he) (cornerPartObj (k := k) he M) ≤
      LinearMap.ker ((relativeEvalTensor (k := k) he M).restrictScalars k) := by
  apply Submodule.span_le.2
  rintro z ⟨x, b, n, rfl⟩
  change relativeEvalTensor (k := k) he M
      ((MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n)) = 0
  simp only [map_sub, relativeEvalTensor_tmul, sub_eq_zero]
  change (x.1 * b.1) • n.1 = x.1 • b.1 • n.1
  rw [mul_smul]

set_option maxHeartbeats 800000 in
/-- Evaluation descends to the relative tensor product. -/
def relativeEval (M : ModuleCat.{v} A) : relativeTensor (k := k) (he := he)
    (cornerPartObj (k := k) he M) →ₗ[A] M where
  toFun := Quotient.lift (relativeEvalTensor (k := k) he M) (by
    intro x y hxy
    change QuotientAddGroup.leftRel
      (balanceSubmodule (k := k) (he := he)
        (cornerPartObj (k := k) he M)).toAddSubgroup x y at hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy
    change -x + y ∈
      balanceSubmodule (k := k) (he := he) (cornerPartObj (k := k) he M) at hxy
    have h := balanceSubmodule_le_ker_relativeEvalTensor he M hxy
    rw [LinearMap.mem_ker] at h
    change relativeEvalTensor (k := k) he M (-x + y) = 0 at h
    rw [map_add] at h
    apply eq_of_neg_add_eq_zero
    exact (congrArg (fun t : M ↦ t + relativeEvalTensor (k := k) he M y)
      (map_neg (relativeEvalTensor (k := k) he M) x)).symm.trans h)
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y => exact map_add (relativeEvalTensor (k := k) he M) x y
  map_smul' a x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      change relativeEvalTensor (k := k) he M
          (tensorLeftAction (k := k) (he := he)
            (cornerPartObj (k := k) he M) a x) =
        a • relativeEvalTensor (k := k) he M x
      exact map_smul (relativeEvalTensor (k := k) he M) a x

@[simp]
theorem relativeEval_relativeTmul (M : ModuleCat.{v} A) (x : P)
    (m : cornerPart (k := k) (e := e) M) :
    relativeEval (k := k) he M
        (relativeTmul (k := k) (he := he)
          (cornerPartObj (k := k) he M) x m) =
      x.1 • m.1 :=
  rfl

end IsIdempotentElem

end BalancedTensor

section MoritaFunctors

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

namespace IsIdempotentElem

/-- A module morphism restricts to the idempotent-fixed submodules. -/
def cornerPartMap {M M' : ModuleCat.{v} A} (f : M ⟶ M') :
    cornerPartObj (k := k) he M →ₗ[B]
      cornerPartObj (k := k) he M' where
  toFun m := ⟨f.hom m.1, by
    change e • f.hom m.1 = f.hom m.1
    rw [← map_smul, m.2]⟩
  map_add' m n := Subtype.ext (map_add f.hom m.1 n.1)
  map_smul' b m := Subtype.ext (map_smul f.hom b.1 m.1)

theorem cornerPartMap_smul {M M' : ModuleCat.{v} A} (f : M ⟶ M')
    (c : k) (m : cornerPartObj (k := k) he M) :
    cornerPartMap he (c • f) m = c • cornerPartMap he f m := by
  apply Subtype.ext
  change algebraMap k A c • f.hom m.1 =
    (algebraMap k A c * e) • f.hom m.1
  have hfix : e • f.hom m.1 = f.hom m.1 := by
    rw [← map_smul, m.2]
  exact (congrArg (fun y : M' ↦ algebraMap k A c • y) hfix.symm).trans
    (mul_smul (algebraMap k A c) e (f.hom m.1)).symm

/-- The functor `M ↦ eM`. -/
def cornerPartFunctor : ModuleCat.{v} A ⥤ ModuleCat.{v} B where
  obj M := cornerPartObj (k := k) he M
  map f := ModuleCat.ofHom (cornerPartMap he f)
  map_id M := by
    apply ModuleCat.hom_ext
    ext m
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext m
    rfl

instance cornerPartFunctorLinear :
    (cornerPartFunctor (k := k) (A := A) he).Linear k where
  map_smul {M N} f c := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change cornerPartMap he (c • f) m = c • cornerPartMap he f m
    exact cornerPartMap_smul he f c m

/-- The tensor map before taking balanced quotients. -/
def relativeTensorMapTensor {N N' : ModuleCat.{v} B} (f : N ⟶ N') :
    TensorProduct k P N →ₗ[k] TensorProduct k P N' :=
  TensorProduct.map LinearMap.id (f.hom.restrictScalars k)

@[simp]
theorem relativeTensorMapTensor_tmul {N N' : ModuleCat.{v} B}
    (f : N ⟶ N') (x : P) (n : N) :
    relativeTensorMapTensor (k := k) (he := he) f (x ⊗ₜ[k] n) =
      x ⊗ₜ[k] f n :=
  rfl

theorem relativeTensorMapTensor_mem_balanceSubmodule
    {N N' : ModuleCat.{v} B} (f : N ⟶ N') {z : TensorProduct k P N}
    (hz : z ∈ balanceSubmodule (k := k) (he := he) N) :
    relativeTensorMapTensor (k := k) (he := he) f z ∈
      balanceSubmodule (k := k) (he := he) N' := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, b, n, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨x, b, f n, ?_⟩
      simp only [map_sub, relativeTensorMapTensor_tmul]
      rw [map_smul]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa using (balanceSubmodule (k := k) (he := he) N').add_mem ihx ihy
  | smul c z hz ih =>
      rw [map_smul]
      exact (balanceSubmodule (k := k) (he := he) N').smul_mem c ih

set_option maxHeartbeats 800000 in
/-- The induced `k`-linear map on balanced tensor products. -/
def relativeTensorMapK {N N' : ModuleCat.{v} B} (f : N ⟶ N') :
    relativeTensor (k := k) (he := he) N →ₗ[k]
      relativeTensor (k := k) (he := he) N' where
  toFun := Quotient.map' (relativeTensorMapTensor (k := k) (he := he) f) (by
    intro x y hxy
    change QuotientAddGroup.leftRel
      (balanceSubmodule (k := k) (he := he) N).toAddSubgroup x y at hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy ⊢
    change -x + y ∈ balanceSubmodule (k := k) (he := he) N at hxy
    change -(relativeTensorMapTensor (k := k) (he := he) f x) +
        relativeTensorMapTensor (k := k) (he := he) f y ∈
      balanceSubmodule (k := k) (he := he) N'
    have h := relativeTensorMapTensor_mem_balanceSubmodule he f hxy
    rw [map_add] at h
    rw [← map_neg (relativeTensorMapTensor (k := k) (he := he) f) x]
    exact h)
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        exact congrArg Quotient.mk''
          (map_add (relativeTensorMapTensor (k := k) (he := he) f) x y)
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      change (Quotient.mk''
          (relativeTensorMapTensor (k := k) (he := he) f (c • x)) :
            relativeTensor (k := k) (he := he) N') =
        Quotient.mk'' (c • relativeTensorMapTensor (k := k) (he := he) f x)
      exact congrArg Quotient.mk''
        (map_smul (relativeTensorMapTensor (k := k) (he := he) f) c x)

@[simp]
theorem relativeTensorMapK_mk {N N' : ModuleCat.{v} B} (f : N ⟶ N')
    (z : TensorProduct k P N) :
    relativeTensorMapK he f
        (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
      (Quotient.mk'' (relativeTensorMapTensor (k := k) (he := he) f z) :
        relativeTensor (k := k) (he := he) N') :=
  rfl

/-- The induced map is `A`-linear. -/
def relativeTensorMap {N N' : ModuleCat.{v} B} (f : N ⟶ N') :
    relativeTensor (k := k) (he := he) N →ₗ[A]
      relativeTensor (k := k) (he := he) N' where
  __ := relativeTensorMapK he f
  map_smul' a z := by
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorMapK he f
            (relativeTensorAction he N a
              (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)) =
          relativeTensorAction he N' a
            (relativeTensorMapK he f
              (Quotient.mk'' z : relativeTensor (k := k) (he := he) N))
        simp only [relativeTensorAction_mk, relativeTensorMapK_mk]
        congr 1
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x n => simp
        | add x y ihx ihy => simp [ihx, ihy]

/-- The functor `N ↦ Ae ⊗_{eAe} N`. -/
def relativeTensorFunctor : ModuleCat.{v} B ⥤ ModuleCat.{v} A where
  obj N := ModuleCat.of A (relativeTensor (k := k) (he := he) N)
  map f := ModuleCat.ofHom (relativeTensorMap he f)
  map_id N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorMapK he (𝟙 N)
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) N) =
          (Quotient.mk'' z : relativeTensor (k := k) (he := he) N)
        rw [relativeTensorMapK_mk]
        congr 1
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x n => rfl
        | add x y ihx ihy => simp [ihx, ihy]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using Quotient.inductionOn' with
    | _ z =>
        change relativeTensorMapK he (f ≫ g)
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) _) =
          relativeTensorMapK he g (relativeTensorMapK he f
            (Quotient.mk'' z : relativeTensor (k := k) (he := he) _))
        simp only [relativeTensorMapK_mk]
        congr 1
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul x n => rfl
        | add x y ihx ihy => simp [ihx, ihy]

theorem relativeTensorMap_smul_relativeTmul {N N' : ModuleCat.{v} B}
    (f : N ⟶ N') (c : k) (x : P) (n : N) :
    relativeTensorMap he (c • f)
        (relativeTmul (k := k) (he := he) N x n) =
      algebraMap k A c • relativeTensorMap he f
        (relativeTmul (k := k) (he := he) N x n) := by
  change relativeTmul (k := k) (he := he) N' x ((c • f).hom n) =
    relativeTensorAction he N' (algebraMap k A c)
      (relativeTmul (k := k) (he := he) N' x (f.hom n))
  rw [show (c • f).hom n = (algebraMap k B c) • f.hom n by rfl]
  rw [← relativeTmul_balance]
  change relativeTmul (k := k) (he := he) N'
      (MulOpposite.op (algebraMap k B c) • x) (f.hom n) =
    relativeTensorAction he N' (algebraMap k A c)
      (Quotient.mk'' (x ⊗ₜ[k] f.hom n))
  rw [relativeTensorAction_mk, tensorLeftAction_tmul]
  apply congrArg Quotient.mk''
  congr 1
  apply Subtype.ext
  change x.1 * (algebraMap k A c * e) = algebraMap k A c * x.1
  calc
    x.1 * (algebraMap k A c * e) =
        (x.1 * algebraMap k A c) * e := by rw [mul_assoc]
    _ = (algebraMap k A c * x.1) * e := by
      exact congrArg (fun z : A ↦ z * e) (Algebra.commutes c x.1).symm
    _ = algebraMap k A c * x.1 := by rw [mul_assoc, x.2]

theorem relativeTensorMap_smul {N N' : ModuleCat.{v} B} (f : N ⟶ N')
    (c : k) (z : relativeTensor (k := k) (he := he) N) :
    relativeTensorMap he (c • f) z =
      algebraMap k A c • relativeTensorMap he f z := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero =>
          change (Quotient.mk''
              (relativeTensorMapTensor (k := k) (he := he) (c • f) 0) :
                relativeTensor (k := k) (he := he) N') =
            relativeTensorAction he N' (algebraMap k A c)
              (Quotient.mk''
                (relativeTensorMapTensor (k := k) (he := he) f 0))
          rw [map_zero, map_zero, relativeTensorAction_mk, map_zero]
      | tmul x n => exact relativeTensorMap_smul_relativeTmul he f c x n
      | add x y ihx ihy =>
          change (Quotient.mk''
              (relativeTensorMapTensor (k := k) (he := he) (c • f) (x + y)) :
                relativeTensor (k := k) (he := he) N') =
            relativeTensorAction he N' (algebraMap k A c)
              (Quotient.mk''
                (relativeTensorMapTensor (k := k) (he := he) f (x + y)))
          rw [map_add, map_add, relativeTensorAction_mk, map_add]
          exact congrArg₂
            (fun a b : (relativeTensorFunctor (k := k) (A := A) he).obj N' ↦ a + b)
            ihx ihy

instance relativeTensorFunctorLinear :
    (relativeTensorFunctor (k := k) (A := A) he).Linear k where
  map_smul {M N} f c := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change relativeTensorMap he (c • f) z =
      algebraMap k A c • relativeTensorMap he f z
    exact relativeTensorMap_smul he f c z

end IsIdempotentElem

end MoritaFunctors

section MoritaUnit

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

namespace IsIdempotentElem

/-- The `Ae` factor attached to one term of a fullness certificate. -/
def certificateLeftFactor (p : A × A) : P :=
  ⟨p.1 * e, by
    change (p.1 * e) * e = p.1 * e
    rw [mul_assoc, he.eq]⟩

/-- The `eM` factor attached to one term of a fullness certificate. -/
def certificateRightFactor (M : ModuleCat.{v} A) (p : A × A) (m : M) :
    cornerPartObj (k := k) he M :=
  ⟨(e * p.2) • m, by
    change e • (e * p.2) • m = (e * p.2) • m
    rw [← mul_smul, ← mul_assoc, he.eq]⟩

/-- The raw inverse to multiplication, obtained from a fixed expression
`1 = ∑ xᵢ e yᵢ`. -/
def relativeEvalInverseFunction (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) (m : M) :
    relativeTensor (k := k) (he := he)
      (cornerPartObj (k := k) he M) :=
  (C.terms.map fun p ↦
    relativeTmul (k := k) (he := he)
      (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p m)).sum

@[simp]
theorem relativeEvalInverseFunction_zero (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) :
    relativeEvalInverseFunction (k := k) he C M 0 = 0 := by
  change (C.terms.map fun p ↦
    relativeTmul (k := k) (he := he) (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p 0)).sum = 0
  induction C.terms with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hright : certificateRightFactor (k := k) (he := he) M p 0 = 0 := by
        apply Subtype.ext
        exact smul_zero (e * p.2)
      rw [hright]
      rw [relativeTmul_zero_right, ih, zero_add]

@[simp]
theorem relativeEvalInverseFunction_add (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) (m n : M) :
    relativeEvalInverseFunction (k := k) he C M (m + n) =
      relativeEvalInverseFunction (k := k) he C M m +
        relativeEvalInverseFunction (k := k) he C M n := by
  change (C.terms.map fun p ↦ relativeTmul (k := k) (he := he)
      (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p (m + n))).sum =
    (C.terms.map fun p ↦ relativeTmul (k := k) (he := he)
      (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p m)).sum +
    (C.terms.map fun p ↦ relativeTmul (k := k) (he := he)
      (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p n)).sum
  induction C.terms with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [show certificateRightFactor (k := k) (he := he) M p (m + n) =
          certificateRightFactor (k := k) (he := he) M p m +
            certificateRightFactor (k := k) (he := he) M p n by
        apply Subtype.ext
        exact smul_add (e * p.2) m n]
      rw [relativeTmul_add_right]
      rw [ih]
      abel

/-- Evaluating the certificate formula gives back the original vector. -/
theorem relativeEval_apply_inverseFunction (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) (m : M) :
    relativeEval (k := k) he M
      (relativeEvalInverseFunction (k := k) he C M m) = m := by
  simp only [relativeEvalInverseFunction, map_list_sum, List.map_map]
  change (C.terms.map fun p ↦ (p.1 * e) • ((e * p.2) • m)).sum = m
  simp only [← mul_smul]
  have hterms :
      (C.terms.map fun p ↦ (p.1 * e) * (e * p.2)).sum = 1 := by
    have hterm (p : A × A) :
        (p.1 * e) * (e * p.2) = p.1 * (e * p.2) := by
      rw [← mul_assoc (p.1 * e) e p.2, mul_assoc p.1 e e, he.eq,
        mul_assoc]
    rw [List.map_congr_left (fun p _ ↦ hterm p)]
    exact C.sum_mul
  have hsum (xs : List A) :
      (xs.map fun a ↦ a • m).sum = xs.sum • m := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, add_smul]
  have hmap :
      (C.terms.map fun p ↦ ((p.1 * e) * (e * p.2)) • m) =
        (C.terms.map fun p ↦ (p.1 * e) * (e * p.2)).map
          (fun a ↦ a • m) := by
    rw [List.map_map]
    rfl
  rw [hmap]
  rw [hsum, hterms, one_smul]

/-- The middle coefficient used to move a certificate term across the
balanced tensor product. -/
def certificateMiddle (p : A × A) (x : P) : B :=
  ⟨e * p.2 * x.1, by
    refine (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩
    · rw [← mul_assoc e (e * p.2) x.1,
        ← mul_assoc e e p.2, he.eq]
    · rw [mul_assoc, x.2]⟩

theorem certificateRightFactor_smul (M : ModuleCat.{v} A)
    (p : A × A) (x : P) (m : cornerPartObj (k := k) he M) :
    certificateRightFactor (k := k) (he := he) M p (x.1 • m.1) =
      certificateMiddle (k := k) (he := he) p x • m := by
  apply Subtype.ext
  change (e * p.2) • x.1 • m.1 = (e * p.2 * x.1) • m.1
  rw [← mul_smul]

theorem sum_relativeTmul_eq_relativeTmul_sum
    (N : ModuleCat.{v} B) (xs : List P) (n : N) :
    (xs.map fun x ↦ relativeTmul (k := k) (he := he) N x n).sum =
      relativeTmul (k := k) (he := he) N xs.sum n := by
  induction xs with
  | nil => simp [relativeTmul]
  | cons x xs ih => simp [ih, relativeTmul_add_left]

theorem certificateSummedLeft_eq (C : FullnessCertificate e) (x : P) :
    (C.terms.map fun p ↦
      MulOpposite.op (certificateMiddle (k := k) (he := he) p x) •
        certificateLeftFactor (k := k) he p).sum = x := by
  apply Subtype.ext
  have hval :
      ((C.terms.map fun p ↦
        MulOpposite.op (certificateMiddle (k := k) (he := he) p x) •
          certificateLeftFactor (k := k) he p).sum : P).1 =
        (C.terms.map fun p ↦ (p.1 * e) * (e * p.2 * x.1)).sum := by
    induction C.terms with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        change (p.1 * e) * (e * p.2 * x.1) +
            ((ps.map fun q ↦
              MulOpposite.op (certificateMiddle (k := k) (he := he) q x) •
                certificateLeftFactor (k := k) he q).sum : P).1 = _
        rw [ih]
  rw [hval]
  have hfactor :
      (C.terms.map fun p ↦ (p.1 * e) * (e * p.2 * x.1)).sum =
        (C.terms.map fun p ↦ p.1 * (e * p.2)).sum * x.1 := by
    induction C.terms with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih, add_mul]
        congr 1
        rw [← mul_assoc (p.1 * e) (e * p.2) x.1,
          ← mul_assoc (p.1 * e) e p.2, mul_assoc p.1 e e, he.eq,
          mul_assoc p.1 e p.2]
  rw [hfactor, C.sum_mul, one_mul]

theorem relativeEvalInverseFunction_apply_eval_tmul
    (C : FullnessCertificate e) (M : ModuleCat.{v} A) (x : P)
    (m : cornerPartObj (k := k) he M) :
    relativeEvalInverseFunction (k := k) he C M (x.1 • m.1) =
      relativeTmul (k := k) (he := he)
        (cornerPartObj (k := k) he M) x m := by
  change (C.terms.map fun p ↦ relativeTmul (k := k) (he := he)
      (cornerPartObj (k := k) he M)
      (certificateLeftFactor (k := k) he p)
      (certificateRightFactor (k := k) (he := he) M p (x.1 • m.1))).sum = _
  have hterm (p : A × A) :
      relativeTmul (k := k) (he := he)
          (cornerPartObj (k := k) he M)
          (certificateLeftFactor (k := k) he p)
          (certificateRightFactor (k := k) (he := he) M p (x.1 • m.1)) =
        relativeTmul (k := k) (he := he)
          (cornerPartObj (k := k) he M)
          (MulOpposite.op (certificateMiddle (k := k) (he := he) p x) •
            certificateLeftFactor (k := k) he p) m := by
    rw [certificateRightFactor_smul]
    exact (relativeTmul_balance he _ _ _ _).symm
  rw [List.map_congr_left (fun p _ ↦ hterm p)]
  have hmap :
      (C.terms.map fun p ↦ relativeTmul (k := k) (he := he)
        (cornerPartObj (k := k) he M)
        (MulOpposite.op (certificateMiddle (k := k) (he := he) p x) •
          certificateLeftFactor (k := k) he p) m) =
      (C.terms.map fun p ↦
        MulOpposite.op (certificateMiddle (k := k) (he := he) p x) •
          certificateLeftFactor (k := k) he p).map fun y ↦
        relativeTmul (k := k) (he := he)
          (cornerPartObj (k := k) he M) y m := by
    rw [List.map_map]
    rfl
  rw [hmap]
  rw [sum_relativeTmul_eq_relativeTmul_sum, certificateSummedLeft_eq]

/-- The certificate formula is also a left inverse to evaluation. -/
theorem relativeEvalInverseFunction_apply_eval (C : FullnessCertificate e)
    (M : ModuleCat.{v} A)
    (z : relativeTensor (k := k) (he := he)
      (cornerPartObj (k := k) he M)) :
    relativeEvalInverseFunction (k := k) he C M
      (relativeEval (k := k) he M z) = z := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero => exact relativeEvalInverseFunction_zero (k := k) he C M
      | tmul x m =>
          change relativeEvalInverseFunction (k := k) he C M (x.1 • m.1) =
            (Quotient.mk'' (x ⊗ₜ[k] m) :
              relativeTensor (k := k) (he := he)
                (cornerPartObj (k := k) he M))
          exact relativeEvalInverseFunction_apply_eval_tmul he C M x m
      | add x y ihx ihy =>
          change relativeEvalInverseFunction (k := k) he C M
              (relativeEvalTensor (k := k) he M x) =
            (Quotient.mk'' x : relativeTensor (k := k) (he := he)
              (cornerPartObj (k := k) he M)) at ihx
          change relativeEvalInverseFunction (k := k) he C M
              (relativeEvalTensor (k := k) he M y) =
            (Quotient.mk'' y : relativeTensor (k := k) (he := he)
              (cornerPartObj (k := k) he M)) at ihy
          change relativeEvalInverseFunction (k := k) he C M
              (relativeEvalTensor (k := k) he M (x + y)) =
            (Quotient.mk'' (x + y) : relativeTensor (k := k) (he := he)
              (cornerPartObj (k := k) he M))
          rw [map_add, relativeEvalInverseFunction_add (k := k), ihx, ihy]
          rfl

/-- Multiplication `Ae ⊗_{eAe} eM → M` is bijective for a full idempotent. -/
theorem relativeEval_bijective (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) :
    Function.Bijective (relativeEval (k := k) he M) := by
  exact ⟨
    fun x y h ↦ by
      rw [← relativeEvalInverseFunction_apply_eval he C M x,
        ← relativeEvalInverseFunction_apply_eval he C M y, h],
    fun m ↦ ⟨relativeEvalInverseFunction (k := k) he C M m,
      relativeEval_apply_inverseFunction he C M m⟩⟩

/-- The multiplication isomorphism `Ae ⊗_{eAe} eM ≃ M`. -/
def relativeEvalLinearEquiv (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) :
    relativeTensor (k := k) (he := he)
        (cornerPartObj (k := k) he M) ≃ₗ[A] M :=
  LinearEquiv.ofBijective (relativeEval (k := k) he M)
    (relativeEval_bijective he C M)

end IsIdempotentElem

end MoritaUnit

section MoritaCounit

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

namespace IsIdempotentElem

/-- Left multiplication by `e` regards an element of `Ae` as an element
of the corner algebra. -/
def leftCornerCoefficient (x : P) : B :=
  ⟨e * x.1, by
    refine (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, he.eq]
    · rw [mul_assoc, x.2]⟩

@[simp]
theorem leftCornerCoefficient_val (x : P) :
    (leftCornerCoefficient (k := k) (he := he) x).1 = e * x.1 :=
  rfl

/-- The bilinear evaluation `(x,n) ↦ (ex)n` before imposing the
balancing relations. -/
def relativeCounitBilinear (N : ModuleCat.{v} B) :
    P →ₗ[k] N →ₗ[k] N where
  toFun x :=
    { toFun := fun n ↦ leftCornerCoefficient (k := k) (he := he) x • n
      map_add' := fun m n ↦ smul_add _ m n
      map_smul' := fun c n ↦ by
        exact (smul_comm c (leftCornerCoefficient (k := k) (he := he) x) n).symm }
  map_add' x y := by
    ext n
    have hcoef : leftCornerCoefficient (k := k) (he := he) (x + y) =
        leftCornerCoefficient (k := k) (he := he) x +
          leftCornerCoefficient (k := k) (he := he) y := by
      apply Subtype.ext
      exact mul_add e x.1 y.1
    change leftCornerCoefficient (k := k) (he := he) (x + y) • n =
        leftCornerCoefficient (k := k) (he := he) x • n +
          leftCornerCoefficient (k := k) (he := he) y • n
    rw [hcoef]
    exact add_smul _ _ n
  map_smul' c x := by
    ext n
    have hcoef : leftCornerCoefficient (k := k) (he := he) (c • x) =
        c • leftCornerCoefficient (k := k) (he := he) x := by
      apply Subtype.ext
      change e * (c • x.1) =
        (IsIdempotentElem.cornerAlgebraMap he c *
          leftCornerCoefficient (k := k) (he := he) x).1
      rw [Algebra.smul_def]
      exact calc
        e * (algebraMap k A c * x.1) =
            (e * algebraMap k A c) * x.1 := by rw [mul_assoc]
        _ = (algebraMap k A c * e) * x.1 := by rw [Algebra.commutes c e]
        _ = (algebraMap k A c * e) * (e * x.1) := by
          rw [← mul_assoc, mul_assoc (algebraMap k A c) e e, he.eq]
    change leftCornerCoefficient (k := k) (he := he) (c • x) • n =
      c • (leftCornerCoefficient (k := k) (he := he) x • n)
    rw [hcoef]
    exact smul_assoc c (leftCornerCoefficient (k := k) (he := he) x) n

/-- Evaluation on the ordinary tensor product before balancing. -/
def relativeCounitTensor (N : ModuleCat.{v} B) :
    TensorProduct k P N →ₗ[k] N :=
  TensorProduct.lift (relativeCounitBilinear (k := k) (he := he) N)

@[simp]
theorem relativeCounitTensor_tmul (N : ModuleCat.{v} B) (x : P) (n : N) :
    relativeCounitTensor (k := k) (he := he) N (x ⊗ₜ[k] n) =
      leftCornerCoefficient (k := k) (he := he) x • n :=
  rfl

/-- The evaluation kills the balancing relations. -/
theorem balanceSubmodule_le_ker_relativeCounitTensor (N : ModuleCat.{v} B) :
    balanceSubmodule (k := k) (he := he) N ≤
      LinearMap.ker (relativeCounitTensor (k := k) (he := he) N) := by
  apply Submodule.span_le.2
  rintro z ⟨x, b, n, rfl⟩
  change relativeCounitTensor (k := k) (he := he) N
      ((MulOpposite.op b • x) ⊗ₜ[k] n - x ⊗ₜ[k] (b • n)) = 0
  simp only [map_sub, relativeCounitTensor_tmul, sub_eq_zero]
  have hcoef : leftCornerCoefficient (k := k) (he := he)
      (MulOpposite.op b • x) =
        leftCornerCoefficient (k := k) (he := he) x * b := by
    apply Subtype.ext
    change e * (x.1 * b.1) = (e * x.1) * b.1
    rw [mul_assoc]
  rw [hcoef, mul_smul]

set_option maxHeartbeats 800000 in
/-- Evaluation on the balanced tensor product. -/
def relativeCounitK (N : ModuleCat.{v} B) :
    relativeTensor (k := k) (he := he) N →ₗ[k] N where
  toFun := Quotient.lift (relativeCounitTensor (k := k) (he := he) N) (by
    intro x y hxy
    change QuotientAddGroup.leftRel
      (balanceSubmodule (k := k) (he := he) N).toAddSubgroup x y at hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy
    change -x + y ∈ balanceSubmodule (k := k) (he := he) N at hxy
    have h := balanceSubmodule_le_ker_relativeCounitTensor he N hxy
    rw [LinearMap.mem_ker] at h
    change relativeCounitTensor (k := k) (he := he) N (-x + y) = 0 at h
    rw [map_add] at h
    apply eq_of_neg_add_eq_zero
    exact (congrArg (fun t : N ↦
      t + relativeCounitTensor (k := k) (he := he) N y)
      (map_neg (relativeCounitTensor (k := k) (he := he) N) x)).symm.trans h)
  map_add' x y := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y => exact map_add (relativeCounitTensor (k := k) (he := he) N) x y
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ x => exact map_smul (relativeCounitTensor (k := k) (he := he) N) c x

@[simp]
theorem relativeCounitK_relativeTmul (N : ModuleCat.{v} B) (x : P) (n : N) :
    relativeCounitK (k := k) he N (relativeTmul (k := k) (he := he) N x n) =
      leftCornerCoefficient (k := k) (he := he) x • n :=
  rfl

/-- The raw counit intertwines the corner action. -/
theorem relativeCounitK_corner_smul (N : ModuleCat.{v} B) (b : B)
    (z : relativeTensor (k := k) (he := he) N) :
    relativeCounitK (k := k) he N (b.1 • z) =
      b • relativeCounitK (k := k) he N z := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x n =>
          change leftCornerCoefficient (k := k) (he := he) (b.1 • x) • n =
            b • (leftCornerCoefficient (k := k) (he := he) x • n)
          have hcoef : leftCornerCoefficient (k := k) (he := he) (b.1 • x) =
              b * leftCornerCoefficient (k := k) (he := he) x := by
            apply Subtype.ext
            obtain ⟨hb_left, hb_right⟩ := (Subsemigroup.mem_corner_iff he).mp b.2
            change e * (b.1 * x.1) = b.1 * (e * x.1)
            calc
              e * (b.1 * x.1) = (e * b.1) * x.1 := by rw [mul_assoc]
              _ = b.1 * x.1 := by rw [hb_left]
              _ = (b.1 * e) * x.1 := by rw [hb_right]
              _ = b.1 * (e * x.1) := by rw [mul_assoc]
          rw [hcoef, mul_smul]
      | add x y ihx ihy =>
          change relativeCounitTensor (k := k) (he := he) N
              (tensorLeftAction (k := k) (he := he) N b.1 (x + y)) =
            b • relativeCounitTensor (k := k) (he := he) N (x + y)
          change relativeCounitTensor (k := k) (he := he) N
              (tensorLeftAction (k := k) (he := he) N b.1 x) =
            b • relativeCounitTensor (k := k) (he := he) N x at ihx
          change relativeCounitTensor (k := k) (he := he) N
              (tensorLeftAction (k := k) (he := he) N b.1 y) =
            b • relativeCounitTensor (k := k) (he := he) N y at ihy
          calc
            relativeCounitTensor (k := k) (he := he) N
                (tensorLeftAction (k := k) (he := he) N b.1 (x + y)) =
              relativeCounitTensor (k := k) (he := he) N
                  (tensorLeftAction (k := k) (he := he) N b.1 x) +
                relativeCounitTensor (k := k) (he := he) N
                  (tensorLeftAction (k := k) (he := he) N b.1 y) := by
                    rw [map_add, map_add]
            _ = b • relativeCounitTensor (k := k) (he := he) N x +
                b • relativeCounitTensor (k := k) (he := he) N y := by
                  rw [ihx, ihy]
            _ = b • (relativeCounitTensor (k := k) (he := he) N x +
                relativeCounitTensor (k := k) (he := he) N y) := by
                  rw [smul_add]
            _ = b • relativeCounitTensor (k := k) (he := he) N (x + y) := by
                  rw [map_add]

/-- Restriction of the raw counit to the `e`-fixed part. -/
def relativeCounit (N : ModuleCat.{v} B) :
    cornerPartObj (k := k) he ((relativeTensorFunctor (k := k) (A := A) he).obj N) →ₗ[B] N where
  toFun z := relativeCounitK (k := k) he N z.1
  map_add' z w := map_add (relativeCounitK (k := k) he N) z.1 w.1
  map_smul' b z := relativeCounitK_corner_smul he N b z.1

/-- The copy of `e` in the left ideal `Ae`. -/
def cornerGenerator : P :=
  ⟨e, he.eq⟩

/-- The inverse counit sends `n` to the fixed tensor `e ⊗ n`. -/
def relativeCounitInverseFunction (N : ModuleCat.{v} B) (n : N) :
    cornerPartObj (k := k) he ((relativeTensorFunctor (k := k) (A := A) he).obj N) :=
  ⟨relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he) n, by
    change relativeTensorAction he N e
        (relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he) n) =
      relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he) n
    change relativeTensorAction he N e
        (Quotient.mk'' ((cornerGenerator (k := k) he) ⊗ₜ[k] n)) = _
    rw [relativeTensorAction_mk, tensorLeftAction_tmul]
    apply congrArg Quotient.mk''
    congr 1
    apply Subtype.ext
    exact he.eq⟩

/-- The inverse counit as a corner-linear map. -/
def relativeCounitInverse (N : ModuleCat.{v} B) :
    N →ₗ[B]
      cornerPartObj (k := k) he ((relativeTensorFunctor (k := k) (A := A) he).obj N) where
  toFun := relativeCounitInverseFunction (k := k) he N
  map_add' n n' := by
    apply Subtype.ext
    exact relativeTmul_add_right (k := k) he N (cornerGenerator (k := k) he) n n'
  map_smul' b n := by
    apply Subtype.ext
    change relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he) (b • n) =
      b.1 • relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he) n
    rw [← relativeTmul_balance]
    change relativeTmul (k := k) (he := he) N
        (MulOpposite.op b • cornerGenerator (k := k) he) n =
      relativeTensorAction he N b.1
        (Quotient.mk'' ((cornerGenerator (k := k) he) ⊗ₜ[k] n))
    rw [relativeTensorAction_mk, tensorLeftAction_tmul]
    apply congrArg Quotient.mk''
    congr 1
    apply Subtype.ext
    obtain ⟨hb_left, hb_right⟩ := (Subsemigroup.mem_corner_iff he).mp b.2
    change e * b.1 = b.1 * e
    rw [hb_left, hb_right]

@[simp]
theorem relativeCounit_apply_inverse (N : ModuleCat.{v} B) (n : N) :
    relativeCounit (k := k) he N (relativeCounitInverse (k := k) he N n) = n := by
  change leftCornerCoefficient (k := k) (he := he) (cornerGenerator (k := k) he) • n = n
  have hcoeff : leftCornerCoefficient (k := k) (he := he)
      (cornerGenerator (k := k) he) = 1 := by
    apply Subtype.ext
    change e * e = e
    exact he.eq
  rw [hcoeff, one_smul]

/-- On an arbitrary relative tensor, inverse-after-evaluation is multiplication by `e`. -/
theorem relativeCounitInverse_raw (N : ModuleCat.{v} B)
    (z : relativeTensor (k := k) (he := he) N) :
    (relativeCounitInverse (k := k) he N
      (relativeCounitK (k := k) he N z)).1 = e • z := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero =>
          change (relativeCounitInverse (k := k) he N 0).1 =
            e • (0 : relativeTensor (k := k) (he := he) N)
          rw [map_zero, smul_zero]
          rfl
      | tmul x n =>
          change relativeTmul (k := k) (he := he) N (cornerGenerator (k := k) he)
              (leftCornerCoefficient (k := k) (he := he) x • n) =
            relativeTensorAction he N e (Quotient.mk'' (x ⊗ₜ[k] n))
          rw [← relativeTmul_balance, relativeTensorAction_mk,
            tensorLeftAction_tmul]
          apply congrArg Quotient.mk''
          congr 1
          apply Subtype.ext
          change e * (e * x.1) = e * x.1
          rw [← mul_assoc, he.eq]
      | add x y ihx ihy =>
          change ((relativeCounitInverse (k := k) he N)
              (relativeCounitTensor (k := k) (he := he) N (x + y))).1 =
            (Quotient.mk''
              (tensorLeftAction (k := k) (he := he) N e (x + y)) :
                relativeTensor (k := k) (he := he) N)
          change ((relativeCounitInverse (k := k) he N)
              (relativeCounitTensor (k := k) (he := he) N x)).1 =
            (Quotient.mk'' (tensorLeftAction (k := k) (he := he) N e x) :
              relativeTensor (k := k) (he := he) N) at ihx
          change ((relativeCounitInverse (k := k) he N)
              (relativeCounitTensor (k := k) (he := he) N y)).1 =
            (Quotient.mk'' (tensorLeftAction (k := k) (he := he) N e y) :
              relativeTensor (k := k) (he := he) N) at ihy
          rw [map_add, map_add]
          change ((relativeCounitInverse (k := k) he N
              (relativeCounitTensor (k := k) (he := he) N x)).1 +
            (relativeCounitInverse (k := k) he N
              (relativeCounitTensor (k := k) (he := he) N y)).1) = _
          rw [ihx, ihy]
          change (Quotient.mk''
              (tensorLeftAction (k := k) (he := he) N e x +
                tensorLeftAction (k := k) (he := he) N e y) :
              relativeTensor (k := k) (he := he) N) = _
          exact congrArg Quotient.mk''
            (map_add (tensorLeftAction (k := k) (he := he) N e) x y).symm

@[simp]
theorem relativeCounitInverse_apply (N : ModuleCat.{v} B)
    (z : cornerPartObj (k := k) he
      ((relativeTensorFunctor (k := k) (A := A) he).obj N)) :
    relativeCounitInverse (k := k) he N (relativeCounit (k := k) he N z) = z := by
  apply Subtype.ext
  change (relativeCounitInverse (k := k) he N
      (relativeCounitK (k := k) he N z.1)).1 = z.1
  rw [relativeCounitInverse_raw]
  exact z.2

/-- The counit is a linear equivalence on the fixed part. -/
def relativeCounitLinearEquiv (N : ModuleCat.{v} B) :
    cornerPartObj (k := k) he ((relativeTensorFunctor (k := k) (A := A) he).obj N) ≃ₗ[B] N :=
  LinearEquiv.ofBijective (relativeCounit (k := k) he N) ⟨
    fun z w h ↦ by
      rw [← relativeCounitInverse_apply (k := k) he N z,
        ← relativeCounitInverse_apply (k := k) he N w, h],
    fun n ↦ ⟨relativeCounitInverse (k := k) he N n,
      relativeCounit_apply_inverse (k := k) he N n⟩⟩

end IsIdempotentElem

end MoritaCounit

section MoritaEquivalence

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {e : A} (he : IsIdempotentElem e)

local notation "B" => he.Corner
local notation "P" => IsIdempotentElem.leftIdeal (k := k) (e := e)

local instance : Algebra k B := IsIdempotentElem.cornerAlgebra he
local instance (N : ModuleCat.{v} B) :
    HasQuotient (TensorProduct k P N) (Submodule k (TensorProduct k P N)) :=
  @Submodule.hasQuotient k (TensorProduct k P N) _ _ TensorProduct.instModule

namespace IsIdempotentElem

/-- Naturality of multiplication `Ae ⊗ eM → M`. -/
theorem relativeEval_naturality {M M' : ModuleCat.{v} A} (f : M ⟶ M')
    (z : relativeTensor (k := k) (he := he) (cornerPartObj (k := k) he M)) :
    relativeEval (k := k) he M'
        (relativeTensorMap he (ModuleCat.ofHom (cornerPartMap he f)) z) =
      f (relativeEval (k := k) he M z) := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero =>
          change relativeEvalTensor (k := k) he M'
              (relativeTensorMapTensor (k := k) (he := he)
                (ModuleCat.ofHom (cornerPartMap he f)) 0) =
            f.hom (relativeEvalTensor (k := k) he M 0)
          rw [map_zero, map_zero, map_zero]
          exact (map_zero f.hom).symm
      | tmul x m =>
          change x.1 • f.hom m.1 = f.hom (x.1 • m.1)
          rw [map_smul]
      | add x y ihx ihy =>
          change relativeEvalTensor (k := k) he M'
              (relativeTensorMapTensor (k := k) (he := he)
                (ModuleCat.ofHom (cornerPartMap he f)) (x + y)) =
            f.hom (relativeEvalTensor (k := k) he M (x + y))
          change relativeEvalTensor (k := k) he M'
              (relativeTensorMapTensor (k := k) (he := he)
                (ModuleCat.ofHom (cornerPartMap he f)) x) =
            f.hom (relativeEvalTensor (k := k) he M x) at ihx
          change relativeEvalTensor (k := k) he M'
              (relativeTensorMapTensor (k := k) (he := he)
                (ModuleCat.ofHom (cornerPartMap he f)) y) =
            f.hom (relativeEvalTensor (k := k) he M y) at ihy
          rw [map_add, map_add, ihx, ihy, map_add, map_add]

/-- The multiplication isomorphisms form a natural isomorphism. -/
def relativeEvalNatIso (C : FullnessCertificate e) :
    cornerPartFunctor (k := k) (A := A) he ⋙
        relativeTensorFunctor (k := k) (A := A) he ≅
      Functor.id (ModuleCat.{v} A) :=
  NatIso.ofComponents
    (fun M ↦ (relativeEvalLinearEquiv (k := k) he C M).toModuleIso)
    (fun {M M'} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact relativeEval_naturality (k := k) he f z)

/-- Naturality of the raw counit before restricting to fixed parts. -/
theorem relativeCounitK_naturality {N N' : ModuleCat.{v} B} (f : N ⟶ N')
    (z : relativeTensor (k := k) (he := he) N) :
    relativeCounitK (k := k) he N' (relativeTensorMap he f z) =
      f (relativeCounitK (k := k) he N z) := by
  induction z using Quotient.inductionOn' with
  | _ z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x n =>
          change leftCornerCoefficient (k := k) (he := he) x • f.hom n =
            f.hom (leftCornerCoefficient (k := k) (he := he) x • n)
          rw [map_smul]
      | add x y ihx ihy =>
          change relativeCounitTensor (k := k) (he := he) N'
              (relativeTensorMapTensor (k := k) (he := he) f (x + y)) =
            f.hom (relativeCounitTensor (k := k) (he := he) N (x + y))
          change relativeCounitTensor (k := k) (he := he) N'
              (relativeTensorMapTensor (k := k) (he := he) f x) =
            f.hom (relativeCounitTensor (k := k) (he := he) N x) at ihx
          change relativeCounitTensor (k := k) (he := he) N'
              (relativeTensorMapTensor (k := k) (he := he) f y) =
            f.hom (relativeCounitTensor (k := k) (he := he) N y) at ihy
          rw [map_add, map_add, ihx, ihy, map_add, map_add]

/-- The fixed-part counits form a natural isomorphism. -/
def relativeCounitNatIso :
    relativeTensorFunctor (k := k) (A := A) he ⋙
        cornerPartFunctor (k := k) (A := A) he ≅
      Functor.id (ModuleCat.{v} B) :=
  NatIso.ofComponents
    (fun N ↦ (relativeCounitLinearEquiv (k := k) he N).toModuleIso)
    (fun {N N'} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact relativeCounitK_naturality (k := k) he f z.1)

/-- A fullness certificate gives the Morita equivalence induced by the full
idempotent `e`. -/
def fullIdempotentModuleCatEquivalence (C : FullnessCertificate e) :
    ModuleCat.{v} A ≌ ModuleCat.{v} B :=
  CategoryTheory.Equivalence.mk
    (cornerPartFunctor (k := k) (A := A) he)
    (relativeTensorFunctor (k := k) (A := A) he)
    (relativeEvalNatIso (k := k) he C).symm
    (relativeCounitNatIso (k := k) he)

/-- The Morita equivalence attached to a full idempotent. -/
def fullIdempotentModuleCatEquivalenceOfIsFull (hfull : IsFull e) :
    ModuleCat.{v} A ≌ ModuleCat.{v} B :=
  fullIdempotentModuleCatEquivalence (k := k) he
    (Classical.choice hfull.exists_fullnessCertificate)

/-- The full-idempotent equivalence, packaged as Mathlib's coefficient-linear
Morita equivalence. -/
def fullIdempotentMoritaEquivalence (C : FullnessCertificate e) :
    MoritaEquivalence k A B where
  eqv := fullIdempotentModuleCatEquivalence (k := k) he C
  linear := cornerPartFunctorLinear he

/-- Every full idempotent gives a coefficient-linear Morita equivalence with
its corner algebra. -/
def fullIdempotentMoritaEquivalenceOfIsFull (hfull : IsFull e) :
    MoritaEquivalence k A B :=
  fullIdempotentMoritaEquivalence (k := k) he
    (Classical.choice hfull.exists_fullnessCertificate)

/-- Passing to the fixed part of a module preserves finite-dimensionality. -/
theorem cornerPartObj_moduleFinite (M : ModuleCat.{v} A)
    [Module.Finite k M] :
    Module.Finite k (cornerPartObj (k := k) he M) :=
  (Module.Finite.equiv_iff (cornerPartLinearEquiv (k := k) he M)).mp
    (by infer_instance)

/-- For a full idempotent, a module is finite-dimensional exactly when its
fixed part is finite-dimensional. -/
theorem moduleFinite_cornerPartObj_iff (C : FullnessCertificate e)
    (M : ModuleCat.{v} A) [Module.Finite k A] :
    Module.Finite k M ↔ Module.Finite k (cornerPartObj (k := k) he M) := by
  constructor
  · intro hM
    letI := hM
    exact cornerPartObj_moduleFinite (k := k) he M
  · intro hcorner
    letI := hcorner
    letI : Module.Finite k P := by infer_instance
    letI : Module.Finite k
        (relativeTensor (k := k) (he := he)
          (cornerPartObj (k := k) he M)) :=
      relativeTensor_moduleFinite (k := k) he _
    exact (Module.Finite.equiv_iff
      ((relativeEvalLinearEquiv (k := k) he C M).restrictScalars k)).mp
        (by infer_instance)

end IsIdempotentElem

/-- Representation-finiteness passes from an algebra to a full idempotent
corner. -/
theorem IsRepresentationFinite.of_fullIdempotent
    (hA : IsRepresentationFinite k A) (C : FullnessCertificate e)
    [Module.Finite k A] :
    IsRepresentationFinite k B := by
  let E := IsIdempotentElem.fullIdempotentMoritaEquivalence (k := k) he C
  letI : E.eqv.functor.Linear k := E.linear
  letI : E.eqv.inverse.Linear k := E.eqv.inverseLinear k
  apply IsRepresentationFinite.of_equivalence hA E.eqv
  intro M
  exact IsIdempotentElem.moduleFinite_cornerPartObj_iff (k := k) he C M

/-- Representation-finiteness passes to the corner cut out by any full
idempotent. -/
theorem IsRepresentationFinite.of_isFullIdempotent
    (hA : IsRepresentationFinite k A) (hfull : IsFull e)
    [Module.Finite k A] :
    IsRepresentationFinite k B :=
  IsRepresentationFinite.of_fullIdempotent he hA
    (Classical.choice hfull.exists_fullnessCertificate)

namespace BasicIdempotentData

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [Ring A] [Algebra k A]

/-- The ordinary Cartan matrix of `A` in the ordering selected by a basic
full-corner reduction.  Its entries are computed in the split-basic Morita
representative `D.Corner`. -/
abbrev cartanMatrix [FiniteDimensional k A] (D : BasicIdempotentData k A) :
    Matrix (Fin D.n) (Fin D.n) ℤ :=
  (D.splitBasicIdempotents (k := k) (A := A)).cartanMatrix

omit [IsAlgClosed k] in
/-- The split-basic full corner of a representation-finite algebra is again
representation-finite. -/
theorem representationFinite_corner [FiniteDimensional k A]
    (D : BasicIdempotentData k A) (hA : IsRepresentationFinite k A) :
    IsRepresentationFinite k D.Corner :=
  hA.of_isFullIdempotent (k := k) D.sumIdempotent_isIdempotentElem D.full

end BasicIdempotentData

end MoritaEquivalence

end LargeIndecomposable
