module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalCleavingTransfer

@[expose] public section

/-!
# The BGRS Figure 16 cleaving source

The literal source is the affine `D̃₅` tree with two central vertices and
two leaves at each center.  The one-parameter family below puts `k²` at both
centers, `k` at each leaf, the identity on the central edge, and the four
lines

* `e₀`,
* `e₁`,
* `e₀ + e₁`, and
* `e₀ + c e₁`.

Naturality forces every family morphism to be scalar on both centers, and its
scalar satisfies `c r = d r`.  Thus the family is indecomposable and separates
parameters.  A Hom-bifunctor retraction of an ambient Figure-16 diagram then
contradicts representation-finiteness by the generic cleaving transfer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.CriticalSingularFigure16

open LargeIndecomposable.CriticalSingularCleaving
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u

variable {k : Type u} [Field k]

/-- The six occurrences in the literal Figure-16 source. -/
inductive Vertex
  | upperCenter
  | lowerCenter
  | upperBeta
  | upperGamma
  | lowerBeta
  | lowerGamma
  deriving DecidableEq

def vertexEquiv : Vertex ≃ Fin 6 where
  toFun
    | .upperCenter => 0
    | .lowerCenter => 1
    | .upperBeta => 2
    | .upperGamma => 3
    | .lowerBeta => 4
    | .lowerGamma => 5
  invFun
    | ⟨0, _⟩ => .upperCenter
    | ⟨1, _⟩ => .lowerCenter
    | ⟨2, _⟩ => .upperBeta
    | ⟨3, _⟩ => .upperGamma
    | ⟨4, _⟩ => .lowerBeta
    | ⟨5, _⟩ => .lowerGamma
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Vertex := Fintype.ofEquiv (Fin 6) vertexEquiv.symm

/-- The five arrows in Figure 16. -/
inductive Arrow : Vertex → Vertex → Type
  | tau : Arrow .lowerCenter .upperCenter
  | betaUpper : Arrow .upperBeta .upperCenter
  | gammaUpper : Arrow .upperGamma .upperCenter
  | betaLower : Arrow .lowerBeta .lowerCenter
  | gammaLower : Arrow .lowerGamma .lowerCenter

instance : Quiver Vertex where Hom := Arrow

private theorem arrow_subsingleton (a b : Vertex) :
    Subsingleton (Arrow a b) := by
  constructor
  intro e f
  cases e <;> cases f <;> rfl

abbrev TotalArrow := Σ a, Σ b, Arrow a b

def totalArrow {a b : Vertex} (e : Arrow a b) : TotalArrow :=
  ⟨a, b, e⟩

private theorem totalArrow_source_ne_target (e : TotalArrow) :
    e.1 ≠ e.2.1 := by
  rcases e with ⟨a, b, e⟩
  cases e <;> intro h <;> cases h

private theorem opposite_arrow_source_ne_target
    {a b : Vertexᵒᵖ} (e : a ⟶ b) : a ≠ b := by
  intro hab
  apply totalArrow_source_ne_target (totalArrow e.unop)
  exact (congrArg Opposite.unop hab).symm

private theorem no_arrow_from_upperCenter (b : Vertex) :
    IsEmpty (Arrow .upperCenter b) := by
  constructor
  intro e
  cases e

private theorem opposite_no_arrow_to_upperCenter (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.upperCenter) := by
  constructor
  intro e
  exact (no_arrow_from_upperCenter a.unop).false e.unop

theorem path_length_zero_of_target_upperCenter {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.upperCenter)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_upperCenter _).false e)

private theorem path_subsingleton_of_all_length_zero
    (a b : Vertexᵒᵖ) (hzero : ∀ p : Quiver.Path a b, p.length = 0) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  have hp := p.eq_of_length_zero (hzero p)
  subst b
  rw [Quiver.Path.eq_nil_of_length_zero p (hzero p),
    Quiver.Path.eq_nil_of_length_zero q (hzero q)]

private theorem path_upperCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperCenter)) :=
  path_subsingleton_of_all_length_zero a _
    (fun p ↦ path_length_zero_of_target_upperCenter p)

private theorem arrow_to_lowerCenter_source_eq_upperCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.lowerCenter) :
    b = Opposite.op Vertex.upperCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_upperBeta_source_eq_upperCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperBeta) :
    b = Opposite.op Vertex.upperCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_upperGamma_source_eq_upperCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperGamma) :
    b = Opposite.op Vertex.upperCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_lowerBeta_source_eq_lowerCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.lowerBeta) :
    b = Opposite.op Vertex.lowerCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_lowerGamma_source_eq_lowerCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.lowerGamma) :
    b = Opposite.op Vertex.lowerCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem path_subsingleton_of_unique_predecessor
    (target predecessor : Vertexᵒᵖ)
    (harrow : ∀ {b : Vertexᵒᵖ} (_ : b ⟶ target), b = predecessor)
    (hprevious : ∀ a : Vertexᵒᵖ, Subsingleton (Quiver.Path a predecessor))
    (hback : Quiver.Path target predecessor → False)
    (a : Vertexᵒᵖ) : Subsingleton (Quiver.Path a target) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have he := harrow e
          subst_vars
          exact False.elim (hback q)
  | cons p e =>
      cases q with
      | nil =>
          have he := harrow e
          subst_vars
          exact False.elim (hback p)
      | cons q f =>
          have he := harrow e
          have hf := harrow f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (hprevious a).elim p q

private theorem no_path_lowerCenter_to_upperCenter
    (p : Quiver.Path (Opposite.op Vertex.lowerCenter)
      (Opposite.op Vertex.upperCenter)) : False := by
  have hp := p.eq_of_length_zero (path_length_zero_of_target_upperCenter p)
  cases hp

private theorem no_path_upperBeta_to_upperCenter
    (p : Quiver.Path (Opposite.op Vertex.upperBeta)
      (Opposite.op Vertex.upperCenter)) : False := by
  have hp := p.eq_of_length_zero (path_length_zero_of_target_upperCenter p)
  cases hp

private theorem no_path_upperGamma_to_upperCenter
    (p : Quiver.Path (Opposite.op Vertex.upperGamma)
      (Opposite.op Vertex.upperCenter)) : False := by
  have hp := p.eq_of_length_zero (path_length_zero_of_target_upperCenter p)
  cases hp

private theorem path_lowerCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.lowerCenter)) :=
  path_subsingleton_of_unique_predecessor _ _
    (fun e ↦ arrow_to_lowerCenter_source_eq_upperCenter e)
    path_upperCenter_subsingleton no_path_lowerCenter_to_upperCenter a

private theorem path_upperBeta_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperBeta)) :=
  path_subsingleton_of_unique_predecessor _ _
    (fun e ↦ arrow_to_upperBeta_source_eq_upperCenter e)
    path_upperCenter_subsingleton no_path_upperBeta_to_upperCenter a

private theorem path_upperGamma_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperGamma)) :=
  path_subsingleton_of_unique_predecessor _ _
    (fun e ↦ arrow_to_upperGamma_source_eq_upperCenter e)
    path_upperCenter_subsingleton no_path_upperGamma_to_upperCenter a

private theorem no_path_lowerBeta_to_lowerCenter
    (p : Quiver.Path (Opposite.op Vertex.lowerBeta)
      (Opposite.op Vertex.lowerCenter)) : False := by
  cases p with
  | cons p e =>
      have he := arrow_to_lowerCenter_source_eq_upperCenter e
      subst_vars
      have hp := p.eq_of_length_zero (path_length_zero_of_target_upperCenter p)
      cases hp

private theorem no_path_lowerGamma_to_lowerCenter
    (p : Quiver.Path (Opposite.op Vertex.lowerGamma)
      (Opposite.op Vertex.lowerCenter)) : False := by
  cases p with
  | cons p e =>
      have he := arrow_to_lowerCenter_source_eq_upperCenter e
      subst_vars
      have hp := p.eq_of_length_zero (path_length_zero_of_target_upperCenter p)
      cases hp

private theorem path_lowerBeta_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.lowerBeta)) :=
  path_subsingleton_of_unique_predecessor _ _
    (fun e ↦ arrow_to_lowerBeta_source_eq_lowerCenter e)
    path_lowerCenter_subsingleton no_path_lowerBeta_to_lowerCenter a

private theorem path_lowerGamma_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.lowerGamma)) :=
  path_subsingleton_of_unique_predecessor _ _
    (fun e ↦ arrow_to_lowerGamma_source_eq_lowerCenter e)
    path_lowerCenter_subsingleton no_path_lowerGamma_to_lowerCenter a

/-- The free Figure-16 path category is thin: between any ordered pair of
source occurrences there is at most one directed path. -/
theorem path_subsingleton (a b : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a b) := by
  induction b using Opposite.rec with
  | _ b =>
      cases b with
      | upperCenter => exact path_upperCenter_subsingleton a
      | lowerCenter => exact path_lowerCenter_subsingleton a
      | upperBeta => exact path_upperBeta_subsingleton a
      | upperGamma => exact path_upperGamma_subsingleton a
      | lowerBeta => exact path_lowerBeta_subsingleton a
      | lowerGamma => exact path_lowerGamma_subsingleton a

/-- Free linear Figure-16 source, with the opposite correcting the path
category's reversed convention. -/
abbrev LinearSource (k : Type u) [Field k] :=
  LinearPathCategory.Category k Vertexᵒᵖ

def vertexOppositeEquiv : Vertex ≃ Vertexᵒᵖ where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

instance vertexOppositeFintype : Fintype Vertexᵒᵖ :=
  Fintype.ofEquiv Vertex vertexOppositeEquiv

instance linearSourceFintype : Fintype (LinearSource k) :=
  Fintype.ofEquiv Vertexᵒᵖ (Equiv.refl Vertexᵒᵖ)

def vertexObj (a : Vertex) : LinearSource k :=
  LinearPathCategory.obj k Vertexᵒᵖ (Opposite.op a)

def generatorHom {a b : Vertex} (e : a ⟶ b) :
    vertexObj (k := k) a ⟶ vertexObj (k := k) b :=
  LinearPathCategory.pathHom (Quiver.Hom.toPath (Quiver.Hom.op e))

abbrev Center := ModuleCat.of k (Fin 2 → k)
abbrev Leaf := ModuleCat.of k k

abbrev obj : Vertex → ModuleCat k
  | .upperCenter | .lowerCenter => Center (k := k)
  | .upperBeta | .upperGamma | .lowerBeta | .lowerGamma => Leaf (k := k)

def basisVec (i : Fin 2) : Center (k := k) := Pi.single i 1

@[simp] private theorem basisVec_apply (i j : Fin 2) :
    basisVec (k := k) i j = if i = j then 1 else 0 := by
  simp [basisVec, Pi.single_apply, eq_comm]

def columnHom (a b : k) : Leaf (k := k) ⟶ Center (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then a * x else b * x
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [mul_add]
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }

@[simp] private theorem columnHom_one_zero (x : k) :
    columnHom (k := k) 1 0 x = x • basisVec (k := k) 0 := by
  funext i
  fin_cases i <;> simp [columnHom, basisVec]

@[simp] private theorem columnHom_zero_one (x : k) :
    columnHom (k := k) 0 1 x = x • basisVec (k := k) 1 := by
  funext i
  fin_cases i <;> simp [columnHom, basisVec]

def centerId : Center (k := k) ⟶ Center (k := k) := 𝟙 _

def arrowMap (c : k) {a b : Vertex} :
    (a ⟶ b) → (obj (k := k) a ⟶ obj (k := k) b)
  | .tau => centerId (k := k)
  | .betaUpper => columnHom (k := k) 1 0
  | .gammaUpper => columnHom (k := k) 0 1
  | .betaLower => columnHom (k := k) 1 1
  | .gammaLower => columnHom (k := k) 1 c

/-- Explicit one-parameter representation of the Figure-16 source. -/
def module (c : k) : LinearSource k ⥤ ModuleCat k :=
  LinearPathCategory.lift
    (fun a ↦ obj (k := k) a.unop)
    (fun e ↦ arrowMap (k := k) c e.unop)

instance module_additive (c : k) : (module (k := k) c).Additive := by
  unfold module
  infer_instance

instance module_linear (c : k) : (module (k := k) c).Linear k := by
  unfold module
  infer_instance

@[simp] theorem module_obj (c : k) (a : Vertex) :
    (module (k := k) c).obj (vertexObj (k := k) a) = obj (k := k) a := rfl

@[simp] theorem module_map_generator (c : k) {a b : Vertex} (e : a ⟶ b) :
    (module (k := k) c).map (generatorHom (k := k) e) =
      arrowMap (k := k) c e := by
  unfold module generatorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

def upperComponent {c d : k} (f : module (k := k) c ⟶ module d) :
    Center (k := k) ⟶ Center (k := k) :=
  f.app (vertexObj (k := k) .upperCenter)

def lowerComponent {c d : k} (f : module (k := k) c ⟶ module d) :
    Center (k := k) ⟶ Center (k := k) :=
  f.app (vertexObj (k := k) .lowerCenter)

def leafComponent {c d : k} (f : module (k := k) c ⟶ module d)
    (a : Vertex) : obj (k := k) a ⟶ obj (k := k) a :=
  f.app (vertexObj (k := k) a)

def coeff {c d : k} (f : module (k := k) c ⟶ module d) : k :=
  upperComponent f (basisVec (k := k) 0) 0

private theorem leaf_map_eq_mul (g : Leaf (k := k) ⟶ Leaf (k := k))
    (x : k) : g x = x * g 1 := by
  simpa using g.hom.map_smul x 1

private theorem naturality_tau {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperComponent f = lowerComponent f := by
  have h := f.naturality (generatorHom (k := k) Arrow.tau)
  rw [module_map_generator, module_map_generator] at h
  change centerId (k := k) ≫ upperComponent f =
    lowerComponent f ≫ centerId (k := k) at h
  simpa [centerId] using h

private theorem upper_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperComponent f (basisVec (k := k) 0) =
      coeff f • basisVec (k := k) 0 := by
  have h := f.naturality (generatorHom (k := k) Arrow.betaUpper)
  rw [module_map_generator, module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Center (k := k) ↦ q 1) h
  have hvec : upperComponent f (basisVec (k := k) 0) =
      (leafComponent f .upperBeta 1) • basisVec (k := k) 0 := by
    change upperComponent f (columnHom (k := k) 1 0 1) =
      columnHom (k := k) 1 0 (leafComponent f .upperBeta 1) at h1
    rw [columnHom_one_zero, columnHom_one_zero] at h1
    simpa using h1
  have hc : leafComponent f .upperBeta 1 = coeff f := by
    have h0 := congrArg (fun x : Center (k := k) ↦ x 0) hvec
    simpa [coeff, basisVec, Pi.single_apply] using h0.symm
  simpa [hc] using hvec

private theorem upper_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperComponent f (basisVec (k := k) 1) =
      coeff f • basisVec (k := k) 1 := by
  let q : k := leafComponent f .upperGamma 1
  have hu := f.naturality (generatorHom (k := k) Arrow.gammaUpper)
  rw [module_map_generator, module_map_generator] at hu
  have hu1 := congrArg
    (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) hu
  have hupper : upperComponent f (basisVec (k := k) 1) =
      q • basisVec (k := k) 1 := by
    change upperComponent f (columnHom (k := k) 0 1 1) =
      columnHom (k := k) 0 1 (leafComponent f .upperGamma 1) at hu1
    rw [columnHom_zero_one, columnHom_zero_one] at hu1
    simpa [q] using hu1
  let r : k := leafComponent f .lowerBeta 1
  have hl := f.naturality (generatorHom (k := k) Arrow.betaLower)
  rw [module_map_generator, module_map_generator] at hl
  have hl1 := congrArg
    (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) hl
  have hline : lowerComponent f (columnHom (k := k) 1 1 1) =
      columnHom (k := k) 1 1 r := by
    change lowerComponent f (columnHom (k := k) 1 1 1) =
      columnHom (k := k) 1 1 (leafComponent f .lowerBeta 1) at hl1
    simpa [r] using hl1
  rw [← naturality_tau f] at hline
  have hzero := congrArg (fun x : Center (k := k) ↦ x 0) hline
  have hone := congrArg (fun x : Center (k := k) ↦ x 1) hline
  have hr : r = coeff f := by
    rw [show columnHom (k := k) 1 1 1 =
        basisVec (k := k) 0 + basisVec (k := k) 1 by
      funext i
      fin_cases i <;> simp [columnHom, basisVec],
      map_add, upper_basis_zero, hupper] at hzero
    simpa [columnHom, basisVec, Pi.single_apply] using hzero.symm
  have hq : q = coeff f := by
    rw [show columnHom (k := k) 1 1 1 =
        basisVec (k := k) 0 + basisVec (k := k) 1 by
      funext i
      fin_cases i <;> simp [columnHom, basisVec],
      map_add, upper_basis_zero, hupper, hr] at hone
    simpa [columnHom, basisVec, Pi.single_apply] using hone
  simpa [hq] using hupper

private theorem upper_central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Center (k := k)) :
    upperComponent f x = coeff f • x := by
  have hx : x = x 0 • basisVec (k := k) 0 +
      x 1 • basisVec (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  rw [hx, map_add, map_smul, map_smul, upper_basis_zero, upper_basis_one]
  module

/-- Every family morphism is scalar on both centers, and its scalar
intertwines the parameters. -/
theorem hom_central_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) :
    (∀ x : Center (k := k), upperComponent f x = coeff f • x) ∧
    (∀ x : Center (k := k), lowerComponent f x = coeff f • x) ∧
    c * coeff f = d * coeff f := by
  have hu (x : Center (k := k)) := upper_central_scalar f x
  have hl (x : Center (k := k)) :
      lowerComponent f x = coeff f • x := by
    rw [← naturality_tau f]
    exact hu x
  have h := f.naturality (generatorHom (k := k) Arrow.gammaLower)
  rw [module_map_generator, module_map_generator] at h
  have h1 := congrArg
    (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
  change lowerComponent f (columnHom (k := k) 1 c 1) =
    columnHom (k := k) 1 d (leafComponent f .lowerGamma 1) at h1
  have hzero := congrArg (fun x : Center (k := k) ↦ x 0) h1
  have hone := congrArg (fun x : Center (k := k) ↦ x 1) h1
  rw [hl] at hzero hone
  have hs : leafComponent f .lowerGamma 1 = coeff f := by
    simpa [columnHom] using hzero.symm
  rw [hs] at hone
  have hcd : c * coeff f = d * coeff f := by
    simpa [columnHom, mul_comm] using hone
  exact ⟨hu, hl, hcd⟩

theorem parameter_eq_of_iso {c d : k}
    (e : module (k := k) c ≅ module d) : c = d := by
  have h := (hom_central_scalar e.hom).2.2
  have hcoeff : coeff e.hom ≠ 0 := by
    intro hz
    have hu := (hom_central_scalar e.hom).1 (basisVec (k := k) 0)
    rw [hz, zero_smul] at hu
    have hinv := congrArg
      (fun g : module (k := k) c ⟶ module c ↦
        g.app (vertexObj (k := k) .upperCenter)
          (basisVec (k := k) 0)) e.hom_inv_id
    change upperComponent e.inv
      (upperComponent e.hom (basisVec (k := k) 0)) =
        basisVec (k := k) 0 at hinv
    rw [hu, map_zero] at hinv
    have hcoord := congrArg (fun x : Center (k := k) ↦ x 0) hinv
    change (0 : k) = 1 at hcoord
    exact zero_ne_one hcoord
  exact mul_right_cancel₀ hcoeff h

private theorem component_scalar {c : k}
    (f : module (k := k) c ⟶ module c) (a : Vertex)
    (x : obj (k := k) a) :
    leafComponent f a x = coeff f • x := by
  cases a with
  | upperCenter => exact (hom_central_scalar f).1 x
  | lowerCenter => exact (hom_central_scalar f).2.1 x
  | upperBeta =>
      have h := f.naturality (generatorHom (k := k) Arrow.betaUpper)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .upperBeta 1 = coeff f := by
        change upperComponent f (columnHom (k := k) 1 0 1) =
          columnHom (k := k) 1 0 (leafComponent f .upperBeta 1) at h1
        have h0 := congrArg (fun y : Center (k := k) ↦ y 0) h1
        rw [(hom_central_scalar f).1] at h0
        simpa [columnHom] using h0.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | upperGamma =>
      have h := f.naturality (generatorHom (k := k) Arrow.gammaUpper)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .upperGamma 1 = coeff f := by
        change upperComponent f (columnHom (k := k) 0 1 1) =
          columnHom (k := k) 0 1 (leafComponent f .upperGamma 1) at h1
        have hcoord := congrArg (fun y : Center (k := k) ↦ y 1) h1
        rw [(hom_central_scalar f).1] at hcoord
        simpa [columnHom] using hcoord.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | lowerBeta =>
      have h := f.naturality (generatorHom (k := k) Arrow.betaLower)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .lowerBeta 1 = coeff f := by
        change lowerComponent f (columnHom (k := k) 1 1 1) =
          columnHom (k := k) 1 1 (leafComponent f .lowerBeta 1) at h1
        have hcoord := congrArg (fun y : Center (k := k) ↦ y 0) h1
        rw [(hom_central_scalar f).2.1] at hcoord
        simpa [columnHom] using hcoord.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _
  | lowerGamma =>
      have h := f.naturality (generatorHom (k := k) Arrow.gammaLower)
      simp only [module_map_generator] at h
      have h1 := congrArg
        (fun g : Leaf (k := k) ⟶ Center (k := k) ↦ g 1) h
      have hone : leafComponent f .lowerGamma 1 = coeff f := by
        change lowerComponent f (columnHom (k := k) 1 c 1) =
          columnHom (k := k) 1 c (leafComponent f .lowerGamma 1) at h1
        have hcoord := congrArg (fun y : Center (k := k) ↦ y 0) h1
        rw [(hom_central_scalar f).2.1] at hcoord
        simpa [columnHom] using hcoord.symm
      rw [leaf_map_eq_mul, hone]
      exact mul_comm _ _

theorem end_eq_zero_or_id_of_idempotent (c : k)
    (f : module (k := k) c ⟶ module c) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  have hc := congrArg coeff hf
  have hmul : coeff f * coeff f = coeff f := by
    change upperComponent (f ≫ f) (basisVec (k := k) 0) 0 = coeff f at hc
    change upperComponent f (upperComponent f (basisVec (k := k) 0)) 0 =
      coeff f at hc
    rw [(hom_central_scalar f).1, (hom_central_scalar f).1] at hc
    simpa [smul_smul] using hc
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using hmul) with h0 | h1
  · left
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change leafComponent f (LinearPathCategory.vertex X).unop x = 0
    rw [component_scalar, h0, zero_smul]
  · right
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change leafComponent f (LinearPathCategory.vertex X).unop x = x
    rw [component_scalar, h1, one_smul]

theorem module_not_isZero (c : k) : ¬ IsZero (module (k := k) c) := by
  intro hzero
  have hid : (𝟙 (module (k := k) c) : module c ⟶ module c) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have h := congrArg
    (fun f : module (k := k) c ⟶ module c ↦
      f.app (vertexObj (k := k) .upperCenter)
        (basisVec (k := k) 0) 0) hid
  change (1 : k) = 0 at h
  exact one_ne_zero h

theorem module_indecomposable (c : k) : Indecomposable (module (k := k) c) := by
  refine ⟨module_not_isZero c, ?_⟩
  intro Y Z e
  let p : module (k := k) c ⟶ module c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p, Category.assoc]
  rcases end_eq_zero_or_id_of_idempotent c p hp with hp0 | hp1
  · left
    apply (IsZero.iff_id_eq_zero Y).mpr
    calc
      𝟙 Y = (biprod.inl ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.fst) := by
        dsimp [p]
        simp
      _ = 0 := by rw [hp0]; simp
  · right
    apply (IsZero.iff_id_eq_zero Z).mpr
    calc
      𝟙 Z = (biprod.inr ≫ e.inv) ≫ p ≫ (e.hom ≫ biprod.snd) := by
        rw [hp1]
        simp
      _ = 0 := by dsimp [p]; simp

instance module_obj_finite (c : k) (X : LinearSource k) :
    Module.Finite k ((module (k := k) c).obj X) := by
  change Module.Finite k (obj (k := k) (LinearPathCategory.vertex X).unop)
  unfold obj Center Leaf
  cases (LinearPathCategory.vertex X).unop <;> infer_instance

theorem module_end_isLocalRing (c : k) :
    IsLocalRing (CategoryTheory.End (module (k := k) c)) :=
  LargeIndecomposable.ClosedZigzagTransfer.functor_end_isLocalRing
    (module (k := k) c) (fun X ↦ module_obj_finite c X)
      (module_indecomposable c)

section Infinite

variable [Infinite k]

def family (n : ℕ) : LinearSource k ⥤ ModuleCat k :=
  module (Infinite.natEmbedding k n)

instance family_additive (n : ℕ) : (family (k := k) n).Additive := by
  unfold family
  infer_instance

instance family_linear (n : ℕ) : (family (k := k) n).Linear k := by
  unfold family
  infer_instance

theorem family_obj_finite (n : ℕ) (X : LinearSource k) :
    Module.Finite k ((family (k := k) n).obj X) := by
  unfold family
  infer_instance

theorem family_indecomposable (n : ℕ) :
    Indecomposable (family (k := k) n) := module_indecomposable _

theorem family_eq_of_iso {m n : ℕ}
    (e : family (k := k) m ≅ family n) : m = n := by
  apply (Infinite.natEmbedding k).injective
  exact parameter_eq_of_iso e

theorem family_end_isLocalRing (n : ℕ) :
    IsLocalRing (CategoryTheory.End (family (k := k) n)) := by
  unfold family
  exact module_end_isLocalRing _

/-- The explicit infinite indecomposable family on the Figure-16 source. -/
def sourceFamily : CleavingSourceFamily (k := k) (LinearSource k) where
  anchor := vertexObj (k := k) .upperCenter
  module := family (k := k)
  additive := fun _ ↦ inferInstance
  linear := fun _ ↦ inferInstance
  obj_finite := family_obj_finite
  indecomposable := family_indecomposable
  eq_of_iso := fun h ↦ family_eq_of_iso (Classical.choice h)
  end_isLocalRing := family_end_isLocalRing

end Infinite

section Diagram

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- Literal ambient realization of Figure 16. -/
structure DiagramData where
  object : Vertex → C
  arrow : ∀ {a b : Vertex}, (a ⟶ b) → (object a ⟶ object b)

/-- The three-object realization underlying Figure 16: both centers are
`M`, the two beta leaves are `B`, and the two gamma leaves are `H`. -/
def repeatedObjectDiagram
    {M B H : C} (tau : End M) (beta : B ⟶ M) (gamma : H ⟶ M) :
    DiagramData (C := C) where
  object
    | .upperCenter | .lowerCenter => M
    | .upperBeta | .lowerBeta => B
    | .upperGamma | .lowerGamma => H
  arrow
    | .tau => tau.asHom
    | .betaUpper | .betaLower => beta
    | .gammaUpper | .gammaLower => gamma

namespace DiagramData

def functor (G : DiagramData (C := C)) : LinearSource k ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ G.object a.unop)
    (fun e ↦ G.arrow e.unop)

instance functor_additive (G : DiagramData (C := C)) :
    (G.functor (k := k)).Additive := by
  unfold functor
  infer_instance

instance functor_linear (G : DiagramData (C := C)) :
    (G.functor (k := k)).Linear k := by
  unfold functor
  infer_instance

@[simp] theorem functor_obj (G : DiagramData (C := C)) (a : Vertex) :
    (G.functor (k := k)).obj (vertexObj (k := k) a) = G.object a := rfl

@[simp] theorem functor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.functor (k := k)).map (generatorHom (k := k) e) = G.arrow e := by
  unfold functor generatorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

end DiagramData

end Diagram

section AmbientContradiction

universe uA x

variable [Infinite k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- A cleaving realization of the literal Figure-16 source contradicts
representation-finiteness of the ambient algebra. -/
theorem not_isRepresentationFinite_of_figure16Data
    (G : DiagramData (C := S.ProjectiveCategory))
    (hG : HomBifunctorRetraction (k := k) (G.functor (k := k))) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A :=
  CriticalSingularCleaving.not_isRepresentationFinite_of_homBifunctorRetraction
    (S := S) (D := G.functor (k := k)) (sourceFamily (k := k)) hG

end AmbientContradiction

end LargeIndecomposable.CriticalSingularFigure16
