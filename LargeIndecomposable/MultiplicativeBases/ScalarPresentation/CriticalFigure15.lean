module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalCleavingTransfer
public import LargeIndecomposable.Foundations.CategoryTheory.MorphismIdeal
public import LargeIndecomposable.Foundations.PathCategories.LinearPathCategory
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import LargeIndecomposable.Foundations.CategoryTheory.LinearIdealQuotientLift

@[expose] public section

/-!
# The BGRS Figure 15 bound cleaving diagram

This file encodes the literal eight-vertex diagram of BGRS Figure 15.  Its
source is the free linear category modulo the single displayed relation
`alphaLeft ≫ delta ≫ alphaRight = 0`.

The explicit family has dimension vector `(1,3,3,1,2,1,2,1)`.  On the two
three-dimensional central vertices the middle matrix is

```
  [1  1  0]
  [0  1  1]
  [1  c  1].
```

The forbidden matrix entry is zero, so the bound relation holds.  The flag
maps on the two sides force a morphism between parameters `c,d` to have one
scalar coefficient `r`; the remaining middle-arrow equation is
`c*r = d*r`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace LargeIndecomposable.CriticalSingularFigure15

open LargeIndecomposable.CriticalSingularCleaving
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u

variable {k : Type u} [Field k]

/-- The eight occurrences in Figure 15. -/
inductive Vertex
  | leftEndpoint
  | leftCenter
  | rightCenter
  | rightEndpoint
  | upperCenter
  | upperEndpoint
  | lowerCenter
  | lowerEndpoint
  deriving DecidableEq

def vertexEquiv : Vertex ≃ Fin 8 where
  toFun
    | .leftEndpoint => 0
    | .leftCenter => 1
    | .rightCenter => 2
    | .rightEndpoint => 3
    | .upperCenter => 4
    | .upperEndpoint => 5
    | .lowerCenter => 6
    | .lowerEndpoint => 7
  invFun
    | ⟨0, _⟩ => .leftEndpoint
    | ⟨1, _⟩ => .leftCenter
    | ⟨2, _⟩ => .rightCenter
    | ⟨3, _⟩ => .rightEndpoint
    | ⟨4, _⟩ => .upperCenter
    | ⟨5, _⟩ => .upperEndpoint
    | ⟨6, _⟩ => .lowerCenter
    | ⟨7, _⟩ => .lowerEndpoint
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Vertex := Fintype.ofEquiv (Fin 8) vertexEquiv.symm

/-- The seven arrows of Figure 15. -/
inductive Arrow : Vertex → Vertex → Type
  | alphaLeft : Arrow .leftEndpoint .leftCenter
  | delta : Arrow .leftCenter .rightCenter
  | alphaRight : Arrow .rightCenter .rightEndpoint
  | rho : Arrow .upperCenter .rightCenter
  | alphaUpper : Arrow .upperCenter .upperEndpoint
  | sigma : Arrow .leftCenter .lowerCenter
  | alphaLower : Arrow .lowerEndpoint .lowerCenter

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

private theorem no_arrow_from_rightEndpoint (b : Vertex) :
    IsEmpty (Arrow .rightEndpoint b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_from_upperEndpoint (b : Vertex) :
    IsEmpty (Arrow .upperEndpoint b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_from_lowerCenter (b : Vertex) :
    IsEmpty (Arrow .lowerCenter b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_leftEndpoint (a : Vertex) :
    IsEmpty (Arrow a .leftEndpoint) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_upperCenter (a : Vertex) :
    IsEmpty (Arrow a .upperCenter) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_lowerEndpoint (a : Vertex) :
    IsEmpty (Arrow a .lowerEndpoint) := by
  constructor
  intro e
  cases e

private theorem opposite_no_arrow_to_rightEndpoint (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.rightEndpoint) := by
  constructor
  intro e
  exact (no_arrow_from_rightEndpoint a.unop).false e.unop

private theorem opposite_no_arrow_to_upperEndpoint (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.upperEndpoint) := by
  constructor
  intro e
  exact (no_arrow_from_upperEndpoint a.unop).false e.unop

private theorem opposite_no_arrow_to_lowerCenter (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.lowerCenter) := by
  constructor
  intro e
  exact (no_arrow_from_lowerCenter a.unop).false e.unop

private theorem opposite_no_arrow_from_leftEndpoint (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.leftEndpoint ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_leftEndpoint b.unop).false e.unop

private theorem opposite_no_arrow_from_upperCenter (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.upperCenter ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_upperCenter b.unop).false e.unop

private theorem opposite_no_arrow_from_lowerEndpoint (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.lowerEndpoint ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_lowerEndpoint b.unop).false e.unop

theorem path_length_zero_of_target_rightEndpoint {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.rightEndpoint)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_rightEndpoint _).false e)

theorem path_length_zero_of_target_upperEndpoint {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.upperEndpoint)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_upperEndpoint _).false e)

theorem path_length_zero_of_target_lowerCenter {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.lowerCenter)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e =>
      exact False.elim ((opposite_no_arrow_to_lowerCenter _).false e)

theorem path_length_zero_of_source_leftEndpoint {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.leftEndpoint) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_leftEndpoint _).false e)

theorem path_length_zero_of_source_upperCenter {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.upperCenter) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_upperCenter _).false e)

theorem path_length_zero_of_source_lowerEndpoint {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.lowerEndpoint) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_lowerEndpoint _).false e)

private theorem arrow_to_rightCenter_source_eq_rightEndpoint
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.rightCenter) :
    b = Opposite.op Vertex.rightEndpoint := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_leftCenter_source
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftCenter) :
    b = Opposite.op Vertex.rightCenter ∨
      b = Opposite.op Vertex.lowerCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | delta => exact Or.inl rfl
      | sigma => exact Or.inr rfl

private theorem arrow_to_leftEndpoint_source_eq_leftCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftEndpoint) :
    b = Opposite.op Vertex.leftCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_upperCenter_source
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperCenter) :
    b = Opposite.op Vertex.rightCenter ∨
      b = Opposite.op Vertex.upperEndpoint := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | rho => exact Or.inl rfl
      | alphaUpper => exact Or.inr rfl

private theorem arrow_to_lowerEndpoint_source_eq_lowerCenter
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.lowerEndpoint) :
    b = Opposite.op Vertex.lowerCenter := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem path_length_zero_before_arrow_to_rightCenter
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b)
    (e : b ⟶ Opposite.op Vertex.rightCenter) : p.length = 0 := by
  have hb := arrow_to_rightCenter_source_eq_rightEndpoint e
  subst b
  exact path_length_zero_of_target_rightEndpoint p

private theorem path_subsingleton_of_all_length_zero
    (a b : Vertexᵒᵖ) (hzero : ∀ p : Quiver.Path a b, p.length = 0) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  have hp := p.eq_of_length_zero (hzero p)
  subst b
  rw [Quiver.Path.eq_nil_of_length_zero p (hzero p),
    Quiver.Path.eq_nil_of_length_zero q (hzero q)]

private theorem path_rightCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.rightCenter)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_before_arrow_to_rightCenter q e
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_before_arrow_to_rightCenter p e
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have hp0 := path_length_zero_before_arrow_to_rightCenter p e
          have hq0 := path_length_zero_before_arrow_to_rightCenter q f
          have hbc := (p.eq_of_length_zero hp0).symm.trans
            (q.eq_of_length_zero hq0)
          cases hbc
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          have hpa := p.eq_of_length_zero hp0
          subst_vars
          rw [Quiver.Path.eq_nil_of_length_zero p hp0,
            Quiver.Path.eq_nil_of_length_zero q hq0]

private theorem no_path_leftCenter_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.leftCenter)
      (Opposite.op Vertex.rightCenter)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_rightCenter p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Arrow .rightCenter .leftCenter) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

private theorem no_path_lowerCenter_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.lowerCenter)
      (Opposite.op Vertex.rightCenter)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_rightCenter p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Arrow .rightCenter .lowerCenter) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

private theorem no_path_leftCenter_to_lowerCenter
    (p : Quiver.Path (Opposite.op Vertex.leftCenter)
      (Opposite.op Vertex.lowerCenter)) : False := by
  have hp0 := path_length_zero_of_target_lowerCenter p
  have h := p.eq_of_length_zero hp0
  cases h

private theorem path_leftCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftCenter)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          rcases arrow_to_leftCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_leftCenter_to_rightCenter q)
          · subst_vars
            exact False.elim (no_path_leftCenter_to_lowerCenter q)
  | cons p e =>
      cases q with
      | nil =>
          rcases arrow_to_leftCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_leftCenter_to_rightCenter p)
          · subst_vars
            exact False.elim (no_path_leftCenter_to_lowerCenter p)
      | cons q f =>
          rcases arrow_to_leftCenter_source e with he | he <;>
            rcases arrow_to_leftCenter_source f with hf | hf
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_rightCenter_subsingleton a).elim p q
          · subst_vars
            have hq0 := path_length_zero_of_target_lowerCenter q
            have ha := q.eq_of_length_zero hq0
            subst a
            exact False.elim (no_path_lowerCenter_to_rightCenter p)
          · subst_vars
            have hp0 := path_length_zero_of_target_lowerCenter p
            have ha := p.eq_of_length_zero hp0
            subst a
            exact False.elim (no_path_lowerCenter_to_rightCenter q)
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_subsingleton_of_all_length_zero a _
              (fun r ↦ path_length_zero_of_target_lowerCenter r)).elim p q

private theorem path_leftEndpoint_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftEndpoint)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_leftEndpoint q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_leftEndpoint p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_leftEndpoint_source_eq_leftCenter e
          have hf := arrow_to_leftEndpoint_source_eq_leftCenter f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_leftCenter_subsingleton a).elim p q

private theorem no_path_upperCenter_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.upperCenter)
      (Opposite.op Vertex.rightCenter)) : False := by
  have hp0 := path_length_zero_of_source_upperCenter p
  have h := p.eq_of_length_zero hp0
  cases h

private theorem no_path_upperEndpoint_to_rightCenter
    (p : Quiver.Path (Opposite.op Vertex.upperEndpoint)
      (Opposite.op Vertex.rightCenter)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_rightCenter p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Arrow .rightCenter .upperEndpoint) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

private theorem no_path_upperCenter_to_upperEndpoint
    (p : Quiver.Path (Opposite.op Vertex.upperCenter)
      (Opposite.op Vertex.upperEndpoint)) : False := by
  have hp0 := path_length_zero_of_target_upperEndpoint p
  have h := p.eq_of_length_zero hp0
  cases h

private theorem path_upperCenter_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperCenter)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          rcases arrow_to_upperCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_upperCenter_to_rightCenter q)
          · subst_vars
            exact False.elim (no_path_upperCenter_to_upperEndpoint q)
  | cons p e =>
      cases q with
      | nil =>
          rcases arrow_to_upperCenter_source e with he | he
          · subst_vars
            exact False.elim (no_path_upperCenter_to_rightCenter p)
          · subst_vars
            exact False.elim (no_path_upperCenter_to_upperEndpoint p)
      | cons q f =>
          rcases arrow_to_upperCenter_source e with he | he <;>
            rcases arrow_to_upperCenter_source f with hf | hf
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_rightCenter_subsingleton a).elim p q
          · subst_vars
            have hq0 := path_length_zero_of_target_upperEndpoint q
            have ha := q.eq_of_length_zero hq0
            subst a
            exact False.elim (no_path_upperEndpoint_to_rightCenter p)
          · subst_vars
            have hp0 := path_length_zero_of_target_upperEndpoint p
            have ha := p.eq_of_length_zero hp0
            subst a
            exact False.elim (no_path_upperEndpoint_to_rightCenter q)
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_subsingleton_of_all_length_zero a _
              (fun r ↦ path_length_zero_of_target_upperEndpoint r)).elim p q

private theorem path_lowerEndpoint_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.lowerEndpoint)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_lowerEndpoint q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_lowerEndpoint p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_lowerEndpoint_source_eq_lowerCenter e
          have hf := arrow_to_lowerEndpoint_source_eq_lowerCenter f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_subsingleton_of_all_length_zero a _
            (fun r ↦ path_length_zero_of_target_lowerCenter r)).elim p q

/-- The free Figure-15 quiver is thin: between any ordered pair of source
occurrences there is at most one directed path. -/
theorem path_subsingleton (a b : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a b) := by
  induction b using Opposite.rec with
  | _ b =>
      cases b with
      | leftEndpoint => exact path_leftEndpoint_subsingleton a
      | leftCenter => exact path_leftCenter_subsingleton a
      | rightCenter => exact path_rightCenter_subsingleton a
      | rightEndpoint =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_rightEndpoint p)
      | upperCenter => exact path_upperCenter_subsingleton a
      | upperEndpoint =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_upperEndpoint p)
      | lowerCenter =>
          exact path_subsingleton_of_all_length_zero a _
            (fun p ↦ path_length_zero_of_target_lowerCenter p)
      | lowerEndpoint => exact path_lowerEndpoint_subsingleton a

abbrev FreeLinearSource (k : Type u) [Field k] :=
  LinearPathCategory.Category k Vertexᵒᵖ

def vertexOppositeEquiv : Vertex ≃ Vertexᵒᵖ where
  toFun := Opposite.op
  invFun := Opposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

instance vertexOppositeFintype : Fintype Vertexᵒᵖ :=
  Fintype.ofEquiv Vertex vertexOppositeEquiv

instance freeLinearSourceFintype : Fintype (FreeLinearSource k) :=
  Fintype.ofEquiv Vertexᵒᵖ (Equiv.refl Vertexᵒᵖ)

def freeVertexObj (a : Vertex) : FreeLinearSource k :=
  LinearPathCategory.obj k Vertexᵒᵖ (Opposite.op a)

def freeGeneratorHom {a b : Vertex} (e : a ⟶ b) :
    freeVertexObj (k := k) a ⟶ freeVertexObj (k := k) b :=
  LinearPathCategory.pathHom (Quiver.Hom.toPath (Quiver.Hom.op e))

/-- The length-three composite printed as zero next to Figure 15. -/
def mainComposite :
    freeVertexObj (k := k) .leftEndpoint ⟶
      freeVertexObj (k := k) .rightEndpoint :=
  freeGeneratorHom (k := k) Arrow.alphaLeft ≫
    freeGeneratorHom (k := k) Arrow.delta ≫
      freeGeneratorHom (k := k) Arrow.alphaRight

/-- A transport-stable singleton presentation of the displayed relation. -/
def relation (X Y : FreeLinearSource k) : Set (X ⟶ Y) :=
  {f | ∃ (hX : X = freeVertexObj (k := k) .leftEndpoint)
      (hY : Y = freeVertexObj (k := k) .rightEndpoint),
    f = eqToHom hX ≫ mainComposite (k := k) ≫ eqToHom hY.symm}

abbrev relationIdeal : MorphismIdeal (FreeLinearSource k) :=
  MorphismIdeal.linearSpan k (relation (k := k))

/-- The bound linear source of Figure 15. -/
abbrev LinearSource := CategoryTheory.Quotient (relationIdeal (k := k)).rel

abbrev quotientFunctor : FreeLinearSource k ⥤ LinearSource (k := k) :=
  CategoryTheory.Quotient.functor (relationIdeal (k := k)).rel

instance linearSourcePreadditive : Preadditive (LinearSource (k := k)) :=
  (relationIdeal (k := k)).quotientPreadditive

instance quotientFunctorAdditive : (quotientFunctor (k := k)).Additive :=
  CategoryTheory.Quotient.functor_additive
    (relationIdeal (k := k)).rel
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
      (relationIdeal (k := k)).add_compatible f₁ f₂ g₁ g₂ hf hg)

instance linearSourceLinear : Linear k (LinearSource (k := k)) :=
  (relationIdeal (k := k)).quotientLinear

instance quotientFunctorLinear : (quotientFunctor (k := k)).Linear k :=
  (relationIdeal (k := k)).quotientFunctorLinear

instance linearSourceFintype : Fintype (LinearSource (k := k)) :=
  Fintype.ofEquiv (FreeLinearSource k)
    (CategoryTheory.Quotient.equiv (relationIdeal (k := k)).rel).symm

abbrev vertexObj (a : Vertex) : LinearSource (k := k) :=
  (quotientFunctor (k := k)).obj (freeVertexObj (k := k) a)

abbrev generatorHom {a b : Vertex} (e : a ⟶ b) :
    vertexObj (k := k) a ⟶ vertexObj (k := k) b :=
  (quotientFunctor (k := k)).map (freeGeneratorHom (k := k) e)

theorem mainComposite_zero :
    (quotientFunctor (k := k)).map (mainComposite (k := k)) = 0 := by
  rw [(relationIdeal (k := k)).map_eq_zero_iff]
  apply MorphismIdeal.relation_mem_linearSpan (relation (k := k))
  exact ⟨rfl, rfl, by simp⟩

section QuotientLift

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (F : FreeLinearSource k ⥤ C) [F.Additive] [F.Linear k]

theorem relationIdeal_isKilledBy
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (relationIdeal (k := k)).IsKilledBy F := by
  apply MorphismIdeal.linearSpan_le (relation (k := k))
    (MorphismIdeal.functorKernel (k := k) F)
  intro X Y r hr
  rw [MorphismIdeal.mem_functorKernel_iff]
  rcases hr with ⟨hX, hY, rfl⟩
  subst X
  subst Y
  simp only [F.map_comp]
  rw [hmain]
  simp

/-- Descend a free diagram which kills the displayed composite. -/
def quotientLift
    (hmain : F.map (mainComposite (k := k)) = 0) :
    LinearSource (k := k) ⥤ C :=
  (relationIdeal (k := k)).quotientLift F
    (relationIdeal_isKilledBy F hmain)

instance quotientLift_additive
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (quotientLift F hmain).Additive := by
  unfold quotientLift
  infer_instance

instance quotientLift_linear
    (hmain : F.map (mainComposite (k := k)) = 0) :
    (quotientLift F hmain).Linear k := by
  unfold quotientLift
  infer_instance

@[simp] theorem quotientLift_map_quotient
    (hmain : F.map (mainComposite (k := k)) = 0)
    {X Y : FreeLinearSource k} (f : X ⟶ Y) :
    (quotientLift F hmain).map ((quotientFunctor (k := k)).map f) = F.map f :=
  rfl

end QuotientLift

abbrev Central := ModuleCat.of k (Fin 3 → k)
abbrev Branch := ModuleCat.of k (Fin 2 → k)
abbrev Leaf := ModuleCat.of k k

abbrev obj : Vertex → ModuleCat k
  | .leftCenter | .rightCenter => Central (k := k)
  | .upperCenter | .lowerCenter => Branch (k := k)
  | .leftEndpoint | .rightEndpoint | .upperEndpoint | .lowerEndpoint =>
      Leaf (k := k)

def basis3 (i : Fin 3) : Central (k := k) := Pi.single i 1
def basis2 (i : Fin 2) : Branch (k := k) := Pi.single i 1

@[simp] private theorem basis3_apply (i j : Fin 3) :
    basis3 (k := k) i j = if i = j then 1 else 0 := by
  simp [basis3, Pi.single_apply, eq_comm]

@[simp] private theorem basis2_apply (i j : Fin 2) :
    basis2 (k := k) i j = if i = j then 1 else 0 := by
  simp [basis2, Pi.single_apply, eq_comm]

def alphaLeftMap : Leaf (k := k) ⟶ Central (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then x else 0
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def deltaMap (c : k) : Central (k := k) ⟶ Central (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦
        if i = 0 then x 0 + x 1
        else if i = 1 then x 1 + x 2
        else x 0 + c * x 1 + x 2
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp [mul_add] <;> abel
      map_smul' := by
        intro a x
        funext i
        fin_cases i <;> simp <;> ring }

def alphaRightMap : Central (k := k) ⟶ Leaf (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ x 1
      map_add' := by intros; simp
      map_smul' := by intros; simp }

def rhoMap : Branch (k := k) ⟶ Central (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then x 0 else if i = 1 then x 1 else 0
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def alphaUpperMap : Branch (k := k) ⟶ Leaf (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ x 0
      map_add' := by intros; simp
      map_smul' := by intros; simp }

def sigmaMap : Central (k := k) ⟶ Branch (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then x 0 else x 1
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def alphaLowerMap : Leaf (k := k) ⟶ Branch (k := k) :=
  ModuleCat.ofHom
    { toFun := fun x i ↦ if i = 0 then 0 else x
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro c x; funext i; fin_cases i <;> simp }

def arrowMap (c : k) {a b : Vertex} :
    (a ⟶ b) → (obj (k := k) a ⟶ obj (k := k) b)
  | .alphaLeft => alphaLeftMap (k := k)
  | .delta => deltaMap (k := k) c
  | .alphaRight => alphaRightMap (k := k)
  | .rho => rhoMap (k := k)
  | .alphaUpper => alphaUpperMap (k := k)
  | .sigma => sigmaMap (k := k)
  | .alphaLower => alphaLowerMap (k := k)

def freeModule (c : k) : FreeLinearSource k ⥤ ModuleCat k :=
  LinearPathCategory.lift
    (fun a ↦ obj (k := k) a.unop)
    (fun e ↦ arrowMap (k := k) c e.unop)

instance freeModule_additive (c : k) : (freeModule (k := k) c).Additive := by
  unfold freeModule
  infer_instance

instance freeModule_linear (c : k) : (freeModule (k := k) c).Linear k := by
  unfold freeModule
  infer_instance

@[simp] private theorem freeModule_map_generator (c : k)
    {a b : Vertex} (e : a ⟶ b) :
    (freeModule (k := k) c).map (freeGeneratorHom (k := k) e) =
      arrowMap (k := k) c e := by
  unfold freeModule freeGeneratorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

theorem freeModule_mainComposite_zero (c : k) :
    (freeModule (k := k) c).map (mainComposite (k := k)) = 0 := by
  unfold mainComposite
  rw [Functor.map_comp, Functor.map_comp]
  simp only [freeModule_map_generator]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change alphaRightMap (k := k)
      (deltaMap (k := k) c (alphaLeftMap (k := k) x)) = 0
  simp [alphaLeftMap, deltaMap, alphaRightMap]

/-- The explicit Figure-15 module of parameter `c`, descended through the
displayed zero relation. -/
def module (c : k) : LinearSource (k := k) ⥤ ModuleCat k :=
  quotientLift (freeModule (k := k) c) (freeModule_mainComposite_zero c)

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
  rw [quotientLift_map_quotient]
  exact freeModule_map_generator c e

/-! The remaining declarations isolate the exact finite matrix calculation
used by the family.  They are phrased on the explicit modules, not as a
representation-infinite callback. -/

/-- Scalar-control statement for the displayed matrices.  This is the exact
linear-algebra lemma needed to finish the explicit Figure-15 family: every
endomorphism is scalar on every vertex, and a morphism between parameters
has `c*r=d*r`. -/
def HasScalarControl : Prop :=
  ∀ {c d : k} (f : module (k := k) c ⟶ module d),
    ∃ r : k,
      c * r = d * r ∧
      ∀ (a : Vertex) (x : obj (k := k) a),
        f.app (vertexObj (k := k) a) x = r • x

def leftCenterComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Central (k := k) ⟶ Central (k := k) :=
  f.app (vertexObj (k := k) .leftCenter)

def rightCenterComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Central (k := k) ⟶ Central (k := k) :=
  f.app (vertexObj (k := k) .rightCenter)

def upperCenterComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Branch (k := k) ⟶ Branch (k := k) :=
  f.app (vertexObj (k := k) .upperCenter)

def lowerCenterComponent {c d : k}
    (f : module (k := k) c ⟶ module d) :
    Branch (k := k) ⟶ Branch (k := k) :=
  f.app (vertexObj (k := k) .lowerCenter)

def leafComponent {c d : k}
    (f : module (k := k) c ⟶ module d) (a : Vertex) :
    obj (k := k) a ⟶ obj (k := k) a :=
  f.app (vertexObj (k := k) a)

def coeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .leftEndpoint 1

def lowerCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .lowerEndpoint 1

def upperCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .upperEndpoint 1

def rightCoeff {c d : k}
    (f : module (k := k) c ⟶ module d) : k :=
  leafComponent f .rightEndpoint 1

@[simp] private theorem deltaMap_basis_zero (c : k) :
    deltaMap (k := k) c (basis3 (k := k) 0) =
      basis3 (k := k) 0 + basis3 (k := k) 2 := by
  funext i
  fin_cases i <;> simp [deltaMap, basis3]

@[simp] private theorem deltaMap_basis_one (c : k) :
    deltaMap (k := k) c (basis3 (k := k) 1) =
      basis3 (k := k) 0 + basis3 (k := k) 1 +
        c • basis3 (k := k) 2 := by
  funext i
  fin_cases i <;> simp [deltaMap, basis3]

@[simp] private theorem deltaMap_basis_two (c : k) :
    deltaMap (k := k) c (basis3 (k := k) 2) =
      basis3 (k := k) 1 + basis3 (k := k) 2 := by
  funext i
  fin_cases i <;> simp [deltaMap, basis3]

@[simp] private theorem sigmaMap_basis_zero :
    sigmaMap (k := k) (basis3 (k := k) 0) = basis2 (k := k) 0 := by
  funext i
  fin_cases i <;> simp [sigmaMap, basis3, basis2]

@[simp] private theorem sigmaMap_basis_one :
    sigmaMap (k := k) (basis3 (k := k) 1) = basis2 (k := k) 1 := by
  funext i
  fin_cases i <;> simp [sigmaMap, basis3, basis2]

@[simp] private theorem sigmaMap_basis_two :
    sigmaMap (k := k) (basis3 (k := k) 2) = 0 := by
  funext i
  fin_cases i <;> simp [sigmaMap, basis3] <;> rfl

@[simp] private theorem rhoMap_basis_zero :
    rhoMap (k := k) (basis2 (k := k) 0) = basis3 (k := k) 0 := by
  funext i
  fin_cases i <;> simp [rhoMap, basis3, basis2]

@[simp] private theorem rhoMap_basis_one :
    rhoMap (k := k) (basis2 (k := k) 1) = basis3 (k := k) 1 := by
  funext i
  fin_cases i <;> simp [rhoMap, basis3, basis2]

private theorem naturality_sigma {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    lowerCenterComponent f (sigmaMap (k := k) x) =
      sigmaMap (k := k) (leftCenterComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.sigma)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Central (k := k) ⟶ Branch (k := k) ↦ q x) h

private theorem naturality_rho {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    rightCenterComponent f (rhoMap (k := k) x) =
      rhoMap (k := k) (upperCenterComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.rho)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Branch (k := k) ⟶ Central (k := k) ↦ q x) h

private theorem naturality_delta {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    rightCenterComponent f (deltaMap (k := k) c x) =
      deltaMap (k := k) d (leftCenterComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.delta)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Central (k := k) ⟶ Central (k := k) ↦ q x) h

private theorem naturality_alphaRight {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    leafComponent f .rightEndpoint (alphaRightMap (k := k) x) =
      alphaRightMap (k := k) (rightCenterComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaRight)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Central (k := k) ⟶ Leaf (k := k) ↦ q x) h

private theorem naturality_alphaUpper {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    leafComponent f .upperEndpoint (alphaUpperMap (k := k) x) =
      alphaUpperMap (k := k) (upperCenterComponent f x) := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaUpper)
  simp only [module_map_generator] at h
  exact congrArg (fun q : Branch (k := k) ⟶ Leaf (k := k) ↦ q x) h

private theorem left_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftCenterComponent f (basis3 (k := k) 0) =
      coeff f • basis3 (k := k) 0 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaLeft)
  simp only [module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Central (k := k) ↦ q 1) h
  change leftCenterComponent f (alphaLeftMap (k := k) 1) =
    alphaLeftMap (k := k) (leafComponent f .leftEndpoint 1) at h1
  calc
    leftCenterComponent f (basis3 (k := k) 0) =
        leftCenterComponent f (alphaLeftMap (k := k) 1) := by
      congr 1
      funext i
      fin_cases i <;> simp [alphaLeftMap, basis3]
    _ = alphaLeftMap (k := k) (leafComponent f .leftEndpoint 1) := h1
    _ = coeff f • basis3 (k := k) 0 := by
      funext i
      fin_cases i <;> simp [alphaLeftMap, basis3, coeff]

private theorem lower_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    lowerCenterComponent f (basis2 (k := k) 1) =
      lowerCoeff f • basis2 (k := k) 1 := by
  have h := f.naturality (generatorHom (k := k) Arrow.alphaLower)
  simp only [module_map_generator] at h
  have h1 := congrArg
    (fun q : Leaf (k := k) ⟶ Branch (k := k) ↦ q 1) h
  change lowerCenterComponent f (alphaLowerMap (k := k) 1) =
    alphaLowerMap (k := k) (leafComponent f .lowerEndpoint 1) at h1
  calc
    lowerCenterComponent f (basis2 (k := k) 1) =
        lowerCenterComponent f (alphaLowerMap (k := k) 1) := by
      congr 1
      funext i
      fin_cases i <;> simp [alphaLowerMap, basis2]
    _ = alphaLowerMap (k := k) (leafComponent f .lowerEndpoint 1) := h1
    _ = lowerCoeff f • basis2 (k := k) 1 := by
      funext i
      fin_cases i <;> simp [alphaLowerMap, basis2, lowerCoeff]

private theorem lower_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    lowerCenterComponent f (basis2 (k := k) 0) =
      coeff f • basis2 (k := k) 0 := by
  have h := naturality_sigma f (basis3 (k := k) 0)
  rw [sigmaMap_basis_zero, left_basis_zero, map_smul,
    sigmaMap_basis_zero] at h
  exact h

private theorem left_basis_one_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftCenterComponent f (basis3 (k := k) 1) =
      lowerCoeff f • basis3 (k := k) 1 +
        (leftCenterComponent f (basis3 (k := k) 1) 2) •
          basis3 (k := k) 2 := by
  have h := naturality_sigma f (basis3 (k := k) 1)
  rw [sigmaMap_basis_one, lower_basis_one] at h
  have h0 := congrArg (fun y : Branch (k := k) ↦ y 0) h
  have h1 := congrArg (fun y : Branch (k := k) ↦ y 1) h
  have hc0 : leftCenterComponent f (basis3 (k := k) 1) 0 = 0 := by
    simpa [sigmaMap, basis2] using h0.symm
  have hc1 : leftCenterComponent f (basis3 (k := k) 1) 1 =
      lowerCoeff f := by
    simpa [sigmaMap, basis2] using h1.symm
  funext i
  fin_cases i
  · simpa [basis3_apply] using hc0
  · simpa [basis3_apply] using hc1
  · simp [basis3_apply]

private theorem left_basis_two_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    leftCenterComponent f (basis3 (k := k) 2) =
      (leftCenterComponent f (basis3 (k := k) 2) 2) •
        basis3 (k := k) 2 := by
  have h := naturality_sigma f (basis3 (k := k) 2)
  rw [sigmaMap_basis_two, map_zero] at h
  have h0 := congrArg (fun y : Branch (k := k) ↦ y 0) h
  have h1 := congrArg (fun y : Branch (k := k) ↦ y 1) h
  have hc0 : leftCenterComponent f (basis3 (k := k) 2) 0 = 0 := by
    change (0 : k) = leftCenterComponent f (basis3 (k := k) 2) 0 at h0
    exact h0.symm
  have hc1 : leftCenterComponent f (basis3 (k := k) 2) 1 = 0 := by
    change (0 : k) = leftCenterComponent f (basis3 (k := k) 2) 1 at h1
    exact h1.symm
  funext i
  fin_cases i
  · simpa [basis3_apply] using hc0
  · simpa [basis3_apply] using hc1
  · simp [basis3_apply]

private theorem right_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    rightCenterComponent f (basis3 (k := k) 0) =
      upperCoeff f • basis3 (k := k) 0 := by
  have hrow := naturality_alphaRight f (basis3 (k := k) 0)
  have hrow1 : rightCenterComponent f (basis3 (k := k) 0) 1 = 0 := by
    simpa [alphaRightMap, basis3] using hrow.symm
  have hupper := naturality_alphaUpper f (basis2 (k := k) 0)
  have hu0 : upperCenterComponent f (basis2 (k := k) 0) 0 =
      upperCoeff f := by
    simpa [alphaUpperMap, basis2, upperCoeff] using hupper.symm
  have hrho := naturality_rho f (basis2 (k := k) 0)
  rw [rhoMap_basis_zero] at hrho
  have h0 := congrArg (fun y : Central (k := k) ↦ y 0) hrho
  have h2 := congrArg (fun y : Central (k := k) ↦ y 2) hrho
  have hc0 : rightCenterComponent f (basis3 (k := k) 0) 0 =
      upperCoeff f := by
    simpa [rhoMap, hu0] using h0
  have hc2 : rightCenterComponent f (basis3 (k := k) 0) 2 = 0 := by
    simpa [rhoMap] using h2
  funext i
  fin_cases i
  · simpa [basis3_apply] using hc0
  · simpa [basis3_apply] using hrow1
  · simpa [basis3_apply] using hc2

private theorem right_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    rightCenterComponent f (basis3 (k := k) 1) =
      rightCoeff f • basis3 (k := k) 1 := by
  have hrow := naturality_alphaRight f (basis3 (k := k) 1)
  have hc1 : rightCenterComponent f (basis3 (k := k) 1) 1 =
      rightCoeff f := by
    simpa [alphaRightMap, basis3, rightCoeff] using hrow.symm
  have hupper := naturality_alphaUpper f (basis2 (k := k) 1)
  have hu0 : upperCenterComponent f (basis2 (k := k) 1) 0 = 0 := by
    simpa [alphaUpperMap, basis2] using hupper.symm
  have hrho := naturality_rho f (basis2 (k := k) 1)
  rw [rhoMap_basis_one] at hrho
  have h0 := congrArg (fun y : Central (k := k) ↦ y 0) hrho
  have h2 := congrArg (fun y : Central (k := k) ↦ y 2) hrho
  have hc0 : rightCenterComponent f (basis3 (k := k) 1) 0 = 0 := by
    simpa [rhoMap, hu0] using h0
  have hc2 : rightCenterComponent f (basis3 (k := k) 1) 2 = 0 := by
    simpa [rhoMap] using h2
  funext i
  fin_cases i
  · simpa [basis3_apply] using hc0
  · simpa [basis3_apply] using hc1
  · simpa [basis3_apply] using hc2

private theorem right_basis_two_shape {c d : k}
    (f : module (k := k) c ⟶ module d) :
    rightCenterComponent f (basis3 (k := k) 2) =
      (rightCenterComponent f (basis3 (k := k) 2) 0) •
          basis3 (k := k) 0 +
        (rightCenterComponent f (basis3 (k := k) 2) 2) •
          basis3 (k := k) 2 := by
  have hrow := naturality_alphaRight f (basis3 (k := k) 2)
  have hc1 : rightCenterComponent f (basis3 (k := k) 2) 1 = 0 := by
    simpa [alphaRightMap, basis3] using hrow.symm
  funext i
  fin_cases i
  · simp [basis3_apply]
  · simpa [basis3_apply] using hc1
  · simp [basis3_apply]

private theorem upper_basis_zero {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperCenterComponent f (basis2 (k := k) 0) =
      upperCoeff f • basis2 (k := k) 0 := by
  have h := naturality_rho f (basis2 (k := k) 0)
  rw [rhoMap_basis_zero, right_basis_zero] at h
  have h0 := congrArg (fun y : Central (k := k) ↦ y 0) h
  have h1 := congrArg (fun y : Central (k := k) ↦ y 1) h
  funext i
  fin_cases i
  · simpa [rhoMap, basis3, basis2] using h0.symm
  · simpa [rhoMap, basis3, basis2] using h1.symm

private theorem upper_basis_one {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperCenterComponent f (basis2 (k := k) 1) =
      rightCoeff f • basis2 (k := k) 1 := by
  have h := naturality_rho f (basis2 (k := k) 1)
  rw [rhoMap_basis_one, right_basis_one] at h
  have h0 := congrArg (fun y : Central (k := k) ↦ y 0) h
  have h1 := congrArg (fun y : Central (k := k) ↦ y 1) h
  funext i
  fin_cases i
  · simpa [rhoMap, basis3, basis2] using h0.symm
  · simpa [rhoMap, basis3, basis2] using h1.symm

private theorem coefficient_relations {c d : k}
    (f : module (k := k) c ⟶ module d) :
    upperCoeff f = coeff f ∧
      rightCoeff f = coeff f ∧
      lowerCoeff f = coeff f ∧
      leftCenterComponent f (basis3 (k := k) 1) 2 = 0 ∧
      rightCenterComponent f (basis3 (k := k) 2) 0 = 0 ∧
      leftCenterComponent f (basis3 (k := k) 2) 2 = coeff f ∧
      rightCenterComponent f (basis3 (k := k) 2) 2 = coeff f ∧
      c * coeff f = d * coeff f := by
  have hdelta0 := naturality_delta f (basis3 (k := k) 0)
  rw [deltaMap_basis_zero, map_add, right_basis_zero,
    right_basis_two_shape, left_basis_zero, map_smul,
    deltaMap_basis_zero] at hdelta0
  have hdelta0_0 := congrArg (fun y : Central (k := k) ↦ y 0) hdelta0
  have hdelta0_2 := congrArg (fun y : Central (k := k) ↦ y 2) hdelta0
  have h0 : upperCoeff f +
      rightCenterComponent f (basis3 (k := k) 2) 0 = coeff f := by
    simpa [basis3_apply] using hdelta0_0
  have hs : rightCenterComponent f (basis3 (k := k) 2) 2 = coeff f := by
    simpa [basis3_apply] using hdelta0_2

  have hdelta2 := naturality_delta f (basis3 (k := k) 2)
  rw [deltaMap_basis_two, map_add, right_basis_one,
    right_basis_two_shape, left_basis_two_shape, map_smul,
    deltaMap_basis_two] at hdelta2
  have hdelta2_0 := congrArg (fun y : Central (k := k) ↦ y 0) hdelta2
  have hdelta2_1 := congrArg (fun y : Central (k := k) ↦ y 1) hdelta2
  have hdelta2_2 := congrArg (fun y : Central (k := k) ↦ y 2) hdelta2
  have hz : rightCenterComponent f (basis3 (k := k) 2) 0 = 0 := by
    simpa [basis3_apply] using hdelta2_0
  have hright : rightCoeff f =
      leftCenterComponent f (basis3 (k := k) 2) 2 := by
    simpa [basis3_apply] using hdelta2_1
  have hsb : rightCenterComponent f (basis3 (k := k) 2) 2 =
      leftCenterComponent f (basis3 (k := k) 2) 2 := by
    simpa [basis3_apply] using hdelta2_2
  have hb : leftCenterComponent f (basis3 (k := k) 2) 2 = coeff f :=
    hsb.symm.trans hs
  have hrightCoeff : rightCoeff f = coeff f := hright.trans hb
  have hupperCoeff : upperCoeff f = coeff f := by
    rw [hz, add_zero] at h0
    exact h0

  have hdelta1 := naturality_delta f (basis3 (k := k) 1)
  rw [deltaMap_basis_one, map_add, map_add, map_smul,
    right_basis_zero, right_basis_one, right_basis_two_shape,
    left_basis_one_shape, map_add, map_smul, map_smul,
    deltaMap_basis_one, deltaMap_basis_two] at hdelta1
  have hdelta1_0 := congrArg (fun y : Central (k := k) ↦ y 0) hdelta1
  have hdelta1_1 := congrArg (fun y : Central (k := k) ↦ y 1) hdelta1
  have hdelta1_2 := congrArg (fun y : Central (k := k) ↦ y 2) hdelta1
  have hlower : lowerCoeff f = coeff f := by
    have hscalar : coeff f = lowerCoeff f := by
      simpa [basis3_apply, hupperCoeff, hz] using hdelta1_0
    exact hscalar.symm
  have ha : leftCenterComponent f (basis3 (k := k) 1) 2 = 0 := by
    have hsum : coeff f = lowerCoeff f +
        leftCenterComponent f (basis3 (k := k) 1) 2 := by
      simpa [basis3_apply, hrightCoeff] using hdelta1_1
    rw [hlower] at hsum
    exact add_left_cancel (hsum.symm.trans (add_zero (coeff f)).symm)
  have hparameter : c * coeff f = d * coeff f := by
    have hcd : c * coeff f = coeff f * d := by
      have h := hdelta1_2
      simp [basis3_apply, hs, hlower, ha] at h
      exact h
    exact hcd.trans (mul_comm (coeff f) d)
  exact ⟨hupperCoeff, hrightCoeff, hlower, ha, hz, hb, hs, hparameter⟩

private theorem leftCenter_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    leftCenterComponent f x = coeff f • x := by
  rcases coefficient_relations f with
    ⟨_, _, hlower, ha, _, hb, _, _⟩
  have h1 : leftCenterComponent f (basis3 (k := k) 1) =
      coeff f • basis3 (k := k) 1 := by
    rw [left_basis_one_shape, hlower, ha, zero_smul, add_zero]
  have h2 : leftCenterComponent f (basis3 (k := k) 2) =
      coeff f • basis3 (k := k) 2 := by
    rw [left_basis_two_shape, hb]
  have hx : x = x 0 • basis3 (k := k) 0 +
      x 1 • basis3 (k := k) 1 + x 2 • basis3 (k := k) 2 := by
    funext i
    fin_cases i <;> simp [basis3]
  rw [hx, map_add, map_add, map_smul, map_smul, map_smul,
    left_basis_zero, h1, h2]
  module

private theorem rightCenter_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Central (k := k)) :
    rightCenterComponent f x = coeff f • x := by
  rcases coefficient_relations f with
    ⟨hupper, hright, _, _, hz, _, hs, _⟩
  have h0 : rightCenterComponent f (basis3 (k := k) 0) =
      coeff f • basis3 (k := k) 0 := by
    rw [right_basis_zero, hupper]
  have h1 : rightCenterComponent f (basis3 (k := k) 1) =
      coeff f • basis3 (k := k) 1 := by
    rw [right_basis_one, hright]
  have h2 : rightCenterComponent f (basis3 (k := k) 2) =
      coeff f • basis3 (k := k) 2 := by
    rw [right_basis_two_shape, hz, hs, zero_smul, zero_add]
  have hx : x = x 0 • basis3 (k := k) 0 +
      x 1 • basis3 (k := k) 1 + x 2 • basis3 (k := k) 2 := by
    funext i
    fin_cases i <;> simp [basis3]
  rw [hx, map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2]
  module

private theorem upperCenter_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    upperCenterComponent f x = coeff f • x := by
  rcases coefficient_relations f with ⟨hupper, hright, _, _, _, _, _, _⟩
  have h0 : upperCenterComponent f (basis2 (k := k) 0) =
      coeff f • basis2 (k := k) 0 := by rw [upper_basis_zero, hupper]
  have h1 : upperCenterComponent f (basis2 (k := k) 1) =
      coeff f • basis2 (k := k) 1 := by rw [upper_basis_one, hright]
  have hx : x = x 0 • basis2 (k := k) 0 +
      x 1 • basis2 (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basis2]
  rw [hx, map_add, map_smul, map_smul, h0, h1]
  module

private theorem lowerCenter_scalar {c d : k}
    (f : module (k := k) c ⟶ module d) (x : Branch (k := k)) :
    lowerCenterComponent f x = coeff f • x := by
  rcases coefficient_relations f with ⟨_, _, hlower, _, _, _, _, _⟩
  have h1 : lowerCenterComponent f (basis2 (k := k) 1) =
      coeff f • basis2 (k := k) 1 := by rw [lower_basis_one, hlower]
  have hx : x = x 0 • basis2 (k := k) 0 +
      x 1 • basis2 (k := k) 1 := by
    funext i
    fin_cases i <;> simp [basis2]
  rw [hx, map_add, map_smul, map_smul, lower_basis_zero, h1]
  module

private theorem leaf_map_eq_mul (g : Leaf (k := k) ⟶ Leaf (k := k))
    (x : k) : g x = x * g 1 := by
  simpa using g.hom.map_smul x 1

/-- The finite matrix computation for the explicit Figure-15 family.  It is
internal to the bound source: no ambient Hom-space complement or cleaving
assumption is used. -/
theorem hasScalarControl : HasScalarControl (k := k) := by
  intro c d f
  rcases coefficient_relations f with
    ⟨hupper, hright, hlower, _, _, _, _, hparameter⟩
  refine ⟨coeff f, hparameter, ?_⟩
  intro a x
  cases a with
  | leftCenter => exact leftCenter_scalar f x
  | rightCenter => exact rightCenter_scalar f x
  | upperCenter => exact upperCenter_scalar f x
  | lowerCenter => exact lowerCenter_scalar f x
  | leftEndpoint =>
      change leafComponent f .leftEndpoint x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | rightEndpoint =>
      change leafComponent f .rightEndpoint x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * rightCoeff f = coeff f • x
      rw [hright]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | upperEndpoint =>
      change leafComponent f .upperEndpoint x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * upperCoeff f = coeff f • x
      rw [hupper]
      change x * coeff f = coeff f * x
      exact mul_comm _ _
  | lowerEndpoint =>
      change leafComponent f .lowerEndpoint x = coeff f • x
      rw [leaf_map_eq_mul]
      change x * lowerCoeff f = coeff f • x
      rw [hlower]
      change x * coeff f = coeff f * x
      exact mul_comm _ _

section ControlledFamily

theorem parameter_eq_of_iso {c d : k}
    (hcontrol : HasScalarControl (k := k))
    (e : module (k := k) c ≅ module d) : c = d := by
  obtain ⟨r, hr, hscalar⟩ := hcontrol e.hom
  have hr0 : r ≠ 0 := by
    intro hz
    let X : LinearSource (k := k) := vertexObj (k := k) .leftEndpoint
    have hhom := hscalar .leftEndpoint (1 : obj (k := k) .leftEndpoint)
    rw [hz, zero_smul] at hhom
    have hzeroImage :
        e.hom.app X (0 : k) =
          (0 : (module (k := k) d).obj X) :=
      map_zero _
    have heq :
        e.hom.app X (1 : k) = e.hom.app X (0 : k) :=
      hhom.trans hzeroImage.symm
    have honezero : (1 : k) = 0 :=
      (ConcreteCategory.bijective_of_isIso (e.hom.app X)).1 heq
    exact one_ne_zero honezero
  exact mul_right_cancel₀ hr0 hr

theorem end_eq_zero_or_id_of_idempotent (c : k)
    (hcontrol : HasScalarControl (k := k))
    (f : module (k := k) c ⟶ module c) (hf : f ≫ f = f) :
    f = 0 ∨ f = 𝟙 _ := by
  obtain ⟨r, _, hscalar⟩ := hcontrol f
  have hr : r * r = r := by
    have h := congrArg
      (fun g : module (k := k) c ⟶ module c ↦
        g.app (vertexObj (k := k) .leftEndpoint) (1 : k)) hf
    change f.app (vertexObj (k := k) .leftEndpoint)
      (f.app (vertexObj (k := k) .leftEndpoint) (1 : k)) =
        f.app (vertexObj (k := k) .leftEndpoint) (1 : k) at h
    rw [hscalar, hscalar] at h
    simpa [smul_smul] using h
  rcases eq_zero_or_one_of_sq_eq_self (by simpa [pow_two] using hr) with h0 | h1
  · left
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases X with ⟨X⟩
    change f.app (vertexObj (k := k) X.unop) x = 0
    rw [hscalar X.unop, h0, zero_smul]
  · right
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases X with ⟨X⟩
    change f.app (vertexObj (k := k) X.unop) x = x
    rw [hscalar X.unop, h1, one_smul]

theorem module_not_isZero (c : k) : ¬ IsZero (module (k := k) c) := by
  intro hzero
  have hid : (𝟙 (module (k := k) c) : module c ⟶ module c) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hzero
  have h := congrArg
    (fun f : module (k := k) c ⟶ module c ↦
      f.app (vertexObj (k := k) .leftEndpoint) (1 : k)) hid
  change (1 : k) = 0 at h
  exact one_ne_zero h

theorem module_indecomposable
    (hcontrol : HasScalarControl (k := k)) (c : k) :
    Indecomposable (module (k := k) c) := by
  refine ⟨module_not_isZero c, ?_⟩
  intro Y Z e
  let p : module (k := k) c ⟶ module c :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  have hp : p ≫ p = p := by simp [p, Category.assoc]
  rcases end_eq_zero_or_id_of_idempotent c hcontrol p hp with hp0 | hp1
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

instance module_obj_finite (c : k) (X : LinearSource (k := k)) :
    Module.Finite k ((module (k := k) c).obj X) := by
  change Module.Finite k (obj (k := k)
    (LinearPathCategory.vertex X.as).unop)
  unfold obj Central Branch Leaf
  cases (LinearPathCategory.vertex X.as).unop <;>
    infer_instance

theorem module_end_isLocalRing (c : k) :
    IsLocalRing (CategoryTheory.End (module (k := k) c)) :=
  LargeIndecomposable.ClosedZigzagTransfer.functor_end_isLocalRing
    (module (k := k) c) (fun X ↦ module_obj_finite c X)
      (module_indecomposable (hasScalarControl (k := k)) c)

section Infinite

variable [Infinite k]

def family (n : ℕ) : LinearSource (k := k) ⥤ ModuleCat k :=
  module (Infinite.natEmbedding k n)

instance family_additive (n : ℕ) : (family (k := k) n).Additive := by
  unfold family
  infer_instance

instance family_linear (n : ℕ) : (family (k := k) n).Linear k := by
  unfold family
  infer_instance

theorem family_obj_finite (n : ℕ) (X : LinearSource (k := k)) :
    Module.Finite k ((family (k := k) n).obj X) := by
  unfold family
  exact module_obj_finite _ X

theorem family_indecomposable (n : ℕ) :
    Indecomposable (family (k := k) n) :=
  module_indecomposable (hasScalarControl (k := k)) _

theorem family_eq_of_iso {m n : ℕ}
    (e : family (k := k) m ≅ family n) : m = n := by
  apply (Infinite.natEmbedding k).injective
  exact parameter_eq_of_iso (hasScalarControl (k := k)) e

theorem family_end_isLocalRing (n : ℕ) :
    IsLocalRing (CategoryTheory.End (family (k := k) n)) := by
  unfold family
  exact module_end_isLocalRing _

def sourceFamily :
    CleavingSourceFamily (k := k) (LinearSource (k := k)) where
  anchor := vertexObj (k := k) .leftCenter
  module := family (k := k)
  additive := fun _ ↦ inferInstance
  linear := fun _ ↦ inferInstance
  obj_finite := family_obj_finite
  indecomposable := family_indecomposable
  eq_of_iso := fun h ↦ family_eq_of_iso (Classical.choice h)
  end_isLocalRing := family_end_isLocalRing

end Infinite

end ControlledFamily

section Diagram

universe v w

variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- Literal ambient Figure-15 data, including exactly its displayed zero
relation. -/
structure DiagramData where
  object : Vertex → C
  arrow : ∀ {a b : Vertex}, (a ⟶ b) → (object a ⟶ object b)
  main_zero :
    arrow Arrow.alphaLeft ≫ arrow Arrow.delta ≫
      arrow Arrow.alphaRight = 0

namespace DiagramData

def freeFunctor (G : DiagramData (C := C)) : FreeLinearSource k ⥤ C :=
  LinearPathCategory.lift
    (fun a ↦ G.object a.unop)
    (fun e ↦ G.arrow e.unop)

instance freeFunctor_additive (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).Additive := by unfold freeFunctor; infer_instance

instance freeFunctor_linear (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).Linear k := by unfold freeFunctor; infer_instance

@[simp] theorem freeFunctor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.freeFunctor (k := k)).map (freeGeneratorHom (k := k) e) =
      G.arrow e := by
  unfold freeFunctor freeGeneratorHom
  rw [LinearPathCategory.lift_map_pathHom]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

theorem freeFunctor_main_zero (G : DiagramData (C := C)) :
    (G.freeFunctor (k := k)).map (mainComposite (k := k)) = 0 := by
  unfold mainComposite
  rw [Functor.map_comp, Functor.map_comp]
  simp only [freeFunctor_map_generator]
  exact G.main_zero

def functor (G : DiagramData (C := C)) : LinearSource (k := k) ⥤ C :=
  quotientLift (G.freeFunctor (k := k)) (G.freeFunctor_main_zero (k := k))

instance functor_additive (G : DiagramData (C := C)) :
    (G.functor (k := k)).Additive := by unfold functor; infer_instance

instance functor_linear (G : DiagramData (C := C)) :
    (G.functor (k := k)).Linear k := by unfold functor; infer_instance

@[simp] theorem functor_obj (G : DiagramData (C := C)) (a : Vertex) :
    (G.functor (k := k)).obj (vertexObj (k := k) a) = G.object a := rfl

@[simp] theorem functor_map_generator (G : DiagramData (C := C))
    {a b : Vertex} (e : a ⟶ b) :
    (G.functor (k := k)).map (generatorHom (k := k) e) = G.arrow e := by
  unfold functor generatorHom
  rw [quotientLift_map_quotient]
  exact G.freeFunctor_map_generator (k := k) e

end DiagramData

end Diagram

section AmbientContradiction

universe uA x

variable [Infinite k]
variable {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]
variable (S : LargeIndecomposable.SplitBasicIdempotents
  (k := k) (A := A) (ι := ι))

/-- Exact Figure-15 contradiction boundary.  The finite matrix computation is
proved above; the only remaining callback is the literal Hom-bifunctor
retraction of the bound diagram. -/
theorem not_isRepresentationFinite_of_figure15Data
    (G : DiagramData (C := S.ProjectiveCategory))
    (hG : HomBifunctorRetraction (k := k) (G.functor (k := k))) :
    ¬ LargeIndecomposable.IsRepresentationFinite k A :=
  CriticalSingularCleaving.not_isRepresentationFinite_of_homBifunctorRetraction
    (S := S) (D := G.functor (k := k))
      (sourceFamily (k := k)) hG

end AmbientContradiction

end LargeIndecomposable.CriticalSingularFigure15
