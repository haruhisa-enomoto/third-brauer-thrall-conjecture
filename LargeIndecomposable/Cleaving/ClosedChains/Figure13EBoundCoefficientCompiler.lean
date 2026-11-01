module

public import LargeIndecomposable.Cleaving.ClosedChains.CrossUniverseThinQuotientRetraction
public import LargeIndecomposable.Cleaving.ClosedChains.Figure13Coefficient
public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.RoiterFigure13E

@[expose] public section

/-!
# Coefficient compiler for the bound BGRS Figure 13E source

The exceptional representatives in the Figure-13 argument satisfy
`alpha ≫ beta = 0`.  Consequently the source is the seven-vertex bound
diagram `E`, rather than the free five-vertex diagram `D`.  This file builds
the coherent arm coefficients needed by `E` and compiles their generator
equations into a Hom-bifunctor retraction of that bound source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.RoiterFigure13E

open LargeIndecomposable.ClosedZigzagTransfer
open LargeIndecomposable.ClosedZigzagCrossUniverse

universe u v w

variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-! ## Thinness of the free Figure-13E quiver -/

abbrev TotalArrow := Σ a, Σ b, Arrow a b

def totalArrow {a b : Vertex} (e : a ⟶ b) : TotalArrow :=
  ⟨a, b, e⟩

def totalArrowEndpoints (e : TotalArrow) : Vertex × Vertex :=
  (e.1, e.2.1)

private theorem totalArrowEndpoints_injective :
    Function.Injective totalArrowEndpoints := by
  intro e f hef
  rcases e with ⟨a, b, e⟩
  rcases f with ⟨c, d, f⟩
  cases e <;> cases f <;>
    simp only [totalArrowEndpoints, Prod.mk.injEq] at hef ⊢
  all_goals simp_all

private theorem arrow_subsingleton (a b : Vertex) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro e f
  have htotal : totalArrow e = totalArrow f :=
    totalArrowEndpoints_injective (by rfl)
  cases htotal
  rfl

private theorem totalArrow_source_ne_target (e : TotalArrow) :
    e.1 ≠ e.2.1 := by
  rcases e with ⟨a, b, e⟩
  cases e <;> intro h <;> cases h

private theorem opposite_arrow_source_ne_target
    {a b : Vertexᵒᵖ} (e : a ⟶ b) : a ≠ b := by
  intro hab
  apply totalArrow_source_ne_target (totalArrow e.unop)
  exact (congrArg Opposite.unop hab).symm

private theorem no_arrow_from_upperRight (b : Vertex) :
    IsEmpty (Vertex.upperRight ⟶ b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_from_rightMiddle (b : Vertex) :
    IsEmpty (Vertex.rightMiddle ⟶ b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_from_lowerMiddle (b : Vertex) :
    IsEmpty (Vertex.lowerMiddle ⟶ b) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_upperMiddle (a : Vertex) :
    IsEmpty (a ⟶ Vertex.upperMiddle) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_leftMiddle (a : Vertex) :
    IsEmpty (a ⟶ Vertex.leftMiddle) := by
  constructor
  intro e
  cases e

private theorem no_arrow_to_lowerLeft (a : Vertex) :
    IsEmpty (a ⟶ Vertex.lowerLeft) := by
  constructor
  intro e
  cases e

private theorem opposite_no_arrow_to_upperRight (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.upperRight) := by
  constructor
  intro e
  exact (no_arrow_from_upperRight a.unop).false e.unop

private theorem opposite_no_arrow_to_rightMiddle (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.rightMiddle) := by
  constructor
  intro e
  exact (no_arrow_from_rightMiddle a.unop).false e.unop

private theorem opposite_no_arrow_to_lowerMiddle (a : Vertexᵒᵖ) :
    IsEmpty (a ⟶ Opposite.op Vertex.lowerMiddle) := by
  constructor
  intro e
  exact (no_arrow_from_lowerMiddle a.unop).false e.unop

private theorem opposite_no_arrow_from_upperMiddle (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.upperMiddle ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_upperMiddle b.unop).false e.unop

private theorem opposite_no_arrow_from_leftMiddle (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.leftMiddle ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_leftMiddle b.unop).false e.unop

private theorem opposite_no_arrow_from_lowerLeft (b : Vertexᵒᵖ) :
    IsEmpty (Opposite.op Vertex.lowerLeft ⟶ b) := by
  constructor
  intro e
  exact (no_arrow_to_lowerLeft b.unop).false e.unop

theorem path_length_zero_of_target_upperRight {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.upperRight)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e => exact False.elim ((opposite_no_arrow_to_upperRight _).false e)

theorem path_length_zero_of_target_rightMiddle {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.rightMiddle)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e => exact False.elim ((opposite_no_arrow_to_rightMiddle _).false e)

theorem path_length_zero_of_target_lowerMiddle {a : Vertexᵒᵖ}
    (p : Quiver.Path a (Opposite.op Vertex.lowerMiddle)) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons _ e => exact False.elim ((opposite_no_arrow_to_lowerMiddle _).false e)

theorem path_length_zero_of_source_upperMiddle {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.upperMiddle) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_upperMiddle _).false e)

theorem path_length_zero_of_source_leftMiddle {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.leftMiddle) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_leftMiddle _).false e)

theorem path_length_zero_of_source_lowerLeft {b : Vertexᵒᵖ}
    (p : Quiver.Path (Opposite.op Vertex.lowerLeft) b) : p.length = 0 := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hsource := p.eq_of_length_zero ih
      subst_vars
      exact False.elim ((opposite_no_arrow_from_lowerLeft _).false e)

theorem path_length_zero_before_arrow_to_center
    {a b : Vertexᵒᵖ} (p : Quiver.Path a b)
    (e : b ⟶ Opposite.op Vertex.center) : p.length = 0 := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | betaCenter => exact path_length_zero_of_target_rightMiddle p
      | tauLower => exact path_length_zero_of_target_lowerMiddle p

private theorem arrow_to_leftMiddle_source_eq_center
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.leftMiddle) :
    b = Opposite.op Vertex.center := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_lowerLeft_source_eq_lowerMiddle
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.lowerLeft) :
    b = Opposite.op Vertex.lowerMiddle := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop
      rfl

private theorem arrow_to_upperMiddle_source
    {b : Vertexᵒᵖ} (e : b ⟶ Opposite.op Vertex.upperMiddle) :
    b = Opposite.op Vertex.center ∨
      b = Opposite.op Vertex.upperRight := by
  induction b using Opposite.rec with
  | _ b =>
      cases e.unop with
      | tauUpper => exact Or.inl rfl
      | betaUpper => exact Or.inr rfl

private theorem path_subsingleton_of_all_length_zero
    (a b : Vertexᵒᵖ) (hzero : ∀ p : Quiver.Path a b, p.length = 0) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  have hp := p.eq_of_length_zero (hzero p)
  subst b
  rw [Quiver.Path.eq_nil_of_length_zero p (hzero p),
    Quiver.Path.eq_nil_of_length_zero q (hzero q)]

theorem path_center_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.center)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_before_arrow_to_center q e
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_before_arrow_to_center p e
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have hp0 := path_length_zero_before_arrow_to_center p e
          have hq0 := path_length_zero_before_arrow_to_center q f
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

theorem path_leftMiddle_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.leftMiddle)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_leftMiddle q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_leftMiddle p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_leftMiddle_source_eq_center e
          have hf := arrow_to_leftMiddle_source_eq_center f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_center_subsingleton a).elim p q

theorem path_lowerLeft_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.lowerLeft)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_lowerLeft q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_lowerLeft p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          have he := arrow_to_lowerLeft_source_eq_lowerMiddle e
          have hf := arrow_to_lowerLeft_source_eq_lowerMiddle f
          subst_vars
          have hef : e = f := Quiver.Hom.unop_inj
            ((arrow_subsingleton _ _).elim e.unop f.unop)
          subst f
          congr 1
          exact (path_subsingleton_of_all_length_zero a _
            (fun r ↦ path_length_zero_of_target_lowerMiddle r)).elim p q

private theorem no_path_upperRight_to_center
    (p : Quiver.Path (Opposite.op Vertex.upperRight)
      (Opposite.op Vertex.center)) : False := by
  cases p with
  | cons p e =>
      have hp0 := path_length_zero_before_arrow_to_center p e
      have hstart := p.eq_of_length_zero hp0
      subst_vars
      have hempty : IsEmpty (Vertex.center ⟶ Vertex.upperRight) := by
        constructor
        intro f
        cases f
      exact hempty.false e.unop

theorem path_upperMiddle_subsingleton (a : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a (Opposite.op Vertex.upperMiddle)) := by
  constructor
  intro p q
  cases p with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e =>
          have hq0 := path_length_zero_of_source_upperMiddle q
          have hstart := q.eq_of_length_zero hq0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
  | cons p e =>
      cases q with
      | nil =>
          have hp0 := path_length_zero_of_source_upperMiddle p
          have hstart := p.eq_of_length_zero hp0
          exact False.elim (opposite_arrow_source_ne_target e hstart.symm)
      | cons q f =>
          rcases arrow_to_upperMiddle_source e with he | he <;>
            rcases arrow_to_upperMiddle_source f with hf | hf
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_center_subsingleton a).elim p q
          · subst_vars
            have hq0 := path_length_zero_of_target_upperRight q
            have ha := q.eq_of_length_zero hq0
            subst a
            exact False.elim (no_path_upperRight_to_center p)
          · subst_vars
            have hp0 := path_length_zero_of_target_upperRight p
            have ha := p.eq_of_length_zero hp0
            subst a
            exact False.elim (no_path_upperRight_to_center q)
          · subst_vars
            have hef : e = f := Quiver.Hom.unop_inj
              ((arrow_subsingleton _ _).elim e.unop f.unop)
            subst f
            congr 1
            exact (path_subsingleton_of_all_length_zero a _
              (fun r ↦ path_length_zero_of_target_upperRight r)).elim p q

/-- The underlying free Figure-13E quiver is thin. -/
theorem path_subsingleton (a b : Vertexᵒᵖ) :
    Subsingleton (Quiver.Path a b) := by
  induction b using Opposite.rec with
  | _ b =>
      cases b with
      | upperMiddle => exact path_upperMiddle_subsingleton a
      | upperRight =>
          exact path_subsingleton_of_all_length_zero a
            (Opposite.op Vertex.upperRight)
            (fun p ↦ path_length_zero_of_target_upperRight p)
      | leftMiddle => exact path_leftMiddle_subsingleton a
      | center => exact path_center_subsingleton a
      | rightMiddle =>
          exact path_subsingleton_of_all_length_zero a
            (Opposite.op Vertex.rightMiddle)
            (fun p ↦ path_length_zero_of_target_rightMiddle p)
      | lowerMiddle =>
          exact path_subsingleton_of_all_length_zero a
            (Opposite.op Vertex.lowerMiddle)
            (fun p ↦ path_length_zero_of_target_lowerMiddle p)
      | lowerLeft => exact path_lowerLeft_subsingleton a

/-- Coherent coefficients on the two arms of Figure 13.  Unlike
`Figure13CoefficientExtensionData`, this package deliberately has no outer
cross coefficient: in Figure 13E the outer composite is the defining zero
relation. -/
structure Figure13ArmCoefficientData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residue : End Y →ₐ[k] k) (tau : End Y)
    (middle : RadicalSquareCoefficientData residue tau) where
  alphaZero : (X ⟶ Y) →ₗ[k] k
  alphaOne : (X ⟶ Y) →ₗ[k] k
  betaZero : (Y ⟶ Z) →ₗ[k] k
  betaOne : (Y ⟶ Z) →ₗ[k] k
  alphaZero_post : ∀ a : End Y,
    alphaZero (alpha ≫ a.asHom) = residue a
  alphaOne_post : ∀ a : End Y,
    alphaOne (alpha ≫ a.asHom) = middle.coefficientOne a
  betaZero_pre : ∀ a : End Y,
    betaZero (a.asHom ≫ beta) = residue a
  betaOne_pre : ∀ a : End Y,
    betaOne (a.asHom ≫ beta) = middle.coefficientOne a

/-- The middle coefficients extend independently to both arms whenever the
two arrows and their adjacent `tau` composites survive. -/
theorem exists_figure13ArmCoefficientData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z)
    (residue : End Y →ₐ[k] k) (tau : End Y)
    (middle : RadicalSquareCoefficientData residue tau)
    (hunit : ∀ a : End Y, IsUnit a ↔ residue a ≠ 0)
    (hfactor : ∀ a : End Y, residue a = 0 →
      ∃ q : End Y, a = q * tau)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (halpha : alpha ≠ 0) (halphaTau : alpha ≫ tau.asHom ≠ 0)
    (hbeta : beta ≠ 0) (htauBeta : tau.asHom ≫ beta ≠ 0) :
    Nonempty (Figure13ArmCoefficientData
      alpha beta residue tau middle) := by
  let alphaAction := postEndomorphismLinearMap (k := k) alpha
  let betaAction := preEndomorphismLinearMap (k := k) beta
  have alphaKerResidue : LinearMap.ker alphaAction ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change alpha ≫ a.asHom = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
    apply halpha
    apply (cancel_mono a.asHom).1
    simpa using ha
  have alphaKerOne : LinearMap.ker alphaAction ≤
      LinearMap.ker middle.coefficientOne := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change alpha ≫ a.asHom = 0 at ha
    have hres : residue a = 0 :=
      LinearMap.mem_ker.mp
        (alphaKerResidue (LinearMap.mem_ker.mpr ha))
    obtain ⟨q, hq⟩ := hfactor a hres
    rw [hq, middle.coefficientOne_mul_tau]
    by_contra hqres
    have hqUnit : IsUnit q := (hunit q).2 hqres
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply halphaTau
    apply (cancel_mono q.asHom).1
    have hzero : (alpha ≫ tau.asHom) ≫ q.asHom = 0 := by
      calc
        (alpha ≫ tau.asHom) ≫ q.asHom =
            alpha ≫ (q * tau).asHom := by
              rw [End.mul_def, Category.assoc]
        _ = alpha ≫ a.asHom := by rw [← hq]
        _ = 0 := ha
    simpa using hzero
  have betaKerResidue : LinearMap.ker betaAction ≤
      LinearMap.ker residue.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a.asHom ≫ beta = 0 at ha
    by_contra hres
    have haUnit : IsUnit a := (hunit a).2 hres
    letI : IsIso a.asHom := (isUnit_iff_isIso a).1 haUnit
    apply hbeta
    apply (cancel_epi a.asHom).1
    simpa using ha
  have betaKerOne : LinearMap.ker betaAction ≤
      LinearMap.ker middle.coefficientOne := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    change a.asHom ≫ beta = 0 at ha
    have hres : residue a = 0 :=
      LinearMap.mem_ker.mp
        (betaKerResidue (LinearMap.mem_ker.mpr ha))
    obtain ⟨q, hq⟩ := hfactor a hres
    rw [hq, middle.coefficientOne_mul_tau]
    by_contra hqres
    have hqUnit : IsUnit q := (hunit q).2 hqres
    letI : IsIso q.asHom := (isUnit_iff_isIso q).1 hqUnit
    apply htauBeta
    apply (cancel_epi q.asHom).1
    have hzero : q.asHom ≫ (tau.asHom ≫ beta) = 0 := by
      calc
        q.asHom ≫ (tau.asHom ≫ beta) =
            (tau * q).asHom ≫ beta := by
              rw [End.mul_def, Category.assoc]
        _ = (q * tau).asHom ≫ beta := by rw [← hcomm q]
        _ = a.asHom ≫ beta := by rw [← hq]
        _ = 0 := ha
    simpa using hzero
  obtain ⟨alphaZero, hAlphaZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le alphaAction residue.toLinearMap
      alphaKerResidue
  obtain ⟨alphaOne, hAlphaOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le alphaAction middle.coefficientOne
      alphaKerOne
  obtain ⟨betaZero, hBetaZero⟩ :=
    exists_linearMap_comp_eq_of_ker_le betaAction residue.toLinearMap
      betaKerResidue
  obtain ⟨betaOne, hBetaOne⟩ :=
    exists_linearMap_comp_eq_of_ker_le betaAction middle.coefficientOne
      betaKerOne
  refine ⟨⟨alphaZero, alphaOne, betaZero, betaOne, ?_, ?_, ?_, ?_⟩⟩
  all_goals intro a
  · exact DFunLike.congr_fun hAlphaZero a
  · exact DFunLike.congr_fun hAlphaOne a
  · exact DFunLike.congr_fun hBetaZero a
  · exact DFunLike.congr_fun hBetaOne a

/-! ## The repeated-middle bound diagram and its coefficients -/

/-- Figure 13E with its three middle occurrences realized by `Y`, its two
left occurrences by `X`, and its two right occurrences by `Z`. -/
def repeatedMiddleDiagram
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0) : DiagramData (C := C) where
  object
    | .upperMiddle | .center | .lowerMiddle => Y
    | .upperRight | .rightMiddle => Z
    | .leftMiddle | .lowerLeft => X
  arrow := fun {_ _} e ↦ match e with
    | Arrow.tauUpper => tau.asHom
    | Arrow.betaUpper => beta
    | Arrow.alphaCenter => alpha
    | Arrow.betaCenter => beta
    | Arrow.tauLower => tau.asHom
    | Arrow.alphaLower => alpha
  main_zero := hspecial

def leftIdentityCoefficient
    {X Y Z : C} {alpha : X ⟶ Y} {beta : Y ⟶ Z} {tau : End Y}
    {residue : End Y →ₐ[k] k}
    {middle : RadicalSquareCoefficientData residue tau}
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle) :
    End X →ₗ[k] k :=
  arm.alphaZero.comp (preEndomorphismLinearMap (k := k) alpha)

def rightIdentityCoefficient
    {X Y Z : C} {alpha : X ⟶ Y} {beta : Y ⟶ Z} {tau : End Y}
    {residue : End Y →ₐ[k] k}
    {middle : RadicalSquareCoefficientData residue tau}
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle) :
    End Z →ₗ[k] k :=
  arm.betaZero.comp (postEndomorphismLinearMap (k := k) beta)

/-- The endpoint coefficient attached to every ordered pair of Figure-13E
vertices.  The `leftMiddle → rightMiddle` entry is zero because that path
is precisely the defining relation. -/
def repeatedMiddleEndpointCoefficient
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (a b : Vertex) :
    ((repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b) →ₗ[k] k := by
  cases a <;> cases b
  -- upperMiddle
  · exact residue.toLinearMap
  · exact arm.betaZero
  · exact 0
  · exact middle.coefficientOne
  · exact arm.betaOne
  · exact middle.coefficientTwo
  · exact 0
  -- upperRight
  · exact 0
  · exact rightIdentityCoefficient arm
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  -- leftMiddle
  · exact 0
  · exact 0
  · exact leftIdentityCoefficient arm
  · exact arm.alphaZero
  · exact 0
  · exact arm.alphaOne
  · exact 0
  -- center
  · exact 0
  · exact 0
  · exact 0
  · exact residue.toLinearMap
  · exact arm.betaZero
  · exact middle.coefficientOne
  · exact 0
  -- rightMiddle
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact rightIdentityCoefficient arm
  · exact 0
  · exact 0
  -- lowerMiddle
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact residue.toLinearMap
  · exact 0
  -- lowerLeft
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact 0
  · exact arm.alphaZero
  · exact leftIdentityCoefficient arm

/-- Path-indexed form of `repeatedMiddleEndpointCoefficient`. -/
def repeatedMiddleVertexCoefficient
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    {a b : Vertexᵒᵖ} (_p : Quiver.Path b a) :
    ((repeatedMiddleDiagram alpha beta tau hspecial).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop) →ₗ[k] k :=
  repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
    a.unop b.unop

@[simp]
theorem repeatedMiddle_pathMap_toPath
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0) {a b : Vertex} (e : a ⟶ b) :
    LinearPathCategory.pathMap
        (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
        (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop)
        (Quiver.Hom.toPath (Quiver.Hom.op e)) =
      (repeatedMiddleDiagram alpha beta tau hspecial).arrow e := by
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  rfl

/-- Except when it creates the displayed zero relation, left whiskering by
a Figure-13E generator preserves the endpoint coefficient. -/
theorem repeatedMiddleEndpointCoefficient_left_arrow
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0)
    {a' a : Vertex} (e : a' ⟶ a) (b : Vertex)
    (hnot : ¬ (a' = Vertex.leftMiddle ∧ b = Vertex.rightMiddle))
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a' b ((repeatedMiddleDiagram alpha beta tau hspecial).arrow e ≫ g) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b g := by
  cases e <;> cases b
  -- tauUpper
  · change residue (End.of (tau.asHom ≫ g)) = 0
    change Y ⟶ Y at g
    change residue (End.of g * tau) = 0
    rw [map_mul, hresTau, mul_zero]
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.betaZero (tau.asHom ≫ (q.asHom ≫ beta)) = 0
    rw [← Category.assoc]
    change arm.betaZero ((q * tau).asHom ≫ beta) = 0
    rw [arm.betaZero_pre, map_mul, hresTau, mul_zero]
  · rfl
  · change middle.coefficientOne (End.of (tau.asHom ≫ g)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (End.of g * tau) = residue (End.of g)
    exact middle.coefficientOne_mul_tau (End.of g)
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.betaOne (tau.asHom ≫ (q.asHom ≫ beta)) =
      arm.betaZero (q.asHom ≫ beta)
    rw [← Category.assoc]
    change arm.betaOne ((q * tau).asHom ≫ beta) =
      arm.betaZero (q.asHom ≫ beta)
    rw [arm.betaOne_pre, arm.betaZero_pre,
      middle.coefficientOne_mul_tau]
  · change middle.coefficientTwo (End.of (tau.asHom ≫ g)) =
      middle.coefficientOne (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientTwo (End.of g * tau) =
      middle.coefficientOne (End.of g)
    exact middle.coefficientTwo_mul_tau (End.of g)
  · rfl
  -- betaUpper
  · change residue (End.of (beta ≫ g)) = 0
    exact hThroughZZero beta g
  · rfl
  · rfl
  · change middle.coefficientOne (End.of (beta ≫ g)) = 0
    exact hThroughZOne beta g
  · change arm.betaOne (beta ≫ g) = 0
    exact hOuterZOne (End.of g)
  · change middle.coefficientTwo (End.of (beta ≫ g)) = 0
    exact hThroughZTwo beta g
  · rfl
  -- alphaCenter
  · rfl
  · rfl
  · change leftIdentityCoefficient arm (alpha ≫ g) = 0
    change arm.alphaZero ((alpha ≫ g) ≫ alpha) = 0
    calc
      arm.alphaZero ((alpha ≫ g) ≫ alpha) =
          residue (End.of (g ≫ alpha)) := by
        rw [Category.assoc]
        exact arm.alphaZero_post (End.of (g ≫ alpha))
      _ = 0 := hThroughXZero g alpha
  · change arm.alphaZero (alpha ≫ g) = residue (End.of g)
    exact arm.alphaZero_post (End.of g)
  · exact False.elim (hnot ⟨rfl, rfl⟩)
  · change arm.alphaOne (alpha ≫ g) = middle.coefficientOne (End.of g)
    exact arm.alphaOne_post (End.of g)
  · rfl
  -- betaCenter
  · rfl
  · rfl
  · rfl
  · change residue (End.of (beta ≫ g)) = 0
    exact hThroughZZero beta g
  · rfl
  · change middle.coefficientOne (End.of (beta ≫ g)) = 0
    exact hThroughZOne beta g
  · rfl
  -- tauLower
  · rfl
  · rfl
  · rfl
  · change residue (End.of (tau.asHom ≫ g)) = 0
    change Y ⟶ Y at g
    change residue (End.of g * tau) = 0
    rw [map_mul, hresTau, mul_zero]
  · rcases hBetaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.betaZero (tau.asHom ≫ (q.asHom ≫ beta)) = 0
    rw [← Category.assoc]
    change arm.betaZero ((q * tau).asHom ≫ beta) = 0
    rw [arm.betaZero_pre, map_mul, hresTau, mul_zero]
  · change middle.coefficientOne (End.of (tau.asHom ≫ g)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (End.of g * tau) = residue (End.of g)
    exact middle.coefficientOne_mul_tau (End.of g)
  · rfl
  -- alphaLower
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change arm.alphaZero (alpha ≫ g) = residue (End.of g)
    exact arm.alphaZero_post (End.of g)
  · change leftIdentityCoefficient arm (alpha ≫ g) = 0
    change arm.alphaZero ((alpha ≫ g) ≫ alpha) = 0
    calc
      arm.alphaZero ((alpha ≫ g) ≫ alpha) =
          residue (End.of (g ≫ alpha)) := by
        rw [Category.assoc]
        exact arm.alphaZero_post (End.of (g ≫ alpha))
      _ = 0 := hThroughXZero g alpha

/-- Except when it creates the displayed zero relation, right whiskering by
a Figure-13E generator preserves the endpoint coefficient. -/
theorem repeatedMiddleEndpointCoefficient_right_arrow
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (a : Vertex) {b b' : Vertex} (e : b ⟶ b')
    (hnot : ¬ (a = Vertex.leftMiddle ∧ b' = Vertex.rightMiddle))
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b' (g ≫ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b g := by
  cases e <;> cases a
  -- tauUpper
  · change middle.coefficientOne (End.of (g ≫ tau.asHom)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (tau * End.of g) = residue (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientOne_mul_tau (End.of g)
  · rfl
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.alphaZero ((alpha ≫ q.asHom) ≫ tau.asHom) = 0
    rw [Category.assoc]
    change arm.alphaZero (alpha ≫ (tau * q).asHom) = 0
    rw [← hcomm q, arm.alphaZero_post, map_mul, hresTau, mul_zero]
  · change residue (End.of (g ≫ tau.asHom)) = 0
    change Y ⟶ Y at g
    change residue (tau * End.of g) = 0
    rw [← hcomm (End.of g), map_mul, hresTau, mul_zero]
  · rfl
  · rfl
  · rfl
  -- betaUpper
  · change arm.betaZero (g ≫ beta) = residue (End.of g)
    exact arm.betaZero_pre (End.of g)
  · change rightIdentityCoefficient arm (g ≫ beta) = 0
    change arm.betaZero (beta ≫ (g ≫ beta)) = 0
    rw [← Category.assoc]
    calc
      arm.betaZero ((beta ≫ g) ≫ beta) =
          residue (End.of (beta ≫ g)) :=
        arm.betaZero_pre (End.of (beta ≫ g))
      _ = 0 := hThroughZZero beta g
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  -- alphaCenter
  · change middle.coefficientOne (End.of (g ≫ alpha)) = 0
    exact hThroughXOne g alpha
  · rfl
  · rfl
  · change residue (End.of (g ≫ alpha)) = 0
    exact hThroughXZero g alpha
  · rfl
  · rfl
  · rfl
  -- betaCenter
  · change arm.betaOne (g ≫ beta) = middle.coefficientOne (End.of g)
    exact arm.betaOne_pre (End.of g)
  · rfl
  · exact False.elim (hnot ⟨rfl, rfl⟩)
  · change arm.betaZero (g ≫ beta) = residue (End.of g)
    exact arm.betaZero_pre (End.of g)
  · change rightIdentityCoefficient arm (g ≫ beta) = 0
    change arm.betaZero (beta ≫ (g ≫ beta)) = 0
    rw [← Category.assoc]
    calc
      arm.betaZero ((beta ≫ g) ≫ beta) =
          residue (End.of (beta ≫ g)) :=
        arm.betaZero_pre (End.of (beta ≫ g))
      _ = 0 := hThroughZZero beta g
  · rfl
  · rfl
  -- tauLower
  · change middle.coefficientTwo (End.of (g ≫ tau.asHom)) =
      middle.coefficientOne (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientTwo (tau * End.of g) =
      middle.coefficientOne (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientTwo_mul_tau (End.of g)
  · rfl
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.alphaOne ((alpha ≫ q.asHom) ≫ tau.asHom) =
      arm.alphaZero (alpha ≫ q.asHom)
    rw [Category.assoc]
    change arm.alphaOne (alpha ≫ (tau * q).asHom) =
      arm.alphaZero (alpha ≫ q.asHom)
    rw [← hcomm q, arm.alphaOne_post, arm.alphaZero_post,
      middle.coefficientOne_mul_tau]
  · change middle.coefficientOne (End.of (g ≫ tau.asHom)) = residue (End.of g)
    change Y ⟶ Y at g
    change middle.coefficientOne (tau * End.of g) = residue (End.of g)
    rw [← hcomm (End.of g)]
    exact middle.coefficientOne_mul_tau (End.of g)
  · rfl
  · change residue (End.of (g ≫ tau.asHom)) = 0
    change Y ⟶ Y at g
    change residue (tau * End.of g) = 0
    rw [← hcomm (End.of g), map_mul, hresTau, mul_zero]
  · rcases hAlphaFactor g with ⟨q, hq⟩
    rw [hq]
    change arm.alphaZero ((alpha ≫ q.asHom) ≫ tau.asHom) = 0
    rw [Category.assoc]
    change arm.alphaZero (alpha ≫ (tau * q).asHom) = 0
    rw [← hcomm q, arm.alphaZero_post, map_mul, hresTau, mul_zero]
  -- alphaLower
  · change middle.coefficientTwo (End.of (g ≫ alpha)) = 0
    exact hThroughXTwo g alpha
  · rfl
  · change arm.alphaOne (g ≫ alpha) = 0
    exact hOuterXOne (End.of g)
  · change middle.coefficientOne (End.of (g ≫ alpha)) = 0
    exact hThroughXOne g alpha
  · rfl
  · change residue (End.of (g ≫ alpha)) = 0
    exact hThroughXZero g alpha
  · rfl

def mainPath : Quiver.Path
    (Opposite.op Vertex.rightMiddle) (Opposite.op Vertex.leftMiddle) :=
  (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaCenter)).comp
    (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaCenter))

set_option maxHeartbeats 800000 in
theorem quotient_path_eq_zero_of_leftMiddle_rightMiddle
    (r : Quiver.Path (Opposite.op Vertex.rightMiddle)
      (Opposite.op Vertex.leftMiddle)) :
    (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) = 0 := by
  rw [(path_subsingleton _ _).elim r mainPath]
  have hpath : LinearPathCategory.pathHom mainPath =
      mainComposite (k := k) := by
    unfold mainPath mainComposite freeGeneratorHom
    exact (LinearPathCategory.pathHom_comp
      (x := freeVertexObj (k := k) Vertex.leftMiddle)
      (y := freeVertexObj (k := k) Vertex.center)
      (z := freeVertexObj (k := k) Vertex.rightMiddle)
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaCenter))
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaCenter))).symm
  rw [hpath]
  exact mainComposite_zero (k := k)

/-- Left-generator compatibility after scaling by the landing quotient path.
This formulation includes the defining zero relation. -/
theorem repeatedMiddleEndpointCoefficient_left_arrow_scaled
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0)
    {a' a : Vertex} (e : a' ⟶ a) (b : Vertex)
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b)
    (r : Quiver.Path (Opposite.op b) (Opposite.op a')) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a' b ((repeatedMiddleDiagram alpha beta tau hspecial).arrow e ≫ g) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b g •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) := by
  by_cases hlanding : a' = Vertex.leftMiddle ∧ b = Vertex.rightMiddle
  · rcases hlanding with ⟨rfl, rfl⟩
    rw [quotient_path_eq_zero_of_leftMiddle_rightMiddle r]
    simp
  · rw [repeatedMiddleEndpointCoefficient_left_arrow alpha beta tau hspecial
      residue middle arm hresTau hBetaFactor hThroughXZero hThroughZZero
      hThroughZOne hThroughZTwo hOuterZOne e b hlanding g]

/-- Right-generator compatibility after scaling by the landing quotient path. -/
theorem repeatedMiddleEndpointCoefficient_right_arrow_scaled
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (a : Vertex) {b b' : Vertex} (e : b ⟶ b')
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b)
    (r : Quiver.Path (Opposite.op b') (Opposite.op a)) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b' (g ≫ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b g •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) := by
  by_cases hlanding : a = Vertex.leftMiddle ∧ b' = Vertex.rightMiddle
  · rcases hlanding with ⟨rfl, rfl⟩
    rw [quotient_path_eq_zero_of_leftMiddle_rightMiddle r]
    simp
  · rw [repeatedMiddleEndpointCoefficient_right_arrow alpha beta tau hspecial
      residue middle arm hresTau hcomm hAlphaFactor hThroughXZero hThroughXOne
      hThroughXTwo hOuterXOne hThroughZZero a e hlanding g]

private theorem arrow_target_ne_leftMiddle
    {a b : Vertex} (e : a ⟶ b) : b ≠ Vertex.leftMiddle := by
  cases e <;> intro h <;> cases h

/-- Iteration of the strict left-generator table away from the killed
landing pair. -/
theorem repeatedMiddleEndpointCoefficient_left_path
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0)
    {a a' : Vertexᵒᵖ} (p : Quiver.Path a a') (b : Vertex)
    (hnot : ¬ (a'.unop = Vertex.leftMiddle ∧ b = Vertex.rightMiddle))
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a'.unop b
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p ≫ g) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a.unop b g := by
  induction p with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.id_comp]
  | cons p e ih =>
      rw [LinearPathCategory.pathMap_cons, Category.assoc]
      exact (repeatedMiddleEndpointCoefficient_left_arrow
        alpha beta tau hspecial residue middle arm hresTau hBetaFactor
        hThroughXZero hThroughZZero hThroughZOne hThroughZTwo hOuterZOne
        e.unop b hnot _).trans (ih (by
          intro h
          exact arrow_target_ne_leftMiddle e.unop h.1))

private theorem path_source_unop_eq_rightMiddle
    {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (hb : b.unop = Vertex.rightMiddle) :
    b'.unop = Vertex.rightMiddle := by
  have hbOp : b = Opposite.op Vertex.rightMiddle := by
    simpa only [Opposite.op_unop] using congrArg Opposite.op hb
  subst b
  have hq0 := path_length_zero_of_target_rightMiddle q
  exact congrArg Opposite.unop (q.eq_of_length_zero hq0)

/-- Iteration of the strict right-generator table away from the killed
landing pair. -/
theorem repeatedMiddleEndpointCoefficient_right_path
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (a : Vertex) {b' b : Vertexᵒᵖ} (q : Quiver.Path b' b)
    (hnot : ¬ (a = Vertex.leftMiddle ∧ b'.unop = Vertex.rightMiddle))
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b'.unop
        (g ≫ LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) q) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a b.unop g := by
  induction q with
  | nil => simp only [LinearPathCategory.pathMap_nil, Category.comp_id]
  | cons q e ih =>
      rw [LinearPathCategory.pathMap_cons, ← Category.assoc]
      exact (ih (g ≫
        (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop)).trans
        (repeatedMiddleEndpointCoefficient_right_arrow
          alpha beta tau hspecial residue middle arm hresTau hcomm
          hAlphaFactor hThroughXZero hThroughXOne hThroughXTwo hOuterXOne
          hThroughZZero _ e.unop (by
            intro h
            exact hnot ⟨h.1, path_source_unop_eq_rightMiddle q h.2⟩) g)

/-- Two-sided path whiskering preserves the endpoint coefficient after
scaling by the landing quotient path. -/
theorem repeatedMiddleEndpointCoefficient_whisker_scaled
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0)
    {a' a b b' : Vertexᵒᵖ}
    (p : Quiver.Path a a')
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a.unop ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop)
    (q : Quiver.Path b' b) (r : Quiver.Path b' a') :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a'.unop b'.unop
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) q) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) =
      repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a.unop b.unop g •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) := by
  by_cases hlanding : a'.unop = Vertex.leftMiddle ∧
      b'.unop = Vertex.rightMiddle
  · rcases hlanding with ⟨ha, hb⟩
    have haOp : a' = Opposite.op Vertex.leftMiddle := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op ha
    have hbOp : b' = Opposite.op Vertex.rightMiddle := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op hb
    subst a'
    subst b'
    rw [quotient_path_eq_zero_of_leftMiddle_rightMiddle r]
    simp
  · have hmiddle : ¬ (a'.unop = Vertex.leftMiddle ∧
        b.unop = Vertex.rightMiddle) := by
      intro h
      exact hlanding ⟨h.1, path_source_unop_eq_rightMiddle q h.2⟩
    have hcoeff :
        repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
            a'.unop b'.unop
            (LinearPathCategory.pathMap
                (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
                (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p ≫
              g ≫ LinearPathCategory.pathMap
                (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
                (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) q) =
          repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
            a.unop b.unop g := by
      rw [← Category.assoc]
      calc
        _ = repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
            a'.unop b.unop
            (LinearPathCategory.pathMap
              (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
              (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p ≫ g) :=
          repeatedMiddleEndpointCoefficient_right_path
            alpha beta tau hspecial residue middle arm hresTau hcomm
            hAlphaFactor hThroughXZero hThroughXOne hThroughXTwo hOuterXOne
            hThroughZZero a'.unop q hlanding _
        _ = _ := repeatedMiddleEndpointCoefficient_left_path
          alpha beta tau hspecial residue middle arm hresTau hBetaFactor
          hThroughXZero hThroughZZero hThroughZOne hThroughZTwo hOuterZOne
          p b.unop hmiddle g
    rw [hcoeff]

/-- The endpoint coefficient is zero when the corresponding free source path
type is empty. -/
theorem repeatedMiddleEndpointCoefficient_eq_zero_of_isEmpty
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    {a b : Vertex}
    (hp : IsEmpty (Quiver.Path (Opposite.op b) (Opposite.op a)))
    (g : (repeatedMiddleDiagram alpha beta tau hspecial).object a ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object b) :
    repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
      a b g = 0 := by
  cases a <;> cases b
  -- upperMiddle
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaUpper))).elim
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaCenter)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauUpper)))).elim
  · rfl
  -- upperRight
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  -- leftMiddle
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaCenter))).elim
  · exact (hp.false mainPath).elim
  · exact (hp.false
      ((Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower)).comp
        (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaCenter)))).elim
  · rfl
  -- center
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.betaCenter))).elim
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.tauLower))).elim
  · rfl
  -- rightMiddle
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  · rfl
  -- lowerMiddle
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false Quiver.Path.nil).elim
  · rfl
  -- lowerLeft
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hp.false
      (Quiver.Hom.toPath (Quiver.Hom.op Arrow.alphaLower))).elim
  · exact (hp.false Quiver.Path.nil).elim

/-- Every path coefficient is normalized after scaling by its quotient path.
The killed path is automatic; every live path reduces by left naturality to
the appropriate identity coefficient. -/
theorem repeatedMiddleVertexCoefficient_normalized_scaled
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0)
    {a b : Vertexᵒᵖ} (p : Quiver.Path b a) :
    repeatedMiddleVertexCoefficient alpha beta tau hspecial residue middle arm p
        (LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) =
      (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) := by
  by_cases hlanding : a.unop = Vertex.leftMiddle ∧
      b.unop = Vertex.rightMiddle
  · rcases hlanding with ⟨ha, hb⟩
    have haOp : a = Opposite.op Vertex.leftMiddle := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op ha
    have hbOp : b = Opposite.op Vertex.rightMiddle := by
      simpa only [Opposite.op_unop] using congrArg Opposite.op hb
    subst a
    subst b
    rw [quotient_path_eq_zero_of_leftMiddle_rightMiddle p]
    simp
  · have hcoeff := repeatedMiddleEndpointCoefficient_left_path
        alpha beta tau hspecial residue middle arm hresTau hBetaFactor
        hThroughXZero hThroughZZero hThroughZOne hThroughZTwo hOuterZOne
        p b.unop hlanding
        (𝟙 (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop)
    have hcoeff' : repeatedMiddleEndpointCoefficient alpha beta tau hspecial
        residue middle arm a.unop b.unop
          (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p) =
        repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
          b.unop b.unop
            (𝟙 (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop) := by
      rw [← Category.comp_id (LinearPathCategory.pathMap
        (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
        (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p)]
      exact hcoeff
    change repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        a.unop b.unop
          (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) = _
    rw [hcoeff']
    have hone : repeatedMiddleEndpointCoefficient alpha beta tau hspecial
        residue middle arm b.unop b.unop
        (𝟙 (repeatedMiddleDiagram alpha beta tau hspecial).object b.unop) = 1 := by
      induction b using Opposite.rec with
      | _ b =>
          cases b
          · change residue (1 : End Y) = 1
            exact map_one residue
          · change rightIdentityCoefficient arm (1 : End Z) = 1
            change arm.betaZero (beta ≫ (1 : End Z).asHom) = 1
            calc
              arm.betaZero (beta ≫ (1 : End Z).asHom) = residue 1 := by
                simpa using arm.betaZero_pre 1
              _ = 1 := map_one residue
          · change leftIdentityCoefficient arm (1 : End X) = 1
            change arm.alphaZero ((1 : End X).asHom ≫ alpha) = 1
            calc
              arm.alphaZero ((1 : End X).asHom ≫ alpha) = residue 1 := by
                simpa using arm.alphaZero_post 1
              _ = 1 := map_one residue
          · change residue (1 : End Y) = 1
            exact map_one residue
          · change rightIdentityCoefficient arm (1 : End Z) = 1
            change arm.betaZero (beta ≫ (1 : End Z).asHom) = 1
            calc
              arm.betaZero (beta ≫ (1 : End Z).asHom) = residue 1 := by
                simpa using arm.betaZero_pre 1
              _ = 1 := map_one residue
          · change residue (1 : End Y) = 1
            exact map_one residue
          · change leftIdentityCoefficient arm (1 : End X) = 1
            change arm.alphaZero ((1 : End X).asHom ≫ alpha) = 1
            calc
              arm.alphaZero ((1 : End X).asHom ≫ alpha) = residue 1 := by
                simpa using arm.alphaZero_post 1
              _ = 1 := map_one residue
    rw [hone, one_smul]

/-- The coherent Figure-13E endpoint coefficients compile into the complete
thin quotient-path package. -/
def repeatedMiddleThinQuotientPathCoefficientData
    {X Y Z : C} (alpha : X ⟶ Y) (beta : Y ⟶ Z) (tau : End Y)
    (hspecial : alpha ≫ beta = 0)
    (residue : End Y →ₐ[k] k)
    (middle : RadicalSquareCoefficientData residue tau)
    (arm : Figure13ArmCoefficientData alpha beta residue tau middle)
    (hresTau : residue tau = 0)
    (hcomm : ∀ a : End Y, a * tau = tau * a)
    (hAlphaFactor : ∀ g : X ⟶ Y,
      ∃ a : End Y, g = alpha ≫ a.asHom)
    (hBetaFactor : ∀ g : Y ⟶ Z,
      ∃ a : End Y, g = a.asHom ≫ beta)
    (hThroughXZero : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughXOne : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughXTwo : ∀ (l : Y ⟶ X) (r : X ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hThroughZZero : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      residue (End.of (l ≫ r)) = 0)
    (hThroughZOne : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientOne (End.of (l ≫ r)) = 0)
    (hThroughZTwo : ∀ (l : Y ⟶ Z) (r : Z ⟶ Y),
      middle.coefficientTwo (End.of (l ≫ r)) = 0)
    (hOuterXOne : ∀ g : End X,
      arm.alphaOne (g.asHom ≫ alpha) = 0)
    (hOuterZOne : ∀ g : End Z,
      arm.betaOne (beta ≫ g.asHom) = 0) :
    ThinQuotientPathCoefficientData (k := k) (relationIdeal (k := k))
      ((repeatedMiddleDiagram alpha beta tau hspecial).functor (k := k)) where
  path_subsingleton := path_subsingleton
  coefficient := fun p ↦
    repeatedMiddleVertexCoefficient alpha beta tau hspecial residue middle arm p
  normalized_scaled := by
    intro U V p
    unfold DiagramData.functor
    rw [quotientLift_map_quotient]
    unfold DiagramData.freeFunctor
    rw [LinearPathCategory.lift_map_pathHom]
    change repeatedMiddleVertexCoefficient alpha beta tau hspecial residue middle arm p
        (LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) =
      (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p)
    exact repeatedMiddleVertexCoefficient_normalized_scaled
      alpha beta tau hspecial residue middle arm hresTau hBetaFactor
      hThroughXZero hThroughZZero hThroughZOne hThroughZTwo hOuterZOne p
  whisker_scaled := by
    classical
    intro U' U V V' p g q r
    change (repeatedMiddleDiagram alpha beta tau hspecial).object
        (LinearPathCategory.vertex U).unop ⟶
      (repeatedMiddleDiagram alpha beta tau hspecial).object
        (LinearPathCategory.vertex V).unop at g
    have hpmap : ((repeatedMiddleDiagram alpha beta tau hspecial).functor
          (k := k)).map
          ((quotientFunctor (k := k)).map (LinearPathCategory.pathHom p)) =
        LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p := by
      unfold DiagramData.functor
      rw [quotientLift_map_quotient]
      unfold DiagramData.freeFunctor
      rw [LinearPathCategory.lift_map_pathHom]
    have hqmap : ((repeatedMiddleDiagram alpha beta tau hspecial).functor
          (k := k)).map
          ((quotientFunctor (k := k)).map (LinearPathCategory.pathHom q)) =
        LinearPathCategory.pathMap
          (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
          (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) q := by
      unfold DiagramData.functor
      rw [quotientLift_map_quotient]
      unfold DiagramData.freeFunctor
      rw [LinearPathCategory.lift_map_pathHom]
    rw [hpmap, hqmap]
    change repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
        (LinearPathCategory.vertex U').unop
        (LinearPathCategory.vertex V').unop
        (LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) p ≫
          g ≫ LinearPathCategory.pathMap
            (fun x ↦ (repeatedMiddleDiagram alpha beta tau hspecial).object x.unop)
            (fun e ↦ (repeatedMiddleDiagram alpha beta tau hspecial).arrow e.unop) q) •
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom r) = _
    have hscaled := repeatedMiddleEndpointCoefficient_whisker_scaled
      alpha beta tau hspecial residue middle arm hresTau hcomm hAlphaFactor
      hBetaFactor hThroughXZero hThroughXOne hThroughXTwo hThroughZZero
      hThroughZOne hThroughZTwo hOuterXOne hOuterZOne p g q r
    rw [hscaled]
    by_cases hmiddle : Nonempty (Quiver.Path
        (LinearPathCategory.vertex V) (LinearPathCategory.vertex U))
    · rw [thinQuotientPathProjection_apply_of_nonempty
          (relationIdeal (k := k))
          ((repeatedMiddleDiagram alpha beta tau hspecial).functor (k := k))
          (fun s ↦ repeatedMiddleVertexCoefficient alpha beta tau hspecial
            residue middle arm s) U V hmiddle g]
      let s := Classical.choice hmiddle
      rw [(path_subsingleton _ _).elim (Classical.choice hmiddle) s]
      have hr : r = q.comp (s.comp p) := (path_subsingleton _ _).elim _ _
      subst r
      dsimp only [s]
      change repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
          (LinearPathCategory.vertex U).unop
          (LinearPathCategory.vertex V).unop g •
            (quotientFunctor (k := k)).map
              (LinearPathCategory.pathHom
                (q.comp ((Classical.choice hmiddle).comp p))) =
        (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) ≫
          (repeatedMiddleEndpointCoefficient alpha beta tau hspecial residue middle arm
            (LinearPathCategory.vertex U).unop
            (LinearPathCategory.vertex V).unop g •
              (quotientFunctor (k := k)).map
                (LinearPathCategory.pathHom (Classical.choice hmiddle))) ≫
          (quotientFunctor (k := k)).map (LinearPathCategory.pathHom q)
      have hpath :
          (quotientFunctor (k := k)).map (LinearPathCategory.pathHom p) ≫
              (quotientFunctor (k := k)).map
                (LinearPathCategory.pathHom (Classical.choice hmiddle)) ≫
            (quotientFunctor (k := k)).map (LinearPathCategory.pathHom q) =
          (quotientFunctor (k := k)).map
            (LinearPathCategory.pathHom
              (q.comp ((Classical.choice hmiddle).comp p))) := by
        rw [← Functor.map_comp, LinearPathCategory.pathHom_comp,
          ← Functor.map_comp, LinearPathCategory.pathHom_comp,
          Quiver.Path.comp_assoc]
      simp only [Linear.comp_smul, Linear.smul_comp, hpath]
    · have hmiddle' : IsEmpty (Quiver.Path
          (LinearPathCategory.vertex V) (LinearPathCategory.vertex U)) :=
        not_nonempty_iff.mp hmiddle
      rw [thinQuotientPathProjection_apply_of_isEmpty
          (relationIdeal (k := k))
          ((repeatedMiddleDiagram alpha beta tau hspecial).functor (k := k))
          (fun s ↦ repeatedMiddleVertexCoefficient alpha beta tau hspecial
            residue middle arm s) U V hmiddle' g]
      have hmiddleVertex : IsEmpty (Quiver.Path
          (Opposite.op (LinearPathCategory.vertex V).unop)
          (Opposite.op (LinearPathCategory.vertex U).unop)) := by
        simpa only [Opposite.op_unop] using hmiddle'
      have hzero := repeatedMiddleEndpointCoefficient_eq_zero_of_isEmpty
        alpha beta tau hspecial residue middle arm
        (a := (LinearPathCategory.vertex U).unop)
        (b := (LinearPathCategory.vertex V).unop) hmiddleVertex g
      rw [hzero]
      simp

end LargeIndecomposable.RoiterFigure13E
