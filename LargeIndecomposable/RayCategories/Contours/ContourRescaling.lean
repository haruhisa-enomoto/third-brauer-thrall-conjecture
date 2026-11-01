module

public import LargeIndecomposable.Foundations.PathCategories.LinearPathRescale
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Contour scalar families and simultaneous rescaling

Package the multiplicative coboundary used in the final step of the
multiplicative-basis standardness theorem.  An exact family of nonzero scalar
discrepancies on any collection of parallel path pairs is removed
simultaneously by one unit-valued rescaling of all quiver arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- A contour is a pair of parallel paths in a quiver. -/
structure QuiverContour (Q : Type v) [Quiver.{w} Q] where
  source : Q
  target : Q
  left : Quiver.Path source target
  right : Quiver.Path source target

namespace QuiverContour

/-- Reverse the order of the two paths in a contour. -/
def reverse (C : QuiverContour Q) : QuiverContour Q where
  source := C.source
  target := C.target
  left := C.right
  right := C.left

/-- Whisker both paths of a contour by common paths on the left and right. -/
def whisker {a b : Q} (C : QuiverContour Q)
    (p : Quiver.Path a C.source) (q : Quiver.Path C.target b) :
    QuiverContour Q where
  source := a
  target := b
  left := (p.comp C.left).comp q
  right := (p.comp C.right).comp q

end QuiverContour

/-- One nonzero scalar weight for every arrow of a quiver. -/
abbrev ArrowUnitWeight (k : Type u) [Monoid k]
    (Q : Type v) [Quiver.{w} Q] :=
  ∀ {i j : Q}, (i ⟶ j) → kˣ

/-- Regard unit-valued arrow weights as field-valued weights for linear
rescaling. -/
def ArrowUnitWeight.coe (e : ArrowUnitWeight k Q) :
    ∀ {i j : Q}, (i ⟶ j) → k :=
  fun a ↦ (e a : k)

/-- Coercing the unit-valued weight of a path to the field agrees with taking
the path weight after coercing every arrow weight. -/
theorem path_weight_arrowUnitWeight_coe
    (e : ArrowUnitWeight k Q) {i j : Q} (p : Quiver.Path i j) :
    ((p.weight e : kˣ) : k) = p.weight e.coe := by
  induction p with
  | nil => simp
  | cons p a ih =>
      simp only [Quiver.Path.weight_cons, Units.val_mul, ih,
        ArrowUnitWeight.coe]

/-- The multiplicative ratio of the weights of two parallel paths.  The
orientation is chosen so that an original relation `p = c q` is normalized
when `c = pathWeightRatio e p q`. -/
def pathWeightRatio (e : ArrowUnitWeight k Q)
    {i j : Q} (p q : Quiver.Path i j) : kˣ :=
  (p.weight e)⁻¹ * q.weight e

/-- Path-weight ratios compose transitively. -/
theorem pathWeightRatio_trans (e : ArrowUnitWeight k Q)
    {i j : Q} (p q r : Quiver.Path i j) :
    pathWeightRatio e p r =
      pathWeightRatio e p q * pathWeightRatio e q r := by
  simp only [pathWeightRatio]
  group

/-- Reversing two paths inverts their path-weight ratio. -/
theorem pathWeightRatio_reverse (e : ArrowUnitWeight k Q)
    {i j : Q} (p q : Quiver.Path i j) :
    pathWeightRatio e q p = (pathWeightRatio e p q)⁻¹ := by
  simp only [pathWeightRatio]
  group

/-- Common left and right whiskers do not change a path-weight ratio. -/
theorem pathWeightRatio_whisker (e : ArrowUnitWeight k Q)
    {a i j b : Q} (p : Quiver.Path a i)
    (v w : Quiver.Path i j) (q : Quiver.Path j b) :
    pathWeightRatio e ((p.comp v).comp q) ((p.comp w).comp q) =
      pathWeightRatio e v w := by
  simp [pathWeightRatio, Quiver.Path.weight_comp, mul_assoc, mul_comm,
    mul_left_comm]

/-- The weight of a path for the pointwise product of two arrow-weight
families is the product of its two weights. -/
theorem path_weight_mul_arrowUnitWeight (e f : ArrowUnitWeight k Q)
    {i j : Q} (p : Quiver.Path i j) :
    p.weight (e * f) = p.weight e * p.weight f := by
  induction p with
  | nil => simp
  | cons p a ih =>
      simp only [Quiver.Path.weight_cons, Pi.mul_apply, ih]
      ac_rfl

/-- The constant-one arrow family gives every path weight one. -/
theorem path_weight_one_arrowUnitWeight {i j : Q} (p : Quiver.Path i j) :
    p.weight (1 : ArrowUnitWeight k Q) = 1 := by
  induction p with
  | nil => simp
  | cons p a ih => simp [Quiver.Path.weight_cons, ih]

/-- Path-weight ratios turn pointwise products of arrow weights into
products. -/
theorem pathWeightRatio_mul (e f : ArrowUnitWeight k Q)
    {i j : Q} (p q : Quiver.Path i j) :
    pathWeightRatio (e * f) p q =
      pathWeightRatio e p q * pathWeightRatio f p q := by
  simp [pathWeightRatio, path_weight_mul_arrowUnitWeight, mul_assoc,
    mul_comm, mul_left_comm]

/-- The path-weight ratio of the constant-one arrow family is one. -/
theorem pathWeightRatio_one {i j : Q} (p q : Quiver.Path i j) :
    pathWeightRatio (1 : ArrowUnitWeight k Q) p q = 1 := by
  simp [pathWeightRatio, path_weight_one_arrowUnitWeight]

/-- The contour coboundary of one arrow-weight family. -/
def contourCoboundary (e : ArrowUnitWeight k Q)
    (C : QuiverContour Q) : kˣ :=
  pathWeightRatio e C.left C.right

theorem contourCoboundary_reverse (e : ArrowUnitWeight k Q)
    (C : QuiverContour Q) :
    contourCoboundary (k := k) e C.reverse =
      (contourCoboundary (k := k) e C)⁻¹ :=
  pathWeightRatio_reverse e C.left C.right

theorem contourCoboundary_whisker (e : ArrowUnitWeight k Q)
    {a b : Q} (C : QuiverContour Q)
    (p : Quiver.Path a C.source) (q : Quiver.Path C.target b) :
    contourCoboundary (k := k) e (C.whisker p q) =
      contourCoboundary (k := k) e C :=
  pathWeightRatio_whisker e p C.left C.right q

/-- The simultaneous contour coboundary is a homomorphism from pointwise
arrow weights to pointwise contour scalar families. -/
def contourCoboundaryHom {T : Type z}
    (contour : T → QuiverContour Q) :
    ArrowUnitWeight k Q →* (T → kˣ) where
  toFun e t := contourCoboundary (k := k) e (contour t)
  map_one' := by
    funext t
    exact pathWeightRatio_one (contour t).left (contour t).right
  map_mul' e f := by
    funext t
    exact pathWeightRatio_mul e f (contour t).left (contour t).right

/-- A unit-valued scalar family on selected contours is exact when it is the
coboundary of one global arrow-weight family. -/
def IsExactContourScalarFamily {T : Type z}
    (contour : T → QuiverContour Q) (c : T → kˣ) : Prop :=
  ∃ e : ArrowUnitWeight k Q,
    ∀ t : T, c t = contourCoboundary (k := k) e (contour t)

/-- Exact scalar families are precisely the range of the simultaneous
contour coboundary homomorphism. -/
theorem isExactContourScalarFamily_iff_mem_range {T : Type z}
    (contour : T → QuiverContour Q) (c : T → kˣ) :
    IsExactContourScalarFamily contour c ↔
      c ∈ MonoidHom.range (contourCoboundaryHom (k := k) contour) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    funext t
    exact (he t).symm
  · rintro ⟨e, he⟩
    refine ⟨e, fun t ↦ ?_⟩
    exact (congrFun he t).symm

/-- Surjectivity of the raw selected-contour coboundary means that every
unit-valued scalar assignment on the selected contours is a global
arrow-weight coboundary.  This is deliberately stronger than cohomology
vanishing, whose codomain contains only scalar families satisfying the
contour-function laws. -/
def SelectedContourCoboundarySurjective {T : Type z}
    (contour : T → QuiverContour Q) : Prop :=
  Function.Surjective (contourCoboundaryHom (k := k) contour)

theorem selectedContourCoboundarySurjective_iff_forall_isExact {T : Type z}
    (contour : T → QuiverContour Q) :
    SelectedContourCoboundarySurjective (k := k) contour ↔
      ∀ c : T → kˣ, IsExactContourScalarFamily contour c := by
  rw [SelectedContourCoboundarySurjective]
  constructor
  · intro h c
    obtain ⟨e, he⟩ := h c
    exact ⟨e, fun t ↦ (congrFun he t).symm⟩
  · intro h c
    obtain ⟨e, he⟩ := h c
    exact ⟨e, funext fun t ↦ (he t).symm⟩

/-- The coboundary identity in the field-valued form required by rescaling
the two paths of a contour. -/
theorem weight_mul_contourCoboundary
    (e : ArrowUnitWeight k Q) (C : QuiverContour Q) :
    C.left.weight e.coe * (contourCoboundary (k := k) e C : k) =
      C.right.weight e.coe := by
  rw [← path_weight_arrowUnitWeight_coe e C.left,
    ← path_weight_arrowUnitWeight_coe e C.right]
  simp only [contourCoboundary, pathWeightRatio, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

/-- Exactness supplies one arrow rescaling satisfying every contour weight
equation simultaneously. -/
theorem exists_arrowUnitWeight_weight_mul_eq_of_isExact
    {T : Type z} (contour : T → QuiverContour Q) (c : T → kˣ)
    (h : IsExactContourScalarFamily contour c) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ t : T,
        (contour t).left.weight e.coe * (c t : k) =
          (contour t).right.weight e.coe := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun t ↦ ?_⟩
  rw [he]
  exact weight_mul_contourCoboundary e (contour t)

variable {C : Type z} [CategoryTheory.Category C] [Preadditive C]
  [CategoryTheory.Linear k C]

/-- A globally exact family of scalar contour discrepancies is killed
simultaneously by one rescaling of all arrow representatives. -/
theorem LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_isExact
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {T : Type*} (contour : T → QuiverContour Q) (c : T → kˣ)
    (hcontour : ∀ t : T,
      LinearPathCategory.pathMap F₀ F₁ (contour t).left =
        (c t : k) •
          LinearPathCategory.pathMap F₀ F₁ (contour t).right)
    (hexact : IsExactContourScalarFamily contour c) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ t : T,
        LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)
            (contour t).left =
          LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)
            (contour t).right := by
  obtain ⟨e, he⟩ :=
    exists_arrowUnitWeight_weight_mul_eq_of_isExact contour c hexact
  refine ⟨e, fun t ↦ ?_⟩
  exact LinearPathCategory.pathMap_rescaleArrow_eq_of_contour
    F₀ F₁ e.coe (contour t).left (contour t).right (c t : k)
      (hcontour t) (he t)

/-- Raw surjectivity of the selected-contour coboundary turns every
simultaneous family of nonzero scalar contour discrepancies into one
normalizing arrow rescaling. -/
theorem LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_coboundarySurjective
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {T : Type*} (contour : T → QuiverContour Q) (c : T → kˣ)
    (hcontour : ∀ t : T,
      LinearPathCategory.pathMap F₀ F₁ (contour t).left =
        (c t : k) •
          LinearPathCategory.pathMap F₀ F₁ (contour t).right)
    (hsurj : SelectedContourCoboundarySurjective (k := k) contour) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ t : T,
        LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)
            (contour t).left =
          LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)
            (contour t).right := by
  apply LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_isExact
    F₀ F₁ contour c hcontour
  exact
    (selectedContourCoboundarySurjective_iff_forall_isExact contour).mp hsurj c

/-- The simultaneous normalization theorem on path-basis morphisms of the
free linear path category. -/
theorem LinearPathCategory.exists_rescaleArrow_lift_map_pathHom_eq_of_isExact
    (F₀ : Q → C)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {T : Type*} (contour : T → QuiverContour Q) (c : T → kˣ)
    (hcontour : ∀ t : T,
      (LinearPathCategory.lift (k := k) F₀ F₁).map
          (LinearPathCategory.pathHom (contour t).left :
            LinearPathCategory.obj k Q (contour t).target ⟶
              LinearPathCategory.obj k Q (contour t).source) =
        (c t : k) •
          (LinearPathCategory.lift (k := k) F₀ F₁).map
            (LinearPathCategory.pathHom (contour t).right :
              LinearPathCategory.obj k Q (contour t).target ⟶
                LinearPathCategory.obj k Q (contour t).source))
    (hexact : IsExactContourScalarFamily contour c) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ t : T,
        (LinearPathCategory.lift (k := k) F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)).map
              (LinearPathCategory.pathHom (contour t).left :
                LinearPathCategory.obj k Q (contour t).target ⟶
                  LinearPathCategory.obj k Q (contour t).source) =
          (LinearPathCategory.lift (k := k) F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe)).map
              (LinearPathCategory.pathHom (contour t).right :
                LinearPathCategory.obj k Q (contour t).target ⟶
                  LinearPathCategory.obj k Q (contour t).source) := by
  simp only [LinearPathCategory.lift_map_pathHom] at hcontour ⊢
  exact LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_isExact
    F₀ F₁ contour c hcontour hexact

end LargeIndecomposable
