module

public import LargeIndecomposable.RayCategories.Contours.ContourRescaling

@[expose] public section

/-!
# Contour functions and their cohomological vanishing target

Restrict raw scalar assignments on parallel path pairs to the subgroup
satisfying the contour-function laws: transitivity through parallel paths and
invariance under common path whiskers.  The arrow-weight coboundary lands in
this subgroup.  Surjectivity onto it is the precise formal target of Roiter's
contour-cohomology vanishing theorem.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- A symmetric, transitive relation on parallel quiver paths.  It is allowed
to be non-reflexive: in ray-category applications `related p p` expresses
that `p` has nonzero image. -/
structure PathContourRelation (Q : Type v) [Quiver.{w} Q] where
  related : ∀ {i j : Q}, Quiver.Path i j → Quiver.Path i j → Prop
  symm' : ∀ {i j : Q} {p q : Quiver.Path i j}, related p q → related q p
  trans' : ∀ {i j : Q} {p q r : Quiver.Path i j},
    related p q → related q r → related p r

namespace PathContourRelation

variable (R : PathContourRelation Q)

theorem symm {i j : Q} {p q : Quiver.Path i j}
    (h : R.related p q) : R.related q p :=
  R.symm' h

theorem trans {i j : Q} {p q r : Quiver.Path i j}
    (hpq : R.related p q) (hqr : R.related q r) : R.related p r :=
  R.trans' hpq hqr

end PathContourRelation

/-- All contours selected by one path relation. -/
abbrev RelatedContour (R : PathContourRelation Q) :=
  {C : QuiverContour Q // R.related C.left C.right}

/-- Build a selected contour directly from two related parallel paths. -/
def relatedContour (R : PathContourRelation Q)
    {i j : Q} (p q : Quiver.Path i j) (h : R.related p q) :
    RelatedContour R :=
  ⟨⟨i, j, p, q⟩, h⟩

/-- A scalar assignment satisfies the contour-function laws when ratios
compose transitively and are unchanged by common path whiskers whenever the
whiskered pair is again a selected contour. -/
def IsContourScalarFunction (R : PathContourRelation Q)
    (c : RelatedContour R → kˣ) : Prop :=
  (∀ {i j : Q} (p q r : Quiver.Path i j)
      (hpq : R.related p q) (hqr : R.related q r),
      c (relatedContour R p r (R.trans hpq hqr)) =
        c (relatedContour R p q hpq) * c (relatedContour R q r hqr)) ∧
    (∀ {a i j b : Q} (u : Quiver.Path a i)
      (p q : Quiver.Path i j) (v : Quiver.Path j b)
      (hpq : R.related p q)
      (hwhisker : R.related ((u.comp p).comp v) ((u.comp q).comp v)),
      c (relatedContour R ((u.comp p).comp v) ((u.comp q).comp v)
          hwhisker) =
        c (relatedContour R p q hpq))

/-- Unit-valued contour functions form a subgroup of all raw scalar
assignments on the selected contours. -/
def contourScalarFunctionSubgroup (R : PathContourRelation Q) :
    Subgroup (RelatedContour R → kˣ) where
  carrier := IsContourScalarFunction (k := k) R
  one_mem' := by
    constructor
    · intro i j p q r hpq hqr
      simp
    · intro a i j b u p q v hpq hwhisker
      simp
  mul_mem' := by
    intro c d hc hd
    obtain ⟨hc_trans, hc_whisker⟩ := hc
    obtain ⟨hd_trans, hd_whisker⟩ := hd
    constructor
    · intro i j p q r hpq hqr
      simp only [Pi.mul_apply, hc_trans p q r hpq hqr,
        hd_trans p q r hpq hqr]
      ac_rfl
    · intro a i j b u p q v hpq hwhisker
      simp only [Pi.mul_apply, hc_whisker u p q v hpq hwhisker,
        hd_whisker u p q v hpq hwhisker]
  inv_mem' := by
    intro c hc
    obtain ⟨hc_trans, hc_whisker⟩ := hc
    constructor
    · intro i j p q r hpq hqr
      simp only [Pi.inv_apply, hc_trans p q r hpq hqr]
      simp [mul_comm]
    · intro a i j b u p q v hpq hwhisker
      simp only [Pi.inv_apply, hc_whisker u p q v hpq hwhisker]

/-- A contour function has value one on a related path paired with itself. -/
theorem contourScalarFunction_self
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p : Quiver.Path i j) (hpp : R.related p p) :
    c.1 (relatedContour R p p hpp) = 1 := by
  have hmul := c.property.1 p p p hpp hpp
  apply mul_left_cancel (a := c.1 (relatedContour R p p hpp))
  simpa using hmul.symm

/-- Reversing a related contour inverts the value of a contour function. -/
theorem contourScalarFunction_reverse
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {i j : Q} (p q : Quiver.Path i j) (hpq : R.related p q) :
    c.1 (relatedContour R q p (R.symm hpq)) =
      (c.1 (relatedContour R p q hpq))⁻¹ := by
  have htrans := c.property.1 q p q (R.symm hpq) hpq
  have hself := contourScalarFunction_self R c q
    (R.trans (R.symm hpq) hpq)
  rw [hself] at htrans
  exact eq_inv_of_mul_eq_one_left htrans.symm

/-- The underlying raw scalar family of a contour function. -/
def contourScalarFamily (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R) :
    RelatedContour R → kˣ :=
  c

/-- Every arrow-weight coboundary satisfies the contour-function laws. -/
theorem contourCoboundary_mem_contourScalarFunctionSubgroup
    (R : PathContourRelation Q) (e : ArrowUnitWeight k Q) :
    (fun C : RelatedContour R ↦
      contourCoboundary (k := k) e C.1) ∈
      contourScalarFunctionSubgroup (k := k) R := by
  constructor
  · intro i j p q r hpq hqr
    exact pathWeightRatio_trans e p q r
  · intro a i j b u p q v hpq hwhisker
    exact pathWeightRatio_whisker e u p q v

/-- The contour-function coboundary homomorphism. -/
def contourFunctionCoboundaryHom (R : PathContourRelation Q) :
    ArrowUnitWeight k Q →*
      contourScalarFunctionSubgroup (k := k) R where
  toFun e := ⟨fun C ↦ contourCoboundary (k := k) e C.1,
    contourCoboundary_mem_contourScalarFunctionSubgroup R e⟩
  map_one' := by
    apply Subtype.ext
    funext C
    exact pathWeightRatio_one C.1.left C.1.right
  map_mul' e f := by
    apply Subtype.ext
    funext C
    exact pathWeightRatio_mul e f C.1.left C.1.right

/-- A contour function is exact when it is the coboundary of one global
arrow-weight family. -/
def IsExactContourFunction (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R) : Prop :=
  ∃ e : ArrowUnitWeight k Q,
    contourFunctionCoboundaryHom (k := k) R e = c

/-- Roiter-style contour-cohomology vanishing: every contour function, not
every raw scalar assignment, is an arrow-weight coboundary. -/
def ContourFunctionCohomologyVanishes (R : PathContourRelation Q) : Prop :=
  Function.Surjective (contourFunctionCoboundaryHom (k := k) R)

theorem contourFunctionCohomologyVanishes_iff_forall_isExact
    (R : PathContourRelation Q) :
    ContourFunctionCohomologyVanishes (k := k) R ↔
      ∀ c : contourScalarFunctionSubgroup (k := k) R,
        IsExactContourFunction R c := by
  rfl

/-- Exactness as a contour function implies exactness of its underlying raw
family on all related contours. -/
theorem isExactContourScalarFamily_of_isExactContourFunction
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (h : IsExactContourFunction R c) :
    IsExactContourScalarFamily
      (fun C : RelatedContour R ↦ C.1) (contourScalarFamily R c) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun C ↦ ?_⟩
  exact (congrArg (fun d : contourScalarFunctionSubgroup (k := k) R ↦
    (d : RelatedContour R → kˣ) C) he).symm

/-- Genuine contour-cohomology vanishing makes every contour function exact
as a raw family and hence ready for simultaneous arrow rescaling. -/
theorem exists_arrowUnitWeight_of_contourFunctionCohomologyVanishes
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (h : ContourFunctionCohomologyVanishes (k := k) R) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ C : RelatedContour R,
        contourScalarFamily R c C = contourCoboundary (k := k) e C.1 := by
  exact isExactContourScalarFamily_of_isExactContourFunction R c (h c)

variable {D : Type z} [CategoryTheory.Category D] [CategoryTheory.Preadditive D]
  [CategoryTheory.Linear k D]

/-- Roiter-style contour-cohomology vanishing feeds directly into one
simultaneous normalization of every related-path discrepancy. -/
theorem LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_contourFunctionCohomologyVanishes
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (hcontour : ∀ C : RelatedContour R,
      LinearPathCategory.pathMap F₀ F₁ C.1.left =
        (contourScalarFamily R c C : k) •
          LinearPathCategory.pathMap F₀ F₁ C.1.right)
    (hvanish : ContourFunctionCohomologyVanishes (k := k) R) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ C : RelatedContour R,
        LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe) C.1.left =
          LinearPathCategory.pathMap F₀
            (LinearPathCategory.rescaleArrow F₀ F₁ e.coe) C.1.right := by
  apply LinearPathCategory.exists_rescaleArrow_pathMap_eq_of_isExact
    F₀ F₁ (fun C : RelatedContour R ↦ C.1)
      (contourScalarFamily R c) hcontour
  exact isExactContourScalarFamily_of_isExactContourFunction R c (hvanish c)

end LargeIndecomposable
