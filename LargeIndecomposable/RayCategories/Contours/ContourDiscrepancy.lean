module

public import LargeIndecomposable.RayCategories.Contours.ContourFunction

@[expose] public section

/-!
# Contour functions induced by path realizations

For a reversed linear realization of a quiver, declare two parallel paths
related when their values are nonzero scalar multiples.  The unique scalar
relating every such pair is a genuine contour function.  Consequently
Roiter-style contour-cohomology vanishing applies directly to the scalar
discrepancies of a path realization.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.LinearPathCategory

universe u v w z

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]
variable {D : Type z} [CategoryTheory.Category D] [Preadditive D]
  [CategoryTheory.Linear k D]

/-- Two parallel paths are related when the first has nonzero realization and
is a nonzero scalar multiple of the second.  The second realization is then
automatically nonzero as well. -/
def nonzeroScalarMultiplePathRelation
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    PathContourRelation Q where
  related := fun p q ↦
    pathMap F₀ F₁ p ≠ 0 ∧
      ∃ c : kˣ, pathMap F₀ F₁ p = (c : k) • pathMap F₀ F₁ q
  symm' := by
    intro i j p q h
    obtain ⟨hp, c, hc⟩ := h
    have hq : pathMap F₀ F₁ q ≠ 0 := by
      intro hq
      apply hp
      rw [hc, hq, smul_zero]
    refine ⟨hq, c⁻¹, ?_⟩
    rw [hc, smul_smul]
    simp
  trans' := by
    intro i j p q r hpq hqr
    obtain ⟨hp, c, hc⟩ := hpq
    obtain ⟨hq, d, hd⟩ := hqr
    refine ⟨hp, c * d, ?_⟩
    rw [hc, hd, smul_smul]
    rfl

/-- The right-hand path in a nonzero scalar-multiple relation also has
nonzero realization. -/
theorem pathMap_ne_zero_right_of_related
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i j : Q} {p q : Quiver.Path i j}
    (h : (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁).related p q) :
    pathMap F₀ F₁ q ≠ 0 := by
  obtain ⟨hp, c, hc⟩ := h
  intro hq
  apply hp
  rw [hc, hq, smul_zero]

/-- The uniquely determined unit scalar relating the two paths in a contour
of the nonzero scalar-multiple relation. -/
def pathContourScalar
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (C : RelatedContour (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)) :
    kˣ :=
  Classical.choose C.property.2

/-- The chosen contour scalar realizes the defining proportionality. -/
theorem pathContourScalar_spec
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (C : RelatedContour (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)) :
    pathMap F₀ F₁ C.1.left =
      (pathContourScalar F₀ F₁ C : k) • pathMap F₀ F₁ C.1.right :=
  Classical.choose_spec C.property.2

/-- The scalar specification specialized to two explicitly related paths. -/
theorem pathContourScalar_spec_related
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    {i j : Q} (p q : Quiver.Path i j)
    (h : (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁).related p q) :
    pathMap F₀ F₁ p =
      (pathContourScalar F₀ F₁
        (relatedContour
          (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) p q h) : k) •
        pathMap F₀ F₁ q := by
  exact pathContourScalar_spec F₀ F₁
    (relatedContour
      (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) p q h)

/-- A nonzero realized right-hand path makes the contour scalar unique. -/
theorem pathContourScalar_eq_of_eq_smul
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (C : RelatedContour (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁))
    (c : kˣ)
    (h : pathMap F₀ F₁ C.1.left =
      (c : k) • pathMap F₀ F₁ C.1.right) :
    pathContourScalar F₀ F₁ C = c := by
  apply Units.ext
  apply smul_left_injective k
    (pathMap_ne_zero_right_of_related F₀ F₁ C.property)
  exact (pathContourScalar_spec F₀ F₁ C).symm.trans h

/-- The scalar discrepancies induced by one path realization form a genuine
contour function. -/
def pathContourScalarFunction
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i)) :
    contourScalarFunctionSubgroup (k := k)
      (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) := by
  refine ⟨fun C ↦ pathContourScalar F₀ F₁ C, ?_⟩
  constructor
  · intro i j p q r hpq hqr
    apply pathContourScalar_eq_of_eq_smul F₀ F₁
    change pathMap F₀ F₁ p =
      ((pathContourScalar F₀ F₁
          (relatedContour
            (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) p q hpq) *
        pathContourScalar F₀ F₁
          (relatedContour
            (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) q r hqr) : kˣ) : k) •
        pathMap F₀ F₁ r
    rw [pathContourScalar_spec_related F₀ F₁ p q hpq,
      pathContourScalar_spec_related F₀ F₁ q r hqr,
      smul_smul]
    rfl
  · intro a i j b u p q v hpq hwhisker
    apply pathContourScalar_eq_of_eq_smul F₀ F₁
    change pathMap F₀ F₁ ((u.comp p).comp v) =
      (pathContourScalar F₀ F₁
        (relatedContour
          (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁) p q hpq) : k) •
        pathMap F₀ F₁ ((u.comp q).comp v)
    simp only [pathMap_comp]
    rw [pathContourScalar_spec_related F₀ F₁ p q hpq]
    simp only [CategoryTheory.Linear.comp_smul,
      CategoryTheory.Linear.smul_comp]

/-- The underlying scalar family of the induced contour function gives the
actual proportionality between every pair of related paths. -/
theorem pathMap_eq_pathContourScalarFunction_smul
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (C : RelatedContour (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)) :
    pathMap F₀ F₁ C.1.left =
      (contourScalarFamily
        (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)
        (pathContourScalarFunction F₀ F₁) C : k) •
          pathMap F₀ F₁ C.1.right :=
  pathContourScalar_spec F₀ F₁ C

/-- If contour-function cohomology vanishes for the relation induced by one
path realization, a single arrow rescaling makes every pair of nonzero
proportional path values equal. -/
theorem exists_rescaleArrow_pathMap_eq_of_inducedContourFunctionCohomologyVanishes
    (F₀ : Q → D)
    (F₁ : ∀ {i j : Q}, (i ⟶ j) → (F₀ j ⟶ F₀ i))
    (hvanish : ContourFunctionCohomologyVanishes (k := k)
      (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)) :
    ∃ e : ArrowUnitWeight k Q,
      ∀ C : RelatedContour
          (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁),
        pathMap F₀ (rescaleArrow F₀ F₁ e.coe) C.1.left =
          pathMap F₀ (rescaleArrow F₀ F₁ e.coe) C.1.right := by
  exact exists_rescaleArrow_pathMap_eq_of_contourFunctionCohomologyVanishes
    F₀ F₁ (nonzeroScalarMultiplePathRelation (k := k) F₀ F₁)
      (pathContourScalarFunction F₀ F₁)
      (pathMap_eq_pathContourScalarFunction_smul F₀ F₁) hvanish

end LargeIndecomposable.LinearPathCategory
