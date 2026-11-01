module

public import LargeIndecomposable.RayCategories.Contours.ContourFunction

@[expose] public section

/-!
# Finite source-by-source normalization of contour functions

Isolate the global induction in Roiter's vanishing argument.  On a finite
quiver, if every contour function can be normalized at one more source while
preserving a finite set of already normalized sources, then every contour
function is exact.  The remaining representation-theoretic content is the
local source-normalization step.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- A contour function is normalized at `x` when it has value one on every
related pair of paths starting at `x`. -/
def ContourFunctionNormalizedAtSource
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R) (x : Q) : Prop :=
  ∀ {y : Q} (p q : Quiver.Path x y) (h : R.related p q),
    contourScalarFamily R c (relatedContour R p q h) = 1

/-- Simultaneous normalization at every source in a finite set. -/
def ContourFunctionNormalizedAtSources
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R) (s : Finset Q) : Prop :=
  ∀ x ∈ s, ContourFunctionNormalizedAtSource R c x

theorem contourFunctionNormalizedAtSources_mono
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {s t : Finset Q} (hst : s ⊆ t)
    (h : ContourFunctionNormalizedAtSources R c t) :
    ContourFunctionNormalizedAtSources R c s := by
  intro x hx
  exact h x (hst hx)

/-- Normalization at all vertices forces a contour function to be the identity
function. -/
theorem contourFunction_eq_one_of_normalizedAtSources_univ
    [Fintype Q] [DecidableEq Q]
    (R : PathContourRelation Q)
    (c : contourScalarFunctionSubgroup (k := k) R)
    (h : ContourFunctionNormalizedAtSources R c Finset.univ) :
    c = 1 := by
  apply Subtype.ext
  funext C
  exact h C.1.source (Finset.mem_univ _)
    C.1.left C.1.right C.property

/-- A generic finite source-by-source correction property for a predicate on a
contour function and a vertex. -/
def HasFiniteSourcePropertyStep
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (P : contourScalarFunctionSubgroup (k := k) R → Q → Prop) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R)
      (s : Finset Q) (x : Q),
    (∀ y ∈ s, P c y) →
      ∃ e : ArrowUnitWeight k Q,
        ∀ y ∈ insert x s,
          P (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) y

/-- If a vertexwise property detects the identity contour function and can be
added one source at a time by exact inverse corrections, finite induction
proves contour-cohomology vanishing. -/
theorem contourFunctionCohomologyVanishes_of_finiteSourceProperty
    [Fintype Q] [DecidableEq Q]
    (R : PathContourRelation Q)
    (P : contourScalarFunctionSubgroup (k := k) R → Q → Prop)
    (hdetect : ∀ c, (∀ x, P c x) → c = 1)
    (hstep : HasFiniteSourcePropertyStep (k := k) R P) :
    ContourFunctionCohomologyVanishes (k := k) R := by
  intro c
  have aux : ∀ todo : Finset Q,
      ∀ d : contourScalarFunctionSubgroup (k := k) R,
        (∀ x ∈ Finset.univ \ todo, P d x) →
          ∃ e : ArrowUnitWeight k Q,
            ∀ x ∈ Finset.univ,
              P (d * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) x := by
    intro todo
    induction todo using Finset.induction_on with
    | empty =>
        intro d hd
        let e : ArrowUnitWeight k Q := fun {_ _} ↦ 1
        refine ⟨e, ?_⟩
        have heq : contourFunctionCoboundaryHom (k := k) R e = 1 := by
          apply Subtype.ext
          funext C
          change pathWeightRatio e C.1.left C.1.right = 1
          simpa [e] using
            (pathWeightRatio_one (k := k) C.1.left C.1.right)
        rw [heq]
        simpa using hd
    | @insert x todo hx ih =>
        intro d hd
        obtain ⟨e, he⟩ :=
          hstep d (Finset.univ \ insert x todo) x hd
        have he' : ∀ y ∈ Finset.univ \ todo,
            P (d * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) y := by
          intro y hy
          apply he y
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hy
          by_cases hyx : y = x
          · simp [hyx]
          · simp [hyx, hy]
        obtain ⟨f, hf⟩ := ih
          (d * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) he'
        let ef : ArrowUnitWeight k Q := fun {_ _} ↦ e * f
        refine ⟨ef, ?_⟩
        have hmap :
            contourFunctionCoboundaryHom (k := k) R ef =
              contourFunctionCoboundaryHom (k := k) R e *
                contourFunctionCoboundaryHom (k := k) R f := by
          apply Subtype.ext
          funext C
          change pathWeightRatio ef C.1.left C.1.right =
            pathWeightRatio e C.1.left C.1.right *
              pathWeightRatio f C.1.left C.1.right
          simpa [ef] using
            (pathWeightRatio_mul e f C.1.left C.1.right)
        have hfamily :
            d * (contourFunctionCoboundaryHom (k := k) R ef)⁻¹ =
              (d * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) *
                (contourFunctionCoboundaryHom (k := k) R f)⁻¹ := by
          rw [hmap]
          rw [mul_inv_rev]
          ac_rfl
        rw [hfamily]
        exact hf
  have hempty : ∀ x ∈ Finset.univ \ Finset.univ, P c x := by
    intro x hx
    simp at hx
  obtain ⟨e, he⟩ := aux Finset.univ c hempty
  have hone :
      c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹ = 1 :=
    hdetect _ (fun x ↦ he x (Finset.mem_univ _))
  refine ⟨e, ?_⟩
  symm
  calc
    c = (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) *
        contourFunctionCoboundaryHom (k := k) R e := by group
    _ = 1 * contourFunctionCoboundaryHom (k := k) R e := by rw [hone]
    _ = contourFunctionCoboundaryHom (k := k) R e := one_mul _

/-- The local normalization property used in the finite global induction:
after multiplying by the inverse of one exact contour function, one can add
any chosen source to a finite protected set of normalized sources. -/
def HasSourceNormalizationStep
    [DecidableEq Q]
    (R : PathContourRelation Q) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R)
      (s : Finset Q) (x : Q),
    ContourFunctionNormalizedAtSources R c s →
      ∃ e : ArrowUnitWeight k Q,
        ContourFunctionNormalizedAtSources R
          (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹)
          (insert x s)

/-- On a finite quiver, the source-local normalization step implies genuine
contour-function cohomology vanishing.  This is the finite form of the global
vertex-by-vertex induction in Roiter's proof. -/
theorem contourFunctionCohomologyVanishes_of_hasSourceNormalizationStep
    [Fintype Q] [DecidableEq Q]
    (R : PathContourRelation Q)
    (hstep : HasSourceNormalizationStep (k := k) R) :
    ContourFunctionCohomologyVanishes (k := k) R := by
  apply contourFunctionCohomologyVanishes_of_finiteSourceProperty R
    (fun c x ↦ ContourFunctionNormalizedAtSource R c x)
  · intro c hc
    apply contourFunction_eq_one_of_normalizedAtSources_univ R c
    intro x hx
    exact hc x
  · intro c s x hs
    exact hstep c s x hs

end LargeIndecomposable
