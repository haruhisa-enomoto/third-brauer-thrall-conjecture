module

public import LargeIndecomposable.RayCategories.Contours.ContourSourceNormalization

@[expose] public section

/-!
# Interlacement classes and Roiter clinging

Package the source-faithful global interface in BGRS, Section 8.3.  A contour
function clings at a source when every pair of related paths admits
representatives in the same respective interlacement classes on which the
contour value is one.  If clinging at every source detects the identity and a
local exact correction adds one source while preserving previous ones, finite
source induction gives contour-cohomology vanishing.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- An equivalence relation on parallel paths representing the
interlacement classes inside every nonzero ray.  Compatibility with a
particular ray-category realization is intentionally kept separate. -/
structure PathInterlacementRelation
    (R : PathContourRelation Q) where
  interlaced : ∀ {i j : Q},
    Quiver.Path i j → Quiver.Path i j → Prop
  refl' : ∀ {i j : Q} (p : Quiver.Path i j), interlaced p p
  symm' : ∀ {i j : Q} {p q : Quiver.Path i j},
    interlaced p q → interlaced q p
  trans' : ∀ {i j : Q} {p q r : Quiver.Path i j},
    interlaced p q → interlaced q r → interlaced p r

namespace PathInterlacementRelation

variable {R : PathContourRelation Q}

theorem refl (I : PathInterlacementRelation R)
    {i j : Q} (p : Quiver.Path i j) : I.interlaced p p :=
  I.refl' p

theorem symm (I : PathInterlacementRelation R)
    {i j : Q} {p q : Quiver.Path i j}
    (h : I.interlaced p q) : I.interlaced q p :=
  I.symm' h

theorem trans (I : PathInterlacementRelation R)
    {i j : Q} {p q r : Quiver.Path i j}
    (hpq : I.interlaced p q) (hqr : I.interlaced q r) :
    I.interlaced p r :=
  I.trans' hpq hqr

end PathInterlacementRelation

/-- A contour function clings at `x` when any two related paths starting at
`x` have representatives in their respective interlacement classes on which
the contour value is one. -/
def ContourFunctionClingsAtSource
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R) (x : Q) : Prop :=
  ∀ {y : Q} (p q : Quiver.Path x y) (_hpq : R.related p q),
    ∃ p' q' : Quiver.Path x y,
      I.interlaced p p' ∧ R.related p p' ∧
        I.interlaced q q' ∧ R.related q q' ∧
        ∃ hpq' : R.related p' q',
          contourScalarFamily R c
            (relatedContour R p' q' hpq') = 1

/-- A contour function clings to the nonzero ray selected by one path when
every other representative admits same-class replacements on which the
contour value is one.  This is the path-level form of membership in the set
`M(c)` in BGRS 8.6. -/
def ContourFunctionClingsToPath
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R)
    {x y : Q} (p : Quiver.Path x y) : Prop :=
  ∀ (q : Quiver.Path x y) (_hpq : R.related p q),
    ∃ p' q' : Quiver.Path x y,
      I.interlaced p p' ∧ R.related p p' ∧
        I.interlaced q q' ∧ R.related q q' ∧
        ∃ hpq' : R.related p' q',
          contourScalarFamily R c
            (relatedContour R p' q' hpq') = 1

/-- Clinging at a source is exactly clinging to every path beginning at that
source. -/
theorem contourFunctionClingsAtSource_iff_forall_clingsToPath
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R) (x : Q) :
    ContourFunctionClingsAtSource R I c x ↔
      ∀ {y : Q} (p : Quiver.Path x y),
        ContourFunctionClingsToPath R I c p := by
  rfl

/-- Simultaneous clinging at every source in a finite set. -/
def ContourFunctionClingsAtSources
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R) (s : Finset Q) : Prop :=
  ∀ x ∈ s, ContourFunctionClingsAtSource R I c x

/-- Full normalization is stronger than clinging: use the original paths as
their own interlacement-class representatives. -/
theorem contourFunctionClingsAtSource_of_normalizedAtSource
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (c : contourScalarFunctionSubgroup (k := k) R) (x : Q)
    (h : ContourFunctionNormalizedAtSource R c x) :
    ContourFunctionClingsAtSource R I c x := by
  intro y p q hpq
  have hpp : R.related p p := R.trans hpq (R.symm hpq)
  have hqq : R.related q q := R.trans (R.symm hpq) hpq
  exact ⟨p, q, I.refl p, hpp, I.refl q, hqq, hpq, h p q hpq⟩

/-- The depth/interlacement conclusion needed after the global induction:
clinging at every source forces the contour function to be the identity. -/
def ClingingAtEverySourceDetectsIdentity
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R) : Prop :=
  ∀ c : contourScalarFunctionSubgroup (k := k) R,
    (∀ x : Q, ContourFunctionClingsAtSource R I c x) → c = 1

/-- The remaining depth conclusion in the BGRS globalization: after a contour
function clings at every source, it is one on every related interlaced pair. -/
def EverywhereClingingTrivializesInterlacement
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R),
    (∀ x : Q, ContourFunctionClingsAtSource R I c x) →
      ∀ {i j : Q} (p q : Quiver.Path i j),
        I.interlaced p q →
          ∀ hpq : R.related p q,
            contourScalarFamily R c (relatedContour R p q hpq) = 1

/-- If everywhere clinging trivializes interlaced contours, then everywhere
clinging detects the identity contour function. -/
theorem clingingAtEverySourceDetectsIdentity_of_trivializesInterlacement
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (htrivial : EverywhereClingingTrivializesInterlacement (k := k) R I) :
    ClingingAtEverySourceDetectsIdentity (k := k) R I := by
  intro c hclings
  apply Subtype.ext
  funext C
  obtain ⟨p', q', hppI, hppR, hqqI, hqqR, hpq'R, hpq'⟩ :=
    hclings C.1.source C.1.left C.1.right C.property
  have hpp := htrivial c hclings C.1.left p' hppI hppR
  have hq'q := htrivial c hclings q' C.1.right
    (I.symm hqqI) (R.symm hqqR)
  have hpq'R' : R.related C.1.left q' := R.trans hppR hpq'R
  have hfirst := c.property.1 C.1.left p' q' hppR hpq'R
  have hfirst' :
      contourScalarFamily R c
          (relatedContour R C.1.left q' hpq'R') =
        contourScalarFamily R c
            (relatedContour R C.1.left p' hppR) *
          contourScalarFamily R c
            (relatedContour R p' q' hpq'R) := by
    simpa [contourScalarFamily] using hfirst
  have hsecond := c.property.1 C.1.left q' C.1.right
    hpq'R' (R.symm hqqR)
  have hsecond' : contourScalarFamily R c C =
      contourScalarFamily R c
          (relatedContour R C.1.left q' hpq'R') *
        contourScalarFamily R c
          (relatedContour R q' C.1.right (R.symm hqqR)) := by
    simpa [contourScalarFamily, relatedContour] using hsecond
  change contourScalarFamily R c C = (1 : kˣ)
  rw [hsecond', hfirst', hpp, hpq', hq'q]
  simp

/-- The finite form of the source-local adjustment promised by BGRS Lemma
8.6: an exact inverse correction adds one chosen source to a finite protected
set of sources where the contour function already clings. -/
def HasClingingSourceStep
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R)
      (s : Finset Q) (x : Q),
    ContourFunctionClingsAtSources R I c s →
      ∃ e : ArrowUnitWeight k Q,
        ContourFunctionClingsAtSources R I
          (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹)
          (insert x s)

/-- The exact path-level conclusion of BGRS Lemma 8.6.  One correction
preserves every ray to which the original contour function already clings and
makes it cling to every ray starting at the selected source. -/
def HasRoiterClingingPathStep
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R) : Prop :=
  ∀ (c : contourScalarFunctionSubgroup (k := k) R) (x : Q),
    ∃ e : ArrowUnitWeight k Q,
      (∀ {i j : Q} (p : Quiver.Path i j),
        ContourFunctionClingsToPath R I c p →
          ContourFunctionClingsToPath R I
            (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) p) ∧
      ∀ {y : Q} (p : Quiver.Path x y),
        ContourFunctionClingsToPath R I
          (c * (contourFunctionCoboundaryHom (k := k) R e)⁻¹) p

/-- The source-faithful path-level Roiter step supplies the finite protected-
source step needed by the global induction. -/
theorem hasClingingSourceStep_of_roiterClingingPathStep
    [DecidableEq Q]
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (hstep : HasRoiterClingingPathStep (k := k) R I) :
    HasClingingSourceStep (k := k) R I := by
  intro c s x hclings
  obtain ⟨e, hpreserve, hnew⟩ := hstep c x
  refine ⟨e, ?_⟩
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · exact hnew
  · intro y p
    exact hpreserve p (hclings z hz p)

/-- The source-faithful finite globalization of Roiter's proof.  The two
remaining combinatorial inputs are precisely the local clinging-preserving
adjustment and the fact that clinging everywhere detects the identity. -/
theorem contourFunctionCohomologyVanishes_of_clinging
    [Fintype Q] [DecidableEq Q]
    (R : PathContourRelation Q)
    (I : PathInterlacementRelation R)
    (hdetect : ClingingAtEverySourceDetectsIdentity (k := k) R I)
    (hstep : HasClingingSourceStep (k := k) R I) :
    ContourFunctionCohomologyVanishes (k := k) R := by
  apply contourFunctionCohomologyVanishes_of_finiteSourceProperty R
    (fun c x ↦ ContourFunctionClingsAtSource R I c x)
  · exact hdetect
  · intro c s x hs
    exact hstep c s x hs

end LargeIndecomposable
