module

public import LargeIndecomposable.RayCategories.Distributive.BGRSStablePath

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- A ray-zero path which can nevertheless have nonzero ordinary composite
for some global choice of arrow representatives.  On length-two paths (whose
arrows are distinct), this is exactly the BGRS notion of a singular path. -/
def IsBGRSLiftSingularPath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) : Prop :=
  rayPathMap p = 0 ∧
    ∃ L : BGRSRayArrowLift (C := C), L.pathMap p ≠ 0

/-- A globally witnessed singular path is singular in the exact BGRS source
sense, allowing independent representatives at repeated arrow occurrences. -/
theorem IsBGRSLiftSingularPath.isBGRSSourceSingularPath
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsBGRSLiftSingularPath p) : IsBGRSSourceSingularPath p := by
  rw [isBGRSSourceSingularPath_iff]
  refine ⟨hp.1, ?_⟩
  obtain ⟨L, hL⟩ := hp.2
  refine ⟨BGRSPathRepresentative.ofArrowLift L p, ?_⟩
  simpa only [BGRSPathRepresentative.composite_ofArrowLift] using hL

/-- A chosen arrow lift annihilates every path singular with respect to
global arrow-representative choices. -/
def BGRSRayArrowLift.AnnihilatesSingularPaths
    (L : BGRSRayArrowLift (C := C)) : Prop :=
  ∀ {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j),
    IsBGRSLiftSingularPath p → L.pathMap p = 0

/-- An arrow lift annihilating all singular paths detects exactly the zero
paths of the BGRS ray category. -/
theorem BGRSRayArrowLift.pathMap_eq_zero_iff_rayPathMap_eq_zero
    (L : BGRSRayArrowLift (C := C))
    (hL : L.AnnihilatesSingularPaths)
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) :
    L.pathMap p = 0 ↔ rayPathMap p = 0 := by
  constructor
  · contrapose!
    exact L.pathMap_ne_zero_of_rayPathMap_ne_zero p
  · intro hp
    by_contra hLp
    exact hLp (hL p ⟨hp, L, hLp⟩)

/-- Source-faithful formulation of the BGRS structure theorem: every
singular path has a singular length-two subpath.  The source proves uniqueness
as well, but existence is the only part needed for normalization. -/
def HasBGRSSingularPairFactorization (C : Type u)
    [Category.{v} C] [Preadditive C]
    [HasWellDefinedBGRSRayProduct C] : Prop :=
  ∀ {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j),
    IsBGRSLiftSingularPath p →
      ∃ (x y : RayVertex (BGRSRayCategory C))
        (left : Quiver.Path i x) (pair : Quiver.Path x y)
        (right : Quiver.Path y j),
        pair.length = 2 ∧ IsBGRSLiftSingularPath pair ∧
          p = (left.comp pair).comp right

/-- It is enough to annihilate singular paths of length two once the BGRS
singular-pair factorization theorem is available. -/
theorem BGRSRayArrowLift.annihilatesSingularPaths_of_length_two
    (L : BGRSRayArrowLift (C := C))
    (hstructure : HasBGRSSingularPairFactorization C)
    (hpairs : ∀ {i j : RayVertex (BGRSRayCategory C)}
      (p : Quiver.Path i j), p.length = 2 →
        IsBGRSLiftSingularPath p → L.pathMap p = 0) :
    L.AnnihilatesSingularPaths := by
  intro i j p hp
  obtain ⟨x, y, left, pair, right, hlength, hpair, rfl⟩ :=
    hstructure p hp
  have hzero := hpairs pair hlength hpair
  change LinearPathCategory.pathMap (fun x ↦ x.obj.as)
    (fun {i j} (a : i ⟶ j) ↦ L.representative a) pair = 0 at hzero
  simp only [BGRSRayArrowLift.pathMap,
    LinearPathCategory.pathMap_comp]
  rw [hzero]
  simp

/-- Combining the BGRS structure theorem with simultaneous normalization of
singular pairs produces a source presentation which detects precisely the
zero ray paths. -/
theorem exists_BGRSRayArrowLift_pathMap_eq_zero_iff_rayPathMap_eq_zero
    (hstructure : HasBGRSSingularPairFactorization C)
    (hnormalize : ∃ L : BGRSRayArrowLift (C := C),
      ∀ {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j),
        p.length = 2 → IsBGRSLiftSingularPath p → L.pathMap p = 0) :
    ∃ L : BGRSRayArrowLift (C := C),
      ∀ {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j),
        L.pathMap p = 0 ↔ rayPathMap p = 0 := by
  obtain ⟨L, hL⟩ := hnormalize
  refine ⟨L, fun p ↦ L.pathMap_eq_zero_iff_rayPathMap_eq_zero
    (L.annihilatesSingularPaths_of_length_two hstructure hL) p⟩

end LargeIndecomposable
