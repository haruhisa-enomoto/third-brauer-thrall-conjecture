module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.SingularPath
public import LargeIndecomposable.RayCategories.Contours.RayPathInterlacement

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- A singular subpath together with the paths before and after it. -/
structure BGRSSingularSubpath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) where
  source : RayVertex (BGRSRayCategory C)
  target : RayVertex (BGRSRayCategory C)
  left : Quiver.Path i source
  middle : Quiver.Path source target
  right : Quiver.Path target j
  path_eq : p = (left.comp middle).comp right
  singular : IsBGRSLiftSingularPath middle

namespace BGRSSingularSubpath

/-- A singular path occurs as its own singular subpath. -/
def self {i j : RayVertex (BGRSRayCategory C)}
    (p : Quiver.Path i j) (hp : IsBGRSLiftSingularPath p) :
    BGRSSingularSubpath p where
  source := i
  target := j
  left := Quiver.Path.nil
  middle := p
  right := Quiver.Path.nil
  path_eq := by simp
  singular := hp

/-- A singular subpath of the middle of a singular subpath is a singular
subpath of the original path. -/
def nest {i j : RayVertex (BGRSRayCategory C)}
    {p : Quiver.Path i j} (s : BGRSSingularSubpath p)
    (t : BGRSSingularSubpath s.middle) : BGRSSingularSubpath p where
  source := t.source
  target := t.target
  left := s.left.comp t.left
  middle := t.middle
  right := t.right.comp s.right
  path_eq := by
    calc
      p = (s.left.comp s.middle).comp s.right := s.path_eq
      _ = (s.left.comp ((t.left.comp t.middle).comp t.right)).comp s.right := by
        exact congrArg (fun q ↦ (s.left.comp q).comp s.right) t.path_eq
      _ = ((s.left.comp t.left).comp t.middle).comp
          (t.right.comp s.right) := by
        simp only [Quiver.Path.comp_assoc]
  singular := t.singular

end BGRSSingularSubpath

/-- A singular path is critical when none of its singular subpaths is
strictly shorter. -/
def IsCriticalBGRSLiftSingularPath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) : Prop :=
  IsBGRSLiftSingularPath p ∧
    ∀ s : BGRSSingularSubpath p, p.length ≤ s.middle.length

/-- Source-faithful BGRS criticality: the path is singular with independent
representatives, and every contiguous subpath obtained by deleting exactly
one arrow is stable.  Such a subpath is necessarily the path with its first
or last arrow deleted. -/
def IsBGRSSourceCriticalPath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) : Prop :=
  IsBGRSSourceSingularPath p ∧
    ∀ {x y : RayVertex (BGRSRayCategory C)}
      (left : Quiver.Path i x) (middle : Quiver.Path x y)
      (right : Quiver.Path y j),
      p = (left.comp middle).comp right →
        middle.length + 1 = p.length → IsBGRSStablePath middle

/-- Every strictly shorter contiguous subpath of a critical singular path has
nonzero ray evaluation. The witnessing arrow lift for the critical path is
nonzero on the subpath; if its ray evaluation vanished, that subpath would
itself be a shorter singular subpath. -/
theorem IsCriticalBGRSLiftSingularPath.rayPathMap_ne_zero_of_subpath_of_length_lt
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsCriticalBGRSLiftSingularPath p)
    {x y : RayVertex (BGRSRayCategory C)}
    (left : Quiver.Path i x) (middle : Quiver.Path x y)
    (right : Quiver.Path y j)
    (hpath : p = (left.comp middle).comp right)
    (hlt : middle.length < p.length) :
    rayPathMap middle ≠ 0 := by
  obtain ⟨L, hLp⟩ := hp.1.2
  have hLm : L.pathMap middle ≠ 0 := by
    intro hzero
    apply hLp
    rw [hpath]
    simp only [BGRSRayArrowLift.pathMap,
      LinearPathCategory.pathMap_comp]
    change LinearPathCategory.pathMap (fun x ↦ x.obj.as)
      (fun {i j} (a : i ⟶ j) ↦ L.representative a) middle = 0 at hzero
    rw [hzero]
    simp
  intro hmiddle
  let s : BGRSSingularSubpath p :=
    { source := x
      target := y
      left := left
      middle := middle
      right := right
      path_eq := hpath
      singular := ⟨hmiddle, L, hLm⟩ }
  exact (Nat.not_le_of_gt hlt) (hp.2 s)

/-- Every proper contiguous subpath of a minimal lift-singular path is stable
in the exact occurrence-by-occurrence BGRS sense. -/
theorem IsCriticalBGRSLiftSingularPath.isBGRSStablePath_of_subpath_of_length_lt
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsCriticalBGRSLiftSingularPath p)
    {x y : RayVertex (BGRSRayCategory C)}
    (left : Quiver.Path i x) (middle : Quiver.Path x y)
    (right : Quiver.Path y j)
    (hpath : p = (left.comp middle).comp right)
    (hlt : middle.length < p.length) :
    IsBGRSStablePath middle :=
  isBGRSStablePath_of_rayPathMap_ne_zero
    (hp.rayPathMap_ne_zero_of_subpath_of_length_lt
      left middle right hpath hlt)

/-- Minimal lift-singular criticality implies the literal BGRS source
criticality used in Section 4.2. -/
theorem IsCriticalBGRSLiftSingularPath.isBGRSSourceCriticalPath
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsCriticalBGRSLiftSingularPath p) :
    IsBGRSSourceCriticalPath p := by
  refine ⟨hp.1.isBGRSSourceSingularPath, ?_⟩
  intro x y left middle right hpath hlength
  apply hp.isBGRSStablePath_of_subpath_of_length_lt
    left middle right hpath
  omega

private theorem Quiver.Path.exists_first_middle_last_of_three_le_length
    {V : Type u} [Quiver.{v} V] {i j : V} (p : Quiver.Path i j)
    (hthree : 3 ≤ p.length) :
    ∃ (x y : V) (first : i ⟶ x) (middle : Quiver.Path x y)
      (last : y ⟶ j),
      p = (first.toPath.comp middle).comp last.toPath ∧
        1 ≤ middle.length := by
  have hpne : p.length ≠ 0 := by omega
  obtain ⟨x, first, tail, hpath, hlength⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_comp p).1 hpne
  have htailtwo : 2 ≤ tail.length := by omega
  have htailne : tail.length ≠ 0 := by omega
  obtain ⟨y, middle, last, htail⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons tail).1 htailne
  refine ⟨x, y, first, middle, last, ?_, ?_⟩
  · rw [hpath, htail]
    exact Quiver.Path.comp_cons _ _ _
  · rw [htail, Quiver.Path.length_cons] at htailtwo
    omega

/-- First arrow, nonempty middle, and last arrow of a critical path of length
at least three, with a single lift witnessing the full nonzero ordinary
composite and nonzero ray evaluations of all three proper spine pieces. -/
structure BGRSCriticalPathSpine
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j) where
  leftInner : RayVertex (BGRSRayCategory C)
  rightInner : RayVertex (BGRSRayCategory C)
  first : i ⟶ leftInner
  middle : Quiver.Path leftInner rightInner
  last : rightInner ⟶ j
  path_eq : p = (first.toPath.comp middle).comp last.toPath
  middle_length_pos : 1 ≤ middle.length
  lift : BGRSRayArrowLift (C := C)
  ray_path_eq_zero : rayPathMap p = 0
  lift_path_ne_zero : lift.pathMap p ≠ 0
  middle_ray_ne_zero : rayPathMap middle ≠ 0
  prefix_ray_ne_zero : rayPathMap (first.toPath.comp middle) ≠ 0
  suffix_ray_ne_zero : rayPathMap (middle.comp last.toPath) ≠ 0

/-- The packaged first--middle--last decomposition is genuinely of length at
least three. -/
theorem BGRSCriticalPathSpine.three_le_length
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) : 3 ≤ p.length := by
  rw [spine.path_eq, Quiver.Path.length_comp,
    Quiver.Path.length_comp]
  simp only [Quiver.Path.length_toPath]
  have hmiddle := spine.middle_length_pos
  omega

/-- The lifted ordinary middle composite of a critical spine is nonzero. -/
theorem BGRSCriticalPathSpine.lift_middle_pathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    spine.lift.pathMap spine.middle ≠ 0 :=
  spine.lift.pathMap_ne_zero_of_rayPathMap_ne_zero
    spine.middle spine.middle_ray_ne_zero

/-- The lifted ordinary first--middle composite of a critical spine is
nonzero. -/
theorem BGRSCriticalPathSpine.lift_prefix_pathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    spine.lift.pathMap (spine.first.toPath.comp spine.middle) ≠ 0 :=
  spine.lift.pathMap_ne_zero_of_rayPathMap_ne_zero
    (spine.first.toPath.comp spine.middle) spine.prefix_ray_ne_zero

/-- The lifted ordinary middle--last composite of a critical spine is
nonzero. -/
theorem BGRSCriticalPathSpine.lift_suffix_pathMap_ne_zero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    spine.lift.pathMap (spine.middle.comp spine.last.toPath) ≠ 0 :=
  spine.lift.pathMap_ne_zero_of_rayPathMap_ne_zero
    (spine.middle.comp spine.last.toPath) spine.suffix_ray_ne_zero

/-- The middle of a critical spine is stable for independent choices of all
of its arrow occurrences. -/
theorem BGRSCriticalPathSpine.middle_isBGRSStablePath
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    IsBGRSStablePath spine.middle :=
  isBGRSStablePath_of_rayPathMap_ne_zero spine.middle_ray_ne_zero

/-- The first--middle proper path in a critical spine is BGRS-stable. -/
theorem BGRSCriticalPathSpine.prefix_isBGRSStablePath
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    IsBGRSStablePath (spine.first.toPath.comp spine.middle) :=
  isBGRSStablePath_of_rayPathMap_ne_zero spine.prefix_ray_ne_zero

/-- The middle--last proper path in a critical spine is BGRS-stable. -/
theorem BGRSCriticalPathSpine.suffix_isBGRSStablePath
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    IsBGRSStablePath (spine.middle.comp spine.last.toPath) :=
  isBGRSStablePath_of_rayPathMap_ne_zero spine.suffix_ray_ne_zero

/-- Reversed path evaluation identifies the full lifted critical composite
with the displayed last--middle--first threefold composite. -/
theorem BGRSCriticalPathSpine.lift_pathMap_eq_last_middle_first
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : BGRSCriticalPathSpine p) :
    spine.lift.pathMap p =
      spine.lift.representative spine.last ≫
        spine.lift.pathMap spine.middle ≫
          spine.lift.representative spine.first := by
  calc
    spine.lift.pathMap p = spine.lift.pathMap
        ((spine.first.toPath.comp spine.middle).comp spine.last.toPath) :=
      congrArg (fun q ↦ spine.lift.pathMap q) spine.path_eq
    _ = spine.lift.representative spine.last ≫
        spine.lift.pathMap spine.middle ≫
          spine.lift.representative spine.first := by
      simp only [BGRSRayArrowLift.pathMap,
        LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
        LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
        Category.comp_id]

/-- Criticality supplies the stable first--middle--last spine used at the
start of the BGRS Figure-14/15 construction. -/
theorem IsCriticalBGRSLiftSingularPath.exists_spine
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsCriticalBGRSLiftSingularPath p) (hthree : 3 ≤ p.length) :
    Nonempty (BGRSCriticalPathSpine p) := by
  obtain ⟨x, y, first, middle, last, hpath, hmiddle⟩ :=
    Quiver.Path.exists_first_middle_last_of_three_le_length p hthree
  obtain ⟨L, hLp⟩ := hp.1.2
  have hplength : p.length = middle.length + 2 := by
    rw [hpath, Quiver.Path.length_comp, Quiver.Path.length_comp]
    simp only [Quiver.Path.length_toPath]
    omega
  have hmiddlelt : middle.length < p.length := by
    rw [hplength]
    omega
  have hprefixlt : (first.toPath.comp middle).length < p.length := by
    rw [hplength, Quiver.Path.length_comp]
    simp only [Quiver.Path.length_toPath]
    omega
  have hsuffixlt : (middle.comp last.toPath).length < p.length := by
    rw [hplength, Quiver.Path.length_comp]
    simp only [Quiver.Path.length_toPath]
    omega
  refine ⟨
    { leftInner := x
      rightInner := y
      first := first
      middle := middle
      last := last
      path_eq := hpath
      middle_length_pos := hmiddle
      lift := L
      ray_path_eq_zero := hp.1.1
      lift_path_ne_zero := hLp
      middle_ray_ne_zero := hp.rayPathMap_ne_zero_of_subpath_of_length_lt
        first.toPath middle last.toPath hpath hmiddlelt
      prefix_ray_ne_zero := hp.rayPathMap_ne_zero_of_subpath_of_length_lt
        Quiver.Path.nil (first.toPath.comp middle) last.toPath
        (by simpa using hpath) hprefixlt
      suffix_ray_ne_zero := hp.rayPathMap_ne_zero_of_subpath_of_length_lt
        first.toPath (middle.comp last.toPath) Quiver.Path.nil
        (by simpa [Quiver.Path.comp_assoc] using hpath) hsuffixlt }⟩

/-- A singular path in a finite ray category has at least two arrows. -/
theorem IsBGRSLiftSingularPath.two_le_length
    [IsFiniteRayCategory (BGRSRayCategory C)]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (hp : IsBGRSLiftSingularPath p) : 2 ≤ p.length := by
  by_contra hlength
  have hcases : p.length = 0 ∨ p.length = 1 := by omega
  rcases hcases with hzero | hone
  · obtain rfl := Quiver.Path.eq_of_length_zero p hzero
    obtain rfl := Quiver.Path.eq_nil_of_length_zero p hzero
    haveI : IsIso (rayPathMap
        (Quiver.Path.nil : Quiver.Path i i)) := by
      unfold rayPathMap
      rw [LinearPathCategory.pathMap_nil]
      infer_instance
    exact ray_isIso_ne_zero (rayPathMap
      (Quiver.Path.nil : Quiver.Path i i)) hp.1
  · exact (rayPathMap_isIrreducible_of_length_eq_one p hone).1 hp.1

/-- Every singular path contains a critical singular subpath. -/
theorem exists_critical_BGRSSingularSubpath
    {i j : RayVertex (BGRSRayCategory C)} (p : Quiver.Path i j)
    (hp : IsBGRSLiftSingularPath p) :
    ∃ s : BGRSSingularSubpath p,
      IsCriticalBGRSLiftSingularPath s.middle := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ s : BGRSSingularSubpath p, s.middle.length = n
  have hP : ∃ n, P n :=
    ⟨p.length, BGRSSingularSubpath.self p hp, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hP
  refine ⟨s, s.singular, ?_⟩
  intro t
  have hnest : P t.middle.length :=
    ⟨s.nest t, rfl⟩
  rw [hs]
  exact Nat.find_min' hP hnest

/-- To prove the BGRS singular-pair factorization theorem it is enough to
show that every critical singular path has length two. -/
theorem hasBGRSSingularPairFactorization_of_critical_length_two
    (hcritical : ∀ {i j : RayVertex (BGRSRayCategory C)}
      (p : Quiver.Path i j),
      IsCriticalBGRSLiftSingularPath p → p.length = 2) :
    HasBGRSSingularPairFactorization C := by
  intro i j p hp
  obtain ⟨s, hs⟩ := exists_critical_BGRSSingularSubpath p hp
  exact ⟨s.source, s.target, s.left, s.middle, s.right,
    hcritical s.middle hs, s.singular, s.path_eq⟩

/-- Since singular paths automatically have length at least two, the source
structure theorem reduces exactly to excluding critical singular paths of
length at least three. -/
theorem hasBGRSSingularPairFactorization_of_no_long_critical
    [IsFiniteRayCategory (BGRSRayCategory C)]
    (hlong : ∀ {i j : RayVertex (BGRSRayCategory C)}
      (p : Quiver.Path i j),
      IsCriticalBGRSLiftSingularPath p → ¬3 ≤ p.length) :
    HasBGRSSingularPairFactorization C := by
  apply hasBGRSSingularPairFactorization_of_critical_length_two
  intro i j p hp
  have htwo : 2 ≤ p.length := hp.1.two_le_length
  have hnotthree : ¬3 ≤ p.length := hlong p hp
  omega

end LargeIndecomposable
