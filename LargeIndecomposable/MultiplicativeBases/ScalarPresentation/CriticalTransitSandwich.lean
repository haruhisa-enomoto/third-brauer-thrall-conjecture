module

public import LargeIndecomposable.MultiplicativeBases.ScalarPresentation.CriticalSingularPath
public import LargeIndecomposable.RayCategories.RoiterVanishing.RoiterTransit

@[expose] public section

/-!
# Radical sandwiches at the ends of a critical BGRS path

For a critical singular path, both one-arrow truncations have nonzero ray
value while the full path has zero ray value and a nonzero ordinary lift.
Consequently the last BGRS product, in either association, is exceptional.
Unfolding that exceptional product gives the endpoint instances `P₁` and
`Pₙ₋₁` of BGRS Section 4.2: the lifted full composite is a nonzero sandwich
through the Jacobson radical at either adjacent interior vertex.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

end LargeIndecomposable

namespace LargeIndecomposable.BGRSCriticalPathSpine

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasWellDefinedBGRSRayProduct C]

/-- The ordinary full composite is the last representative followed by the
ordinary first--middle prefix composite. -/
theorem lift_pathMap_eq_last_prefix
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    spine.lift.pathMap p =
      spine.lift.representative spine.last ≫
        spine.lift.pathMap (spine.first.toPath.comp spine.middle) := by
  rw [spine.lift_pathMap_eq_last_middle_first]
  simp only [BGRSRayArrowLift.pathMap,
    LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id]

/-- The ordinary full composite is the middle--last suffix composite followed
by the first representative. -/
theorem lift_pathMap_eq_suffix_first
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    spine.lift.pathMap p =
      spine.lift.pathMap (spine.middle.comp spine.last.toPath) ≫
        spine.lift.representative spine.first := by
  rw [spine.lift_pathMap_eq_last_middle_first]
  simp only [BGRSRayArrowLift.pathMap,
    LinearPathCategory.pathMap_comp, Quiver.Hom.toPath,
    LinearPathCategory.pathMap_cons, LinearPathCategory.pathMap_nil,
    Category.comp_id, Category.assoc]

/-- The terminal association of a critical lifted path is an exceptional
BGRS product. -/
theorem terminal_isBGRSSpecialZero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    IsBGRSSpecialZero
      (spine.lift.representative spine.last)
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle)) := by
  apply isBGRSSpecialZero_of_comp_ne_zero_of_unitRay_comp_eq_zero
  · rw [← spine.lift_pathMap_eq_last_prefix]
    exact spine.lift_path_ne_zero
  · have hlastRay := spine.lift.unitRay_representative spine.last
    have hprefixRay :=
      spine.lift.unitRay_pathMap_eq_rayPathMap_of_ne_zero
        (spine.first.toPath.comp spine.middle) spine.prefix_ray_ne_zero
    rw [hlastRay, hprefixRay]
    have hzero := spine.ray_path_eq_zero
    rw [spine.path_eq] at hzero
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp,
      Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id,
      rayArrowMorphism] using hzero

/-- The initial association of a critical lifted path is an exceptional BGRS
product. -/
theorem initial_isBGRSSpecialZero
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    IsBGRSSpecialZero
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath))
      (spine.lift.representative spine.first) := by
  apply isBGRSSpecialZero_of_comp_ne_zero_of_unitRay_comp_eq_zero
  · rw [← spine.lift_pathMap_eq_suffix_first]
    exact spine.lift_path_ne_zero
  · have hsuffixRay :=
      spine.lift.unitRay_pathMap_eq_rayPathMap_of_ne_zero
        (spine.middle.comp spine.last.toPath) spine.suffix_ray_ne_zero
    have hfirstRay := spine.lift.unitRay_representative spine.first
    rw [hsuffixRay, hfirstRay]
    have hzero := spine.ray_path_eq_zero
    rw [spine.path_eq] at hzero
    simpa only [rayPathMap, LinearPathCategory.pathMap_comp,
      Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
      LinearPathCategory.pathMap_nil, Category.comp_id,
      Category.assoc, rayArrowMorphism] using hzero

/-- The `Pₙ₋₁` radical sandwich of BGRS 4.2, in the reversed projective-path
convention. -/
theorem exists_terminal_radical_sandwich
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ∃ ρ : Ring.jacobson (End spine.rightInner.obj.as),
      spine.lift.pathMap p =
          (spine.lift.representative spine.last ≫ ρ.1.asHom) ≫
            spine.lift.pathMap
              (spine.first.toPath.comp spine.middle) ∧
        (spine.lift.representative spine.last ≫ ρ.1.asHom) ≫
            spine.lift.pathMap
              (spine.first.toPath.comp spine.middle) ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := spine.terminal_isBGRSSpecialZero
  refine ⟨ρ, ?_, ?_⟩
  · rw [spine.lift_pathMap_eq_last_prefix]
    exact hρ
  · rw [← hρ, ← spine.lift_pathMap_eq_last_prefix]
    exact spine.lift_path_ne_zero

/-- The `P₁` radical sandwich of BGRS 4.2, in the reversed projective-path
convention. -/
theorem exists_initial_radical_sandwich
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    ∃ ρ : Ring.jacobson (End spine.leftInner.obj.as),
      spine.lift.pathMap p =
          (spine.lift.pathMap
              (spine.middle.comp spine.last.toPath) ≫ ρ.1.asHom) ≫
            spine.lift.representative spine.first ∧
        (spine.lift.pathMap
              (spine.middle.comp spine.last.toPath) ≫ ρ.1.asHom) ≫
            spine.lift.representative spine.first ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := spine.initial_isBGRSSpecialZero
  refine ⟨ρ, ?_, ?_⟩
  · rw [spine.lift_pathMap_eq_suffix_first]
    exact hρ
  · rw [← hρ, ← spine.lift_pathMap_eq_suffix_first]
    exact spine.lift_path_ne_zero

/-- Choose a zero representative pair at the terminal association while
retaining the nonzero `Pₙ₋₁` radical sandwich. -/
theorem terminalZeroPairRadicalSandwich
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (BGRSZeroPairRadicalSandwich
      (spine.lift.representative spine.last)
      (spine.lift.pathMap (spine.first.toPath.comp spine.middle))) := by
  let f := spine.lift.representative spine.last
  let g := spine.lift.pathMap (spine.first.toPath.comp spine.middle)
  obtain ⟨f', g', hf', hg', hzero⟩ :=
    (HasBGRSPairDichotomy.pair f g).zero_representatives_of_special
      spine.terminal_isBGRSSpecialZero
  have hbase : HasNonzeroJacobsonSandwich f g := by
    obtain ⟨ρ, -, hρ⟩ := spine.exists_terminal_radical_sandwich
    exact ⟨ρ, hρ⟩
  exact ⟨
    { left := f'
      right := g'
      left_unitRayEquivalent := hf'
      right_unitRayEquivalent := hg'
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent hf' hg' hbase }⟩

/-- Choose a zero representative pair at the initial association while
retaining the nonzero `P₁` radical sandwich. -/
theorem initialZeroPairRadicalSandwich
    [HasBGRSPairDichotomy C]
    {i j : RayVertex (BGRSRayCategory C)} {p : Quiver.Path i j}
    (spine : LargeIndecomposable.BGRSCriticalPathSpine p) :
    Nonempty (BGRSZeroPairRadicalSandwich
      (spine.lift.pathMap (spine.middle.comp spine.last.toPath))
      (spine.lift.representative spine.first)) := by
  let f := spine.lift.pathMap (spine.middle.comp spine.last.toPath)
  let g := spine.lift.representative spine.first
  obtain ⟨f', g', hf', hg', hzero⟩ :=
    (HasBGRSPairDichotomy.pair f g).zero_representatives_of_special
      spine.initial_isBGRSSpecialZero
  have hbase : HasNonzeroJacobsonSandwich f g := by
    obtain ⟨ρ, -, hρ⟩ := spine.exists_initial_radical_sandwich
    exact ⟨ρ, hρ⟩
  exact ⟨
    { left := f'
      right := g'
      left_unitRayEquivalent := hf'
      right_unitRayEquivalent := hg'
      comp_eq_zero := hzero
      nonzero_sandwich :=
        hasNonzeroJacobsonSandwich_of_unitRayEquivalent hf' hg' hbase }⟩

end LargeIndecomposable.BGRSCriticalPathSpine
