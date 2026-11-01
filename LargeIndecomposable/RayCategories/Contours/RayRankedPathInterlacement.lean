module

public import LargeIndecomposable.RayCategories.Basic.RayMorphismDepth
public import LargeIndecomposable.RayCategories.Contours.RankedPathInterlacement

@[expose] public section

/-!
# Morphism depth as a rank for ray-path interlacement

The maximal length of an irreducible-path presentation of a nonzero ray
morphism is constant on related paths and strictly increases after adding a
proper common whisker.  It therefore supplies the rank used at the end of
Roiter's clinging argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace LargeIndecomposable

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Extend ray-morphism depth by zero on paths with zero evaluation.  The
zero branch is irrelevant to related contours but makes the rank total on all
quiver paths. -/
def rayProperWhiskerPathRank [HasFiniteRayPathDepth C] :
    ProperWhiskerPathRank (rayPathContourRelation (C := C)) where
  rank := fun p ↦ if hp : rayPathMap p ≠ 0 then
    rayMorphismDepth (rayPathMorphism p hp) else 0
  rank_eq_of_related := by
    intro i j p q hpq
    have hq : rayPathMap q ≠ 0 := by
      rw [← hpq.2]
      exact hpq.1
    rw [dif_pos hpq.1, dif_pos hq]
    exact rayMorphismDepth_eq_of_related p q hpq
  inner_lt_outer := by
    intro a i j b s p q t hpq houter hproper
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    let outer := (s.comp p).comp t
    have hp : rayPathMap p ≠ 0 := hpq.1
    have houterNonzero : rayPathMap outer ≠ 0 := houter.1
    rw [dif_pos hp, dif_pos houterNonzero]
    change rayMorphismDepth (rayPathMorphism p hp) <
      rayMorphismDepth (rayPathMorphism outer houterNonzero)
    obtain ⟨r, hrLength⟩ :=
      exists_rayPathPresentation_length_eq_depth (rayPathMorphism p hp)
    let rPath : Quiver.Path (RayVertex.mk i) (RayVertex.mk j) := r.path
    have hrMap : rayPathMap rPath = rayPathMap p := by
      exact r.map_eq
    let rOuter := (s.comp rPath).comp t
    have hrOuterMap : rayPathMap rOuter = rayPathMap outer := by
      dsimp only [rOuter, outer]
      simp only [LinearPathCategory.pathMap_comp]
      change rayPathMap t ≫ rayPathMap rPath ≫ rayPathMap s =
        rayPathMap t ≫ rayPathMap p ≫ rayPathMap s
      rw [hrMap]
    have hrOuterNonzero : rayPathMap rOuter ≠ 0 := by
      rw [hrOuterMap]
      exact houterNonzero
    have hle : rOuter.length ≤
        rayMorphismDepth (rayPathMorphism outer houterNonzero) := by
      calc
        rOuter.length ≤
            rayMorphismDepth (rayPathMorphism rOuter hrOuterNonzero) :=
          rayPath_length_le_depth rOuter hrOuterNonzero
        _ = rayMorphismDepth (rayPathMorphism outer houterNonzero) :=
          rayMorphismDepth_eq_of_related rOuter outer
            ⟨hrOuterNonzero, hrOuterMap⟩
    have hrOuterLength : rOuter.length =
        s.length + rPath.length + t.length := by
      simp [rOuter, Nat.add_assoc]
    rw [hrOuterLength] at hle
    have hrPathLength : rPath.length =
        rayMorphismDepth (rayPathMorphism p hp) := by
      change r.path.length = rayMorphismDepth (rayPathMorphism p hp)
      exact hrLength
    rw [hrPathLength] at hle
    omega

/-- In a finite ray category, clinging at every source for proper-whisker
interlacement forces a contour function to be the identity. -/
theorem rayClingingAtEverySourceDetectsIdentity
    {k : Type*} [Field k]
    [Finite C] [IsFiniteRayCategory C] :
    ClingingAtEverySourceDetectsIdentity (k := k)
      (rayPathContourRelation (C := C))
      (properWhiskerInterlacementRelation
        (rayPathContourRelation (C := C))) :=
  clingingAtEverySourceDetectsIdentity_of_properWhiskerPathRank
    (rayPathContourRelation (C := C)) rayProperWhiskerPathRank

end LargeIndecomposable
