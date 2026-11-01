module

public import LargeIndecomposable.RayCategories.Contours.Interlaced
public import Mathlib.Data.Nat.Lattice

/-!
# Depth of a nonzero morphism

The depth `d(f)` of a nonzero morphism `f` of a ray category is the maximal
length of a path of irreducible morphisms with value `f` (BGRS 8.4). In a ray
category with finitely many nonzero morphisms below each one, path lengths are
bounded by the number of nonzero morphisms below the value
(`RayCat.length_le_ncard_below`), so the depth exists, and it strictly
increases along nonzero composites with non-invertible morphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- The value of a path as a ray morphism. -/
abbrev rm {x y : RayVert P} (p : Quiver.Path x y) : RayMor P := ⟨x.out, y.out, pathVal p⟩

/-- Along a path with nonzero value, the number of nonzero morphisms below the
value exceeds the length. -/
lemma length_le_ncard_below {x : RayVert P} : ∀ {y : RayVert P} (p : Quiver.Path x y),
    pathVal p ≠ 0 → p.length < (IsRayCategory.below (rm p)).ncard + 1
  | _, .nil, _ => by simp
  | _, .cons p e, h => by
    have hp : pathVal p ≠ 0 := fun h0 ↦ h (by change pathVal p ≫ e.1 = 0; rw [h0, zero_comp])
    have ih := length_le_ncard_below p hp
    have hlt : (IsRayCategory.below (rm p)).ncard < (IsRayCategory.below (rm (p.cons e))).ncard :=
      IsRayCategory.ncard_below_lt h ⟨𝟙 _, e.1, by change pathVal p ≫ e.1 = _; simp⟩
        (IsRayCategory.not_le_left (pathVal p) e.1 h e.2.2.1)
    rw [Quiver.Path.length_cons]
    omega

/-- The depth of a morphism: the maximal length of a path with that value. -/
def depth {x y : P} (f : x ⟶ y) : ℕ :=
  sSup {n | ∃ p : Quiver.Path (RayVert.mk x) (RayVert.mk y), p.length = n ∧ pathVal p = f}

lemma bddAbove_lengths {x y : P} {f : x ⟶ y} (hf : f ≠ 0) :
    BddAbove {n | ∃ p : Quiver.Path (RayVert.mk x) (RayVert.mk y), p.length = n ∧ pathVal p = f} :=
  ⟨(IsRayCategory.below (⟨x, y, f⟩ : RayMor P)).ncard, by
    rintro n ⟨p, rfl, rfl⟩
    exact Nat.lt_succ_iff.1 (length_le_ncard_below p hf)⟩

lemma length_le_depth {x y : RayVert P} (p : Quiver.Path x y) (hp : pathVal p ≠ 0) :
    p.length ≤ depth (pathVal p) :=
  le_csSup (bddAbove_lengths hp) ⟨p, rfl, rfl⟩

lemma exists_path_depth {x y : P} {f : x ⟶ y} (hf : f ≠ 0) :
    ∃ p : Quiver.Path (RayVert.mk x) (RayVert.mk y), p.length = depth f ∧ pathVal p = f := by
  obtain ⟨p, hp⟩ := exists_path f hf
  exact Nat.sSup_mem (s := {n | ∃ p : Quiver.Path (RayVert.mk x) (RayVert.mk y),
    p.length = n ∧ pathVal p = f}) ⟨_, p, rfl, hp⟩ (bddAbove_lengths hf)

lemma length_le_depth' {x y : P} (p : Quiver.Path (RayVert.mk x) (RayVert.mk y)) {f : x ⟶ y}
    (hp : pathVal p = f) (hf : f ≠ 0) : p.length ≤ depth f := by
  subst hp
  exact length_le_depth p hf

/-- Depth strictly increases when composing with a non-invertible morphism. -/
lemma depth_lt_comp_right {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0)
    (hg : ¬IsIso g) : depth f < depth (f ≫ g) := by
  have hf : f ≠ 0 := fun h0 ↦ h (by rw [h0, zero_comp])
  have hg0 : g ≠ 0 := fun h0 ↦ h (by rw [h0, comp_zero])
  obtain ⟨p, hpl, hp⟩ := exists_path_depth hf
  obtain ⟨q, hq⟩ := exists_path g hg0
  have hql : 0 < q.length := by
    cases q with
    | nil => exact absurd (hq ▸ IsIso.id _) hg
    | cons q e => simp
  have := length_le_depth' (p.comp q) (f := f ≫ g) (by rw [pathVal_comp, hp, hq]) h
  rw [Quiver.Path.length_comp] at this
  omega

/-- Depth strictly increases when precomposing with a non-invertible morphism. -/
lemma depth_lt_comp_left {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0)
    (hf : ¬IsIso f) : depth g < depth (f ≫ g) := by
  have hf0 : f ≠ 0 := fun h0 ↦ h (by rw [h0, zero_comp])
  have hg : g ≠ 0 := fun h0 ↦ h (by rw [h0, comp_zero])
  obtain ⟨q, hql, hq⟩ := exists_path_depth hg
  obtain ⟨p, hp⟩ := exists_path f hf0
  have hpl : 0 < p.length := by
    cases p with
    | nil => exact absurd (hp ▸ IsIso.id _) hf
    | cons p e => simp
  have := length_le_depth' (p.comp q) (f := f ≫ g) (by rw [pathVal_comp, hp, hq]) h
  rw [Quiver.Path.length_comp] at this
  omega

lemma depth_le_comp_right {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0) :
    depth f ≤ depth (f ≫ g) := by
  have hf : f ≠ 0 := fun h0 ↦ h (by rw [h0, zero_comp])
  have hg0 : g ≠ 0 := fun h0 ↦ h (by rw [h0, comp_zero])
  obtain ⟨p, hpl, hp⟩ := exists_path_depth hf
  obtain ⟨q, hq⟩ := exists_path g hg0
  have := length_le_depth' (p.comp q) (f := f ≫ g) (by rw [pathVal_comp, hp, hq]) h
  rw [Quiver.Path.length_comp] at this
  omega

end RayCat

end LargeIndecomposable
