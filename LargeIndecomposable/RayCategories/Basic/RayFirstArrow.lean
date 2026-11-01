module

public import LargeIndecomposable.RayCategories.Basic.Prefix

/-!
# First arrows of paths

`RayCat.IsFirst v α`: the path `v` starts at `b` with the arrow of value `α`.
Paths from `b` with equal nonzero value and the same first arrow are
interlaced (left cancellation), and interlacing steps with a nontrivial
prefix keep the first arrow.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits

universe v u

namespace RayCat

/-- The first arrow of a path. -/
def firstE {V : Type*} [Quiver V] {a : V} : ∀ {z : V}, Quiver.Path a z → Option (Σ c, a ⟶ c)
  | _, .nil => none
  | _, .cons .nil e => some ⟨_, e⟩
  | _, .cons (.cons p e') _ => firstE (p.cons e')

lemma firstE_cons {V : Type*} [Quiver V] {a y z : V} (p : Quiver.Path a y) (hp : 0 < p.length)
    (e : y ⟶ z) : firstE (p.cons e) = firstE p := by
  cases p with
  | nil => simp at hp
  | cons p e' => rfl

lemma firstE_toPath_comp {V : Type*} [Quiver V] {a c z : V} (e : a ⟶ c)
    (v : Quiver.Path c z) : firstE (e.toPath.comp v) = some ⟨c, e⟩ := by
  induction v with
  | nil => rfl
  | cons v f ih => rw [Quiver.Path.comp_cons, firstE_cons _ (by simp), ih]

variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P]

/-- `α` is the first arrow of `v`. -/
def IsFirst {b : P} {z : RayVert P} (v : Quiver.Path (RayVert.mk b) z) (α : BMor b) : Prop :=
  ∃ (e : RayVert.mk b ⟶ RayVert.mk α.1) (v' : Quiver.Path (RayVert.mk α.1) z),
    e.1 = α.2 ∧ v = e.toPath.comp v'

lemma exists_isFirst {b : P} {z : RayVert P} (v : Quiver.Path (RayVert.mk b) z)
    (hv : 0 < v.length) : ∃ α, IsFirst v α := by
  obtain ⟨c, e, v', -, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ v
    (Nat.succ_pred_eq_of_pos hv).symm
  exact ⟨⟨c, e.1⟩, e, v', rfl, rfl⟩

lemma IsFirst.isIrreducible {b : P} {z : RayVert P} {v : Quiver.Path (RayVert.mk b) z}
    {α : BMor b} (h : IsFirst v α) : IsIrreducible α.2 := by
  obtain ⟨e, v', he, -⟩ := h
  rw [← he]
  exact e.2

lemma IsFirst.bLe {b : P} {z : RayVert P} {v : Quiver.Path (RayVert.mk b) z}
    {α : BMor b} (h : IsFirst v α) : BLe α ⟨z.out, pathVal v⟩ := by
  obtain ⟨e, v', he, rfl⟩ := h
  refine ⟨pathVal v', ?_⟩
  change _ = pathVal (e.toPath.comp v')
  rw [pathVal_comp, pathVal_toPath, he]

lemma IsFirst.comp {b : P} {z z' : RayVert P} {v : Quiver.Path (RayVert.mk b) z}
    {α : BMor b} (h : IsFirst v α) (q : Quiver.Path z z') : IsFirst (v.comp q) α := by
  obtain ⟨e, v', he, rfl⟩ := h
  exact ⟨e, v'.comp q, he, Quiver.Path.comp_assoc _ _ _⟩

lemma IsFirst.length_pos {b : P} {z : RayVert P} {v : Quiver.Path (RayVert.mk b) z}
    {α : BMor b} (h : IsFirst v α) : 0 < v.length := by
  obtain ⟨e, v', -, rfl⟩ := h
  simp

lemma IsFirst.unique {b : P} {z : RayVert P} {v : Quiver.Path (RayVert.mk b) z}
    {α α' : BMor b} (h : IsFirst v α) (h' : IsFirst v α') : α = α' := by
  obtain ⟨e, v₁, he, rfl⟩ := h
  obtain ⟨e', v₂, he', hv⟩ := h'
  have h1 := firstE_toPath_comp e v₁
  rw [hv, firstE_toPath_comp] at h1
  obtain ⟨y, f⟩ := α
  obtain ⟨y', f'⟩ := α'
  have h2 := Option.some.inj h1
  have hy : y' = y := congrArg (fun s ↦ RayVert.out s.1) h2
  subst hy
  have h3 : e' = e := eq_of_heq (Sigma.mk.inj h2).2
  subst h3
  change e'.1 = f at he
  change e'.1 = f' at he'
  rw [← he, ← he']

/-- Paths from `b` with the same first arrow and equal nonzero value are
interlaced. -/
lemma interlaced_of_isFirst (hL : LeftCancel P) {b : P} {z : RayVert P}
    {v w : Quiver.Path (RayVert.mk b) z} {α : BMor b} (hv : IsFirst v α) (hw : IsFirst w α)
    (hvw : pathVal v = pathVal w) (h0 : pathVal v ≠ 0) : Interlaced v w := by
  obtain ⟨e, v', he, rfl⟩ := hv
  obtain ⟨e', w', he', rfl⟩ := hw
  have hee : e = e' := Subtype.ext (he.trans he'.symm)
  subst hee
  refine Relation.EqvGen.rel _ _ ?_
  have h1 : e.1 ≫ pathVal v' = e.1 ≫ pathVal w' := by
    rwa [pathVal_comp, pathVal_comp, pathVal_toPath] at hvw
  refine ⟨_, _, e.toPath, v', w', .nil, rfl, rfl, hL _ _ _ h1 ?_, ?_, Or.inl (by simp)⟩
  · rwa [pathVal_comp, pathVal_toPath] at h0
  · intro h
    apply h0
    rw [pathVal_comp, h, comp_zero]

end RayCat

end LargeIndecomposable
