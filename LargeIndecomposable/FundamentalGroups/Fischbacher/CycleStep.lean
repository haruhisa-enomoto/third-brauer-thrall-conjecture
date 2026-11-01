module

public import LargeIndecomposable.FundamentalGroups.Fischbacher.Lemma42

/-!
# No oriented cycles after adding arrows at one point

Fischbacher, Satz 5.1, first paragraph, in abstract form. Some arrows of a ray category are
"new", all starting at one point `β`; for each new arrow `e : β → δ` there are old paths
`u : β ⇝ γ` and `uₑ : δ ⇝ γ` with `e uₑ = u ≠ 0`. If the old arrows form no oriented cycle
and every old path `z : δ ⇝ β` satisfies `z u = uₑ` (Lemma 4.2 in the old category), there is
no oriented cycle at all (`cycleFree_of_step`): an oriented cycle gives a closed path `e z` at
`β` with `z` old, and then `(e z) u = u`, contradicting nilpotency.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits

universe v u

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [IsRayCategory A]
  (isNew : ∀ {x y : RayVert A}, (x ⟶ y) → Prop)

/-- A path without new arrows. -/
def OldPath {x : RayVert A} : ∀ {y : RayVert A}, Quiver.Path x y → Prop
  | _, .nil => True
  | _, .cons p e => OldPath p ∧ ¬isNew e

variable {isNew} {β : A} (hsrc : ∀ {x y : RayVert A} (e : x ⟶ y), isNew e → x = RayVert.mk β)
include hsrc

/-- The last new arrow of a path. -/
lemma exists_last_new {a : RayVert A} : ∀ {b : RayVert A} (p : Quiver.Path a b),
    ¬OldPath isNew p → ∃ (y : RayVert A) (p₁ : Quiver.Path a (RayVert.mk β))
      (e : RayVert.mk β ⟶ y) (z : Quiver.Path y b), isNew e ∧ OldPath isNew z ∧
        p = (p₁.cons e).comp z
  | _, .nil, h => absurd trivial h
  | _, .cons (b := b') p e, h => by
    by_cases he : isNew e
    · obtain rfl := hsrc e he
      exact ⟨_, p, e, .nil, he, trivial, rfl⟩
    · have hp : ¬OldPath isNew p := fun hp ↦ h ⟨hp, he⟩
      obtain ⟨y, p₁, e', z, he', hz, rfl⟩ := exists_last_new p hp
      exact ⟨y, p₁, e', z.cons e, he', ⟨hz, he⟩, rfl⟩

omit hsrc in
lemma oldPath_comp {x y : RayVert A} {p : Quiver.Path x y} (hp : OldPath isNew p) :
    ∀ {z : RayVert A} {q : Quiver.Path y z}, OldPath isNew q → OldPath isNew (p.comp q)
  | _, .nil, _ => hp
  | _, .cons q _, hq => ⟨oldPath_comp hp hq.1, hq.2⟩

/-- **No oriented cycles after adding arrows at one point.** -/
theorem cycleFree_of_step
    (hold : ∀ (x : RayVert A) (p : Quiver.Path x x), OldPath isNew p → p.length = 0)
    (hdata : ∀ {y : RayVert A} (e : RayVert.mk β ⟶ y), isNew e →
      ∃ (γ : RayVert A) (u : Quiver.Path (RayVert.mk β) γ) (uₑ : Quiver.Path y γ),
        e.1 ≫ pathVal uₑ = pathVal u ∧ pathVal u ≠ 0 ∧
          ∀ z : Quiver.Path y (RayVert.mk β), OldPath isNew z → pathVal (z.comp u) = pathVal uₑ) :
    ∀ (x : RayVert A) (p : Quiver.Path x x), p.length = 0 := by
  intro x p
  by_contra hlen
  by_cases hp : OldPath isNew p
  · exact hlen (hold x p hp)
  obtain ⟨y, p₁, e, z, he, hz, rfl⟩ := exists_last_new hsrc p hp
  have hcyc : ∃ (y' : RayVert A) (e' : RayVert.mk β ⟶ y') (z' : Quiver.Path y' (RayVert.mk β)),
      isNew e' ∧ OldPath isNew z' := by
    by_cases hp₁ : OldPath isNew p₁
    · exact ⟨y, e, z.comp p₁, he, oldPath_comp hz hp₁⟩
    · obtain ⟨y₂, p₂, e₂, z₂, he₂, hz₂, -⟩ := exists_last_new hsrc p₁ hp₁
      exact ⟨y₂, e₂, z₂, he₂, hz₂⟩
  obtain ⟨y', e', z', he', hz'⟩ := hcyc
  obtain ⟨γ, u, uₑ, h1, h0, h42⟩ := hdata e' he'
  have hz'u := h42 z' hz'
  let C : β ⟶ β := e'.1 ≫ pathVal z'
  have hCu : C ≫ pathVal u = pathVal u := by
    change (e'.1 ≫ pathVal z') ≫ pathVal u = pathVal u
    rw [Category.assoc, ← pathVal_comp, hz'u, h1]
  have hCne : C ≠ 𝟙 β := by
    intro hC
    have hni := not_isIso_pathVal (e'.toPath.comp z') (by simp)
    rw [pathVal_comp, pathVal_toPath] at hni
    exact hni (by change IsIso C; rw [hC]; infer_instance)
  obtain ⟨n, hn⟩ := IsRayCategory.nil β C hCne
  have hpow : ∀ k, rpow C k ≫ pathVal u = pathVal u := by
    intro k
    induction k with
    | zero => exact Category.id_comp _
    | succ k ih => rw [rpow_succ, Category.assoc, hCu, ih]
  apply h0
  rw [← hpow n, hn, zero_comp]

/-- A path ending at `β` without returning to `β` is old. -/
lemma oldPath_of_cycleFree (hcf : ∀ (x : RayVert A) (p : Quiver.Path x x), p.length = 0)
    {a : RayVert A} (p : Quiver.Path a (RayVert.mk β)) : OldPath isNew p := by
  by_contra hp
  obtain ⟨y, p₁, e, z, -, -, -⟩ := exists_last_new hsrc p hp
  have := hcf _ ((Quiver.Path.nil.cons e).comp z)
  simp at this

/-- **Interval-finiteness after adding finitely many arrows at one point.** -/
theorem intervalFinite_of_step (hcf : ∀ (x : RayVert A) (p : Quiver.Path x x), p.length = 0)
    (hold : ∀ a b : A, {z : A | (∃ p : Quiver.Path (RayVert.mk a) (RayVert.mk z),
      OldPath isNew p) ∧ ∃ q : Quiver.Path (RayVert.mk z) (RayVert.mk b), OldPath isNew q}.Finite)
    (a b : A) :
    (interval a b).Finite := by
  classical
  -- targets of new arrows
  let T : Set A := {d | ∃ e : RayVert.mk β ⟶ RayVert.mk d, isNew e}
  have hT : T.Finite := (IsRayCategory.finite_out β).subset fun d ⟨e, _⟩ ↦ ⟨e.1, e.2.1⟩
  refine (((hold a b).union (hold a β)).union (hT.biUnion fun d _ ↦ hold d b)).subset ?_
  rintro z ⟨⟨p⟩, ⟨q⟩⟩
  by_cases hp : OldPath isNew p
  · by_cases hq : OldPath isNew q
    · exact Or.inl (Or.inl ⟨⟨p, hp⟩, ⟨q, hq⟩⟩)
    · obtain ⟨y, q₁, e, q₂, -, -, -⟩ := exists_last_new hsrc q hq
      exact Or.inl (Or.inr ⟨⟨p, hp⟩, ⟨q₁, oldPath_of_cycleFree hsrc hcf q₁⟩⟩)
  · obtain ⟨y, p₁, e, p₂, he, hp₂, -⟩ := exists_last_new hsrc p hp
    by_cases hq : OldPath isNew q
    · exact Or.inr (Set.mem_biUnion (x := y.out) ⟨e, he⟩ ⟨⟨p₂, hp₂⟩, ⟨q, hq⟩⟩)
    · obtain ⟨y', q₁, e', q₂, -, -, -⟩ := exists_last_new hsrc q hq
      have := hcf _ (((Quiver.Path.nil.cons e).comp p₂).comp q₁)
      simp at this

end LargeIndecomposable.RayCat
