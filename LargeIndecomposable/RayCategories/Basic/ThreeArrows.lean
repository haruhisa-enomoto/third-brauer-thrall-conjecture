module

public import LargeIndecomposable.RayCategories.Basic.Star
public import LargeIndecomposable.RayCategories.Basic.Prefix
public import LargeIndecomposable.RayCategories.Contours.ContourFirst

/-!
# At most three arrows start at a point

In a ray category over which a minimal representation-infinite algebra has a
twisted multiplicative basis, and which has a non-irreducible non-invertible
nonzero morphism, at most three irreducible morphisms start at any object
(`RayQuiver.MulBasis.not_four_irr`; used in BO13a Lemmas 5 and 6).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Two irreducible morphisms out of `x`, one a prefix of the other, agree. -/
lemma eq_of_bLe_irr {x : P} {f g : BMor x} (hf : IsIrreducible f.2) (hg : IsIrreducible g.2)
    (h : BLe f g) : f = g := by
  obtain ⟨ρ, hρ⟩ := h
  rcases hg.2.2 _ _ _ hρ.symm with h1 | h1
  · exact absurd h1 hf.2.1
  · obtain ⟨hxy, rfl⟩ := eq_eqToHom_of_isIso ρ
    obtain ⟨y, f⟩ := f
    obtain ⟨y', g⟩ := g
    change y = y' at hxy
    subst hxy
    simp only [eqToHom_refl, Category.comp_id] at hρ
    rw [hρ]

/-- An irreducible morphism is not divisible by a non-irreducible
non-invertible nonzero morphism. -/
lemma not_factorsThrough_irr {a b x y : P} {τ : a ⟶ b} (hτ : ¬IsIso τ) (hτ0 : τ ≠ 0)
    (hτr : ¬IsIrreducible τ) {α : x ⟶ y} (hα : IsIrreducible α) : ¬FactorsThroughMorphism τ α := by
  rintro ⟨f, g, rfl⟩
  have : ∃ (z : P) (g' : a ⟶ z) (h' : z ⟶ b), τ = g' ≫ h' ∧ ¬IsIso g' ∧ ¬IsIso h' := by
    by_contra hc
    push_neg at hc
    exact hτr ⟨hτ0, hτ, fun z g' h' he ↦ by
      by_contra hn
      push_neg at hn
      exact hn.2 (hc z g' h' he hn.1)⟩
  obtain ⟨z, g', h', rfl, hg', hh'⟩ := this
  rcases hα.2.2 _ (f ≫ g') (h' ≫ g) (by simp [Category.assoc]) with h1 | h1
  · have hf : IsIso f := by
      rcases hα.2.2 _ f (g' ≫ h' ≫ g) (by simp [Category.assoc]) with h2 | h2
      · exact h2
      · have hne : g' ≫ h' ≠ 0 := hτ0
        have : IsIso (g' ≫ h') := by
          have h3 := isIso_of_isIso_comp (g' ≫ h') g hne (by rw [Category.assoc]; exact h2)
          exact h3
        exact absurd this hτ
    exact hg' (IsIso.of_isIso_comp_left f g')
  · have hh0 : h' ≠ 0 := fun h0 ↦ hτ0 (by rw [h0, comp_zero])
    exact hh' (isIso_of_isIso_comp h' g hh0 h1)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **At most three irreducible morphisms start at an object.** -/
theorem not_four_irr
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) (hτr : ¬IsIrreducible τ) (x : P) (α : Fin 4 → BMor x)
    (hinj : Function.Injective α) (hirr : ∀ i, IsIrreducible (α i).2) : False :=
  B.not_four_out hmin hL hR τ hτ hτ0 x α (fun i ↦ not_factorsThrough_irr hτ hτ0 hτr (hirr i))
    (fun i ↦ (hirr i).2.1) fun i j hij hg ↦ hij (hinj (eq_of_bLe_irr (hirr i) (hirr j) hg))

end MulBasis

end RayQuiver

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), first case.** Let `σ = val(α v') = val(β w')` and
`ρ = val(α' v'') = val(β' w'')` be morphisms out of `x` from two contours.
If `ρ` factors through neither `α` nor `β`, the four first arrows give four
irreducible morphisms out of `x`, which is impossible. -/
theorem not_contours_out
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x a b y a' b' y' : RayVert P}
    (α : x ⟶ a) (β : x ⟶ b) (v' : Quiver.Path a y) (w' : Quiver.Path b y)
    (hval : pathVal (α.toPath.comp v') = pathVal (β.toPath.comp w'))
    (h0 : pathVal (α.toPath.comp v') ≠ 0)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w'))
    (hτ : ¬IsIso (pathVal (α.toPath.comp v'))) (hτr : ¬IsIrreducible (pathVal (α.toPath.comp v')))
    (α' : x ⟶ a') (β' : x ⟶ b') (v'' : Quiver.Path a' y') (w'' : Quiver.Path b' y')
    (hval' : pathVal (α'.toPath.comp v'') = pathVal (β'.toPath.comp w''))
    (h0' : pathVal (α'.toPath.comp v'') ≠ 0)
    (hni' : ¬Interlaced (α'.toPath.comp v'') (β'.toPath.comp w''))
    (hα : ¬BLe (arrB α) ⟨y'.out, pathVal (α'.toPath.comp v'')⟩)
    (hβ : ¬BLe (arrB β) ⟨y'.out, pathVal (α'.toPath.comp v'')⟩) : False := by
  have hpre : ∀ {c : RayVert P} (γ : x ⟶ c) (u : Quiver.Path c y'),
      BLe (arrB γ) ⟨y'.out, pathVal (γ.toPath.comp u)⟩ := fun γ u ↦
    ⟨pathVal u, by rw [pathVal_comp, pathVal_toPath]; rfl⟩
  have hρα' : BLe (arrB α') ⟨y'.out, pathVal (α'.toPath.comp v'')⟩ := hpre α' v''
  have hρβ' : BLe (arrB β') ⟨y'.out, pathVal (α'.toPath.comp v'')⟩ := by
    rw [hval']; exact hpre β' w''
  have d1 : arrB α ≠ arrB β := fun h ↦
    not_bLe_first_of_contour hL α β v' w' hval h0 hni (h ▸ ⟨𝟙 _, Category.comp_id _⟩)
  have d2 : arrB α' ≠ arrB β' := fun h ↦
    not_bLe_first_of_contour hL α' β' v'' w'' hval' h0' hni' (h ▸ ⟨𝟙 _, Category.comp_id _⟩)
  have d3 : arrB α ≠ arrB α' := fun h ↦ hα (h ▸ hρα')
  have d4 : arrB α ≠ arrB β' := fun h ↦ hα (h ▸ hρβ')
  have d5 : arrB β ≠ arrB α' := fun h ↦ hβ (h ▸ hρα')
  have d6 : arrB β ≠ arrB β' := fun h ↦ hβ (h ▸ hρβ')
  refine B.not_four_irr hmin hL hR _ hτ h0 hτr x.out ![arrB α, arrB β, arrB α', arrB β']
    (fun i j h ↦ ?_) (fun i ↦ ?_)
  · fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · fin_cases i
    · exact α.2
    · exact β.2
    · exact α'.2
    · exact β'.2

end MulBasis

end RayQuiver

end LargeIndecomposable
