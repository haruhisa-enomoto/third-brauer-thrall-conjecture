module

public import LargeIndecomposable.Crowns.Lemma6.Symmetries

/-!
# Maximal suffixes and prefixes of contour paths (BO13a Lemma 6, case II)

* `RayCat.exists_max_suffix`: if `f` factors through the value of a suffix of a
  path `v` but not through the value of `v`, there is a split
  `v = (p₁ e) p₂` with `f` factoring through `p₂` but not through `e p₂`
  (BO13a's "appropriate decomposition").
* `MulBasis.l6_not_prefix_w`, `l6_not_prefix_w'`: `ρ` does not factor through a
  nonempty prefix of the path `β w`, `σ` not through one of `β' w'`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- **A maximal suffix through which `f` factors.** -/
lemma exists_max_suffix {x y : RayVert P} {z : P} (f : z ⟶ y.out) :
    ∀ {w : RayVert P} (p : Quiver.Path x w) (q : Quiver.Path w y), 0 < q.length →
      (∃ g, g ≫ pathVal q = f) → (¬∃ g, g ≫ pathVal (p.comp q) = f) →
      ∃ (w'' w' : RayVert P) (p₁ : Quiver.Path x w'') (e : w'' ⟶ w') (p₂ : Quiver.Path w' y),
        (p₁.cons e).comp p₂ = p.comp q ∧ 0 < p₂.length ∧ (∃ g, g ≫ pathVal p₂ = f) ∧
          ¬∃ g, g ≫ e.1 ≫ pathVal p₂ = f := by
  intro w p
  induction p with
  | nil =>
    intro q _ hq hpq
    exact absurd (by simpa using hq) hpq
  | cons p' e ih =>
    intro q hql hq hpq
    by_cases h : ∃ g, g ≫ e.1 ≫ pathVal q = f
    · have e1 : (p'.cons e).comp q = p'.comp (e.toPath.comp q) := by
        rw [← Quiver.Path.comp_assoc]; rfl
      obtain ⟨w'', w', p₁, e', p₂, h1, h2, h3, h4⟩ := ih (e.toPath.comp q) (by simp)
        (by obtain ⟨g, hg⟩ := h; exact ⟨g, by rw [pathVal_comp, pathVal_toPath]; exact hg⟩)
        (by rw [← e1]; exact hpq)
      exact ⟨w'', w', p₁, e', p₂, by rw [h1, e1], h2, h3, h4⟩
    · exact ⟨_, _, p', e, q, rfl, hql, hq, h⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `ρ` does not factor through a nonempty prefix of `β w`. -/
theorem l6_not_prefix_w
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {c : RayVert P} (p₁ : Quiver.Path (RayVert.mk x) c)
    (p₂ : Quiver.Path c (RayVert.mk y₀)) (hp : p₁.comp p₂ = D.β.toPath.comp D.w)
    (hp₁ : 0 < p₁.length) : ¬∃ g, pathVal p₁ ≫ g = ρ := by
  rintro ⟨g, hg⟩
  have hσp : pathVal (p₁.comp p₂) = σ := by rw [hp, D.hσw]
  have hv0 : pathVal p₁ ≠ 0 := fun h ↦ hσ0 (by rw [← hσp, pathVal_comp, h, zero_comp])
  obtain ⟨c', α', p₁', rfl⟩ := exists_first_arrow p₁ (not_isIso_pathVal p₁ hp₁)
  have hval : pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) =
      pathVal (α'.toPath.comp (p₁'.comp p₂)) := by
    rw [← Quiver.Path.comp_assoc, D.hσu, ← Quiver.Path.comp_assoc, hσp]
  have hni : ¬Interlaced (D.α.toPath.comp (D.χ.comp D.u₂)) (α'.toPath.comp (p₁'.comp p₂)) := by
    rw [← Quiver.Path.comp_assoc, ← Quiver.Path.comp_assoc, hp]; exact D.hniσ
  have e : pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) = σ := by
    rw [← Quiver.Path.comp_assoc, D.hσu]
  refine B.not_factors_both hmin hL hR D.α α' (D.χ.comp D.u₂) (p₁'.comp p₂) hval
    (by rw [e]; exact hσ0) hni ⟨y₁, ρ⟩ hρ0 ?_ ?_ ?_ ?_
  · rintro ⟨c'', hc⟩
    rw [e] at hc
    exact hv1 ⟨c'', hc⟩
  · rintro ⟨c'', hc⟩
    change ρ ≫ c'' = pathVal (D.α.toPath.comp (D.χ.comp D.u₂)) at hc
    rw [e] at hc
    exact hv2 ⟨c'', hc⟩
  · refine ⟨pathVal D.χ ≫ D.U', ?_⟩
    change D.α.1 ≫ pathVal D.χ ≫ D.U' = ρ
    have := D.ψU'
    simp only [L6Data.ψ] at this
    rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc] at this
    exact this
  · refine ⟨pathVal p₁' ≫ g, ?_⟩
    change α'.1 ≫ pathVal p₁' ≫ g = ρ
    rw [← hg, pathVal_comp α'.toPath p₁', pathVal_toPath, Category.assoc]

include B in
/-- `σ` does not factor through a nonempty prefix of `β' w'`. -/
theorem l6_not_prefix_w'
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (D : L6Data σ ρ) {c : RayVert P} (p₁ : Quiver.Path (RayVert.mk x) c)
    (p₂ : Quiver.Path c (RayVert.mk y₁)) (hp : p₁.comp p₂ = D.β'.toPath.comp D.w')
    (hp₁ : 0 < p₁.length) : ¬∃ g, pathVal p₁ ≫ g = σ :=
  B.l6_not_prefix_w hmin hL hR hρ0 hσ0 hv2 hv1 D.swap p₁ p₂ hp hp₁

end MulBasis

end RayQuiver

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- A split `β w = p₁ p₂` of the contour path of `σ` into nonempty parts. -/
structure L6WSplit {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (D : L6Data σ ρ) where
  c : RayVert P
  p₁ : Quiver.Path (RayVert.mk x) c
  p₂ : Quiver.Path c (RayVert.mk y₀)
  hp : p₁.comp p₂ = D.β.toPath.comp D.w
  hp₁ : 0 < p₁.length
  hp₂ : 0 < p₂.length

namespace L6WSplit

variable [IsRayCategory P] {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} {D : L6Data σ ρ}
  (S : L6WSplit D)

/-- `w₁`. -/
abbrev w₁ : x ⟶ S.c.out := pathVal S.p₁
/-- `w₂`. -/
abbrev w₂ : S.c.out ⟶ y₀ := pathVal S.p₂

lemma w₁w₂ : S.w₁ ≫ S.w₂ = σ := by
  change pathVal S.p₁ ≫ pathVal S.p₂ = σ
  rw [← pathVal_comp, S.hp, D.hσw]

lemma w₁_not_isIso : ¬IsIso S.w₁ := not_isIso_pathVal _ S.hp₁
lemma w₂_not_isIso : ¬IsIso S.w₂ := not_isIso_pathVal _ S.hp₂

lemma w₂_U (hL : LeftCancel P) (hR : RightCancel P) (hσ0 : σ ≠ 0) :
    (¬∃ g, g ≫ S.w₂ = D.U) ∧ (¬∃ g, g ≫ D.U = S.w₂) := by
  have hval : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) = pathVal (S.p₁.comp S.p₂) := by
    rw [D.hσu, S.hp, D.hσw]
  have h0 : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) ≠ 0 := by rw [D.hσu]; exact hσ0
  have hni : ¬Interlaced ((D.α.toPath.comp D.χ).comp D.u₂) (S.p₁.comp S.p₂) := by
    rw [S.hp]; exact D.hniσ
  exact ⟨(contour_cross hL hR _ _ _ _ hval h0 hni (by simp) S.hp₂).1,
    (contour_cross hL hR _ _ _ _ hval.symm (by rw [← hval]; exact h0) (fun h ↦ hni h.symm)
      S.hp₁ D.hu₂).1⟩

lemma ψ_w₁ (hL : LeftCancel P) (hR : RightCancel P) (hσ0 : σ ≠ 0) : ¬∃ g, D.ψ ≫ g = S.w₁ := by
  have hval : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) = pathVal (S.p₁.comp S.p₂) := by
    rw [D.hσu, S.hp, D.hσw]
  have h0 : pathVal ((D.α.toPath.comp D.χ).comp D.u₂) ≠ 0 := by rw [D.hσu]; exact hσ0
  have hni : ¬Interlaced ((D.α.toPath.comp D.χ).comp D.u₂) (S.p₁.comp S.p₂) := by
    rw [S.hp]; exact D.hniσ
  exact (contour_cross hL hR _ _ _ _ hval h0 hni (by simp) S.hp₂).2

/-- An irreducible `t → y₀` with `σ ∤ t` does not factor through `w₂`. -/
lemma irr (hσ : ¬IsIrreducible σ) {T : P} {t : T ⟶ y₀} (ht : IsIrreducible t)
    (hpk : ¬∃ g, g ≫ t = σ) : ¬∃ g, g ≫ S.w₂ = t := by
  rintro ⟨g, hg⟩
  rcases ht.2.2 _ g S.w₂ hg.symm with h | h
  · exact hpk ⟨S.w₁ ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, S.w₁w₂]⟩
  · exact S.w₂_not_isIso h

/-- `u₂` does not factor a tail `a ≫ w₂` of the contour path of `σ`. -/
lemma U_tail (hL : LeftCancel P) (hR : RightCancel P) (hσ0 : σ ≠ 0) {c₁ : RayVert P}
    (f : RayVert.mk x ⟶ c₁) (q : Quiver.Path c₁ S.c) (hq : S.p₁ = f.toPath.comp q) :
    ¬∃ g, g ≫ D.U = pathVal q ≫ S.w₂ := by
  have hval : pathVal (f.toPath.comp (q.comp S.p₂)) =
      pathVal ((D.α.toPath.comp D.χ).comp D.u₂) := by
    rw [← Quiver.Path.comp_assoc, ← hq, S.hp, D.hσw, D.hσu]
  have h0 : pathVal (f.toPath.comp (q.comp S.p₂)) ≠ 0 := by rw [hval, D.hσu]; exact hσ0
  have hni : ¬Interlaced (f.toPath.comp (q.comp S.p₂)) ((D.α.toPath.comp D.χ).comp D.u₂) := by
    rw [← Quiver.Path.comp_assoc, ← hq, S.hp]; exact fun h ↦ D.hniσ h.symm
  have := (contour_cross hL hR _ _ _ _ hval h0 hni (by simp) D.hu₂).1
  rwa [pathVal_comp q S.p₂] at this

end L6WSplit

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `ρ ∤ w₁`. -/
theorem l6s_ρ_w₁
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    {D : L6Data σ ρ} (S : L6WSplit D) : ¬∃ g, S.w₁ ≫ g = ρ :=
  B.l6_not_prefix_w hmin hL hR hσ0 hρ0 hv1 hv2 D S.p₁ S.p₂ S.hp S.hp₁

include B in
/-- A morphism incomparable with `σ` from the left does not factor through both
`w₂` and `u₂`. -/
theorem l6s_not_w₂_and_U
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) {D : L6Data σ ρ} (S : L6WSplit D) {z : P} (t : z ⟶ y₀) (ht : t ≠ 0)
    (h1 : ¬∃ c, c ≫ σ = t) (h2 : ¬∃ c, c ≫ t = σ) (hW : ∃ g, g ≫ S.w₂ = t)
    (hU : ∃ g, g ≫ D.U = t) : False := by
  obtain ⟨c₁, u'', eu, hu⟩ := exists_last_arrow D.u₂ D.U_not_isIso
  obtain ⟨d₁, p₂', ew, hw⟩ := exists_last_arrow S.p₂ S.w₂_not_isIso
  have hσu : pathVal (((D.α.toPath.comp D.χ).comp u'').cons eu) = σ := by
    have := D.hσu; rw [hu] at this; exact this
  have hσw : pathVal ((S.p₁.comp p₂').cons ew) = σ := by
    have := S.w₁w₂
    change pathVal S.p₁ ≫ pathVal S.p₂ = σ at this
    rw [← pathVal_comp, hw] at this; exact this
  refine B.not_factors_both_last hmin hL hR eu ew ((D.α.toPath.comp D.χ).comp u'')
    (S.p₁.comp p₂') (by rw [hσu, hσw]) (by rw [hσu]; exact hσ.1) ?_ t ht
    (by rw [hσu]; exact h1) (by rw [hσu]; exact h2) ?_ ?_
  · intro h
    apply D.hniσ
    rw [hu, ← S.hp, hw]
    exact h
  · obtain ⟨g, hg⟩ := hU
    refine ⟨g ≫ pathVal u'', ?_⟩
    rw [← hg, Category.assoc]
    change _ = g ≫ pathVal D.u₂
    rw [hu]
    rfl
  · obtain ⟨g, hg⟩ := hW
    refine ⟨g ≫ pathVal p₂', ?_⟩
    rw [← hg, Category.assoc]
    change _ = g ≫ pathVal S.p₂
    rw [hw]
    rfl

end MulBasis

end RayQuiver

end LargeIndecomposable
