module

public import LargeIndecomposable.Crowns.Lemma5.DualNeighbour
public import LargeIndecomposable.RayCategories.Contours.ContourCross

/-!
# BO13a Lemma 6: the set-up (figure 6.0)

Let `σ : x → y₀` and `ρ : x → y₁` be long neighbours of a crown (neither factors
through the other) whose contours `(α v, β w)` and `(α v', β' w')` share the
first arrow `α`. Among the morphisms `φ` out of `x` with `α ⪯ φ ⪯ σ, ρ` there is
a greatest one `ψ` (two incomparable maximal ones would give a crown in `x/P`,
Lemma 4 a)). Then `σ = ψ u₂`, `ρ = ψ u₂'`, and `(ψ u₂, β w)`, `(ψ u₂', β' w')`
are contours (`RayQuiver.MulBasis.exists_l6Data`). A common first arrow
exists because at most three arrows leave `x` (`not_four_irr`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- The data of BO13a figure 6.0. -/
structure L6Data {x y₀ y₁ : P} (σ : x ⟶ y₀) (ρ : x ⟶ y₁) where
  a : RayVert P
  α : RayVert.mk x ⟶ a
  m : RayVert P
  χ : Quiver.Path a m
  u₂ : Quiver.Path m (RayVert.mk y₀)
  u₂' : Quiver.Path m (RayVert.mk y₁)
  b : RayVert P
  β : RayVert.mk x ⟶ b
  w : Quiver.Path b (RayVert.mk y₀)
  b' : RayVert P
  β' : RayVert.mk x ⟶ b'
  w' : Quiver.Path b' (RayVert.mk y₁)
  hu₂ : 0 < u₂.length
  hu₂' : 0 < u₂'.length
  hσu : pathVal ((α.toPath.comp χ).comp u₂) = σ
  hρu : pathVal ((α.toPath.comp χ).comp u₂') = ρ
  hσw : pathVal (β.toPath.comp w) = σ
  hρw : pathVal (β'.toPath.comp w') = ρ
  hniσ : ¬Interlaced ((α.toPath.comp χ).comp u₂) (β.toPath.comp w)
  hniρ : ¬Interlaced ((α.toPath.comp χ).comp u₂') (β'.toPath.comp w')
  hmax : ∀ φ : BMor x, BLe (arrB α) φ → BLe φ ⟨y₀, σ⟩ → BLe φ ⟨y₁, ρ⟩ →
    BLe φ ⟨m.out, pathVal (α.toPath.comp χ)⟩

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 6, set-up**, from contours sharing the first arrow. -/
theorem exists_l6Data_of_common
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    {a b b' : RayVert P} (α : RayVert.mk x ⟶ a) (β : RayVert.mk x ⟶ b) (β' : RayVert.mk x ⟶ b')
    (v : Quiver.Path a (RayVert.mk y₀)) (w : Quiver.Path b (RayVert.mk y₀))
    (v' : Quiver.Path a (RayVert.mk y₁)) (w' : Quiver.Path b' (RayVert.mk y₁))
    (hv : pathVal (α.toPath.comp v) = σ) (hw : pathVal (β.toPath.comp w) = σ)
    (hni : ¬Interlaced (α.toPath.comp v) (β.toPath.comp w))
    (hv' : pathVal (α.toPath.comp v') = ρ) (hw' : pathVal (β'.toPath.comp w') = ρ)
    (hni' : ¬Interlaced (α.toPath.comp v') (β'.toPath.comp w')) :
    Nonempty (L6Data σ ρ) := by
  classical
  have : ∀ y : P, Finite (x ⟶ y) := fun y ↦ IsRayCategory.finite_hom x y
  have hσα : BLe (arrB α) ⟨y₀, σ⟩ := ⟨pathVal v, by rw [← hv, pathVal_comp, pathVal_toPath]; rfl⟩
  have hρα : BLe (arrB α) ⟨y₁, ρ⟩ := ⟨pathVal v', by rw [← hv', pathVal_comp, pathVal_toPath]; rfl⟩
  -- the greatest element `ψ`
  let S : Set (BMor x) := {φ | BLe (arrB α) φ ∧ BLe φ ⟨y₀, σ⟩ ∧ BLe φ ⟨y₁, ρ⟩}
  obtain ⟨ψ, ⟨hαψ, hψσ, hψρ⟩, hmaxψ⟩ := Set.exists_max_image S (fun φ ↦ depth φ.2)
    (Set.toFinite _) ⟨arrB α, BLe.refl _, hσα, hρα⟩
  have hgreat : ∀ φ ∈ S, BLe φ ψ := by
    intro φ ⟨hαφ, hφσ, hφρ⟩
    by_contra hφψ
    by_cases hψφ : BLe ψ φ
    · obtain ⟨c, hc⟩ := hψφ
      have hφ0 : φ.2 ≠ 0 := by
        obtain ⟨d, hd⟩ := hφσ
        change φ.2 ≫ d = σ at hd
        exact fun h ↦ hσ0 (by rw [← hd, h, zero_comp])
      by_cases hci : IsIso c
      · exact hφψ ⟨inv c, by rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]⟩
      · have h1 := depth_lt_comp_right ψ.2 c (by rw [hc]; exact hφ0) hci
        have h2 := hmaxψ φ ⟨hαφ, hφσ, hφρ⟩
        rw [hc] at h1
        omega
    · exact B.not_four_le hmin hR ψ φ ⟨y₀, σ⟩ ⟨y₁, ρ⟩ hσ0 hρ0 hψσ hφσ hψρ hφρ hψφ hφψ
        (fun ⟨c, hc⟩ ↦ hv1 ⟨c, hc⟩) (fun ⟨c, hc⟩ ↦ hv2 ⟨c, hc⟩)
  -- `ψ = α ≫ χ`, `σ = ψ ≫ c₀`, `ρ = ψ ≫ c₁`
  obtain ⟨χv', hχv⟩ := hαψ
  let χv : a.out ⟶ ψ.1 := χv'
  obtain ⟨c₀, hc₀⟩ := hψσ
  obtain ⟨c₁, hc₁⟩ := hψρ
  change α.1 ≫ χv = ψ.2 at hχv
  change ψ.2 ≫ c₀ = σ at hc₀
  change ψ.2 ≫ c₁ = ρ at hc₁
  have hψ0 : ψ.2 ≠ 0 := fun h ↦ hσ0 (by rw [← hc₀, h, zero_comp])
  have hχ0 : χv ≠ 0 := fun h ↦ hψ0 (by rw [← hχv, h, comp_zero])
  have hc₀0 : c₀ ≠ 0 := fun h ↦ hσ0 (by rw [← hc₀, h, comp_zero])
  have hc₁0 : c₁ ≠ 0 := fun h ↦ hρ0 (by rw [← hc₁, h, comp_zero])
  have hc₀i : ¬IsIso c₀ := fun h ↦ hv1 ⟨inv c₀ ≫ c₁, by rw [← hc₀, ← hc₁]; simp⟩
  have hc₁i : ¬IsIso c₁ := fun h ↦ hv2 ⟨inv c₁ ≫ c₀, by rw [← hc₀, ← hc₁]; simp⟩
  obtain ⟨χ, hχ⟩ := RayCat.exists_path χv hχ0
  obtain ⟨u₂, hu₂⟩ := RayCat.exists_path c₀ hc₀0
  obtain ⟨u₂', hu₂'⟩ := RayCat.exists_path c₁ hc₁0
  have hlen : ∀ {p q : RayVert P} (t : Quiver.Path p q), ¬IsIso (pathVal t : p.out ⟶ q.out) →
      0 < t.length := by
    intro p q t ht
    cases t with
    | nil => exact absurd (IsIso.id _) ht
    | cons _ _ => simp
  have hψv : pathVal (α.toPath.comp χ) = ψ.2 := by
    rw [pathVal_comp, pathVal_toPath, hχ]; exact hχv
  have hσu : pathVal ((α.toPath.comp χ).comp u₂) = σ := by
    rw [pathVal_comp, hψv, hu₂]; exact hc₀
  have hρu : pathVal ((α.toPath.comp χ).comp u₂') = ρ := by
    rw [pathVal_comp, hψv, hu₂']; exact hc₁
  -- `ψ u₂` is interlaced with `α v`, and `ψ u₂'` with `α v'`
  have hint : ∀ {y : P} (t t' : Quiver.Path a (RayVert.mk y)),
      pathVal (α.toPath.comp t) = pathVal (α.toPath.comp t') → pathVal (α.toPath.comp t) ≠ 0 →
      Interlaced (α.toPath.comp t) (α.toPath.comp t') := by
    intro y t t' h h0
    rw [pathVal_comp, pathVal_comp] at h
    rw [pathVal_comp] at h0
    exact .rel _ _ (interStep_prefix α.toPath (by simp) t t' (hL _ _ _ h h0) (fun h' ↦ h0 (by
      rw [h', comp_zero])))
  refine ⟨⟨a, α, RayVert.mk ψ.1, χ, u₂, u₂', b, β, w, b', β', w',
    hlen u₂ (by rw [hu₂]; exact hc₀i), hlen u₂' (by rw [hu₂']; exact hc₁i), hσu, hρu, hw, hw',
    ?_, ?_, ?_⟩⟩
  · intro h
    apply hni
    have h1 := hint (χ.comp u₂) v (by rw [← Quiver.Path.comp_assoc, hσu, hv])
      (by rw [← Quiver.Path.comp_assoc, hσu]; exact hσ0)
    rw [← Quiver.Path.comp_assoc] at h1
    exact h1.symm.trans _ _ _ h
  · intro h
    apply hni'
    have h1 := hint (χ.comp u₂') v' (by rw [← Quiver.Path.comp_assoc, hρu, hv'])
      (by rw [← Quiver.Path.comp_assoc, hρu]; exact hρ0)
    rw [← Quiver.Path.comp_assoc] at h1
    exact h1.symm.trans _ _ _ h
  · intro φ h1 h2 h3
    have := hgreat φ ⟨h1, h2, h3⟩
    change BLe φ ⟨ψ.1, pathVal (α.toPath.comp χ)⟩
    rw [hψv]
    exact this

include B in
/-- **BO13a Lemma 6, set-up.** Long neighbours with a common domain give the
data of figure 6.0. -/
theorem exists_l6Data
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ : IsLong σ) (hρ : IsLong ρ) (hcσ : ¬NotInContour σ) (hcρ : ¬NotInContour ρ)
    (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ) : Nonempty (L6Data σ ρ) := by
  obtain ⟨c, d, α, β, v, w, hv, hw, hni⟩ := exists_contour_first hσ hcσ
  obtain ⟨c', d', α', β', v', w', hv', hw', hni'⟩ := exists_contour_first hρ hcρ
  have hαβ : arrB α ≠ arrB β := fun h ↦ not_bLe_first_of_contour hL α β v w (by rw [hv, hw])
    (by rw [hv]; exact hσ.1) hni (h ▸ ⟨𝟙 _, Category.comp_id _⟩)
  have hαβ' : arrB α' ≠ arrB β' := fun h ↦ not_bLe_first_of_contour hL α' β' v' w'
    (by rw [hv', hw']) (by rw [hv']; exact hρ.1) hni' (h ▸ ⟨𝟙 _, Category.comp_id _⟩)
  have same : ∀ {e e' : RayVert P} (γ : RayVert.mk x ⟶ e) (γ' : RayVert.mk x ⟶ e'),
      arrB γ = arrB γ' → ∃ h : e' = e, γ' = h ▸ γ := by
    intro e e' γ γ' h
    have h' : (⟨e.out, γ.1⟩ : BMor x) = ⟨e'.out, γ'.1⟩ := h
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.mp h'
    change e = e' at e1
    subst e1
    exact ⟨rfl, Subtype.ext (eq_of_heq e2).symm⟩
  have key : ∀ {e f f' : RayVert P} (γ : RayVert.mk x ⟶ e) (δ : RayVert.mk x ⟶ f)
      (δ' : RayVert.mk x ⟶ f') (p : Quiver.Path e (RayVert.mk y₀))
      (q : Quiver.Path f (RayVert.mk y₀)) (p' : Quiver.Path e (RayVert.mk y₁))
      (q' : Quiver.Path f' (RayVert.mk y₁)), pathVal (γ.toPath.comp p) = σ →
      pathVal (δ.toPath.comp q) = σ → ¬Interlaced (γ.toPath.comp p) (δ.toPath.comp q) →
      pathVal (γ.toPath.comp p') = ρ → pathVal (δ'.toPath.comp q') = ρ →
      ¬Interlaced (γ.toPath.comp p') (δ'.toPath.comp q') → Nonempty (L6Data σ ρ) :=
    fun γ δ δ' p q p' q' ↦ B.exists_l6Data_of_common hmin hL hR hσ.1 hρ.1 hv1 hv2 γ δ δ' p q p' q'
  by_cases h1 : arrB α = arrB α'
  · obtain ⟨rfl, rfl⟩ := same α α' h1
    exact key α' β β' v w v' w' hv hw hni hv' hw' hni'
  by_cases h2 : arrB α = arrB β'
  · obtain ⟨rfl, rfl⟩ := same α β' h2
    exact key β' β α' v w w' v' hv hw hni hw' hv' (fun h ↦ hni' h.symm)
  by_cases h3 : arrB β = arrB α'
  · obtain ⟨rfl, rfl⟩ := same β α' h3
    exact key α' α β' w v v' w' hw hv (fun h ↦ hni h.symm) hv' hw' hni'
  by_cases h4 : arrB β = arrB β'
  · obtain ⟨rfl, rfl⟩ := same β β' h4
    exact key β' α α' w v w' v' hw hv (fun h ↦ hni h.symm) hw' hv' (fun h ↦ hni' h.symm)
  exfalso
  refine B.not_four_irr hmin hL hR σ hσ.2.1 hσ.1 hσ.2.2.1 x ![arrB α, arrB β, arrB α', arrB β']
    ?_ ?_
  · intro i j hij
    have := hαβ.symm
    have := hαβ'.symm
    have := Ne.symm h1
    have := Ne.symm h2
    have := Ne.symm h3
    have := Ne.symm h4
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    exacts [α.2, β.2, α'.2, β'.2]

end MulBasis

end RayQuiver

end LargeIndecomposable
