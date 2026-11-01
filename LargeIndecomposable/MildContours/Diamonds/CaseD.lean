module

public import LargeIndecomposable.MildContours.Diamonds.CaseC
public import LargeIndecomposable.Cleaving.Families.FamMD29A
public import LargeIndecomposable.Cleaving.Families.FamMD29B

/-!
# [mild] diamonds, case (D): `α ≫ ω' = η ≫ γ`, first structure

In case (D) of the diamond trichotomy:
* case (B) `ω' = g ≫ γ` is impossible (`ρ = g ≫ ω = g ≫ δ ≫ β`, Lemma 2.2);
* `η` is not invertible (else case (A));
* a suffix `δ'` of `w` with `δ' ≫ ω' = θ ≫ γ` is excluded by the crown
  `Ã(α, δ', θ, η)` ([mild] proof of PD), in particular case (C);
* `ω' ≫ η` is zero in `P/τ` (the `D̃₄` star at `a`);
* `γ` and `δ` are arrows ([mild] figure 2.9, two thin diagrams).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace MildContour

variable {x y : P} (C : MildContour x y)

/-- **Case (B) is impossible**: `ω' = g ≫ γ` gives `ρ = g ≫ δ ≫ β`. -/
theorem caseB (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hρ : C.ρ = ω' ≫ C.α.1) (g : y ⟶ x)
    (hg : g ≫ C.γ = ω') : False :=
  C.not_ρ_factor_both hM hρ (ω'' := g ≫ C.δ)
    (by rw [hρ, ← hg, Category.assoc, Category.assoc]; change g ≫ C.ω = _; rw [C.ω_eq_w])

/-- **The crown of [mild] PD**: no `δ' ≫ ω' = θ ≫ γ` for a morphism `δ'` into `y` that is
apart from `α`, has a left factor `q` with `q ≫ δ' = ω`, and `δ' ≫ ω' ≠ 0`. -/
theorem crownD (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) {m : P} (δ' : m ⟶ y) (θ : m ⟶ x)
    (q : x ⟶ m) (hq : q ≫ δ' = C.ω) (h : δ' ≫ ω' = θ ≫ C.γ) (hp1 : ¬∃ c, c ≫ δ' = C.α.1)
    (hp2 : ¬∃ c, c ≫ C.α.1 = δ') (hδ' : ¬FactorsThroughMorphism C.τ δ') : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := C.τ_ne_zero
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτη : C.τ = C.γ ≫ η ≫ C.γ ≫ C.α.1 := by
    rw [hτv, ← Category.assoc C.α.1, hη]; simp
  have hωω : C.γ ≫ C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ hτ0 (by
    rw [hτv, show C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 = (C.γ ≫ C.α.1 ≫ ω') ≫ C.α.1 by simp, h0, zero_comp])
  have hδω : δ' ≫ ω' ≠ 0 := fun h0 ↦ hωω (by
    rw [← Category.assoc, show C.γ ≫ C.α.1 = C.ω from rfl, ← hq, Category.assoc, h0, comp_zero])
  have hαω : C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ hωω (by rw [h0, comp_zero])
  have hθγ : θ ≫ C.γ ≠ 0 := by rw [← h]; exact hδω
  refine hM.not_crown2 C.τ C.τ_not_isIso hτ0 C.α.1 δ' θ η (C.ftm_α hR) hδ' ?_
    (nfp hτ0 C.γ η (C.γ ≫ C.α.1) (Or.inl (C.γ_not_isIso hR)) (by rw [hτη]))
    hp1 hp2 ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v, huv⟩
    have e : C.τ = (q ≫ u) ≫ C.τ ≫ (v ≫ C.γ ≫ C.α.1) := by
      conv_lhs => rw [hτv, show C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 = ((C.γ ≫ C.α.1) ≫ ω') ≫ C.α.1 by simp,
        show C.γ ≫ C.α.1 = C.ω from rfl, ← hq, Category.assoc q, h, huv]
      simp
    obtain ⟨-, h1⟩ := IsRayCategory.eq_id_of_two_sided _ hτ0 _ _ e
    haveI : IsIso (v ≫ C.γ ≫ C.α.1) := by rw [h1]; infer_instance
    exact C.ω_not_isIso (ray_isIso_factors v (C.γ ≫ C.α.1)).2
  · rintro ⟨c, hc⟩
    exact hp2 ⟨c, hR _ _ _ (show (c ≫ C.α.1) ≫ ω' = δ' ≫ ω' by
      rw [Category.assoc, hη, ← Category.assoc, hc, h]) (by
        rw [show (c ≫ C.α.1) ≫ ω' = δ' ≫ ω' by rw [Category.assoc, hη, ← Category.assoc, hc, h]]
        exact hδω)⟩
  · rintro ⟨c, hc⟩
    exact hp1 ⟨c, hR _ _ _ (show (c ≫ δ') ≫ ω' = C.α.1 ≫ ω' by
      rw [Category.assoc, h, ← Category.assoc, hc, hη]) (by
        rw [show (c ≫ δ') ≫ ω' = C.α.1 ≫ ω' by rw [Category.assoc, h, ← Category.assoc, hc, hη]]
        exact hαω)⟩
  · rintro ⟨c, hc⟩
    exact C.caseB hM hρ c (hL _ _ _ (show δ' ≫ (c ≫ C.γ) = δ' ≫ ω' by
      rw [← Category.assoc, hc, h]) (by rw [← Category.assoc, hc, ← h]; exact hδω))
  · rintro ⟨c, hc⟩
    exact C.caseA hM hω' hρ (ξ := c) (hL _ _ _ (show θ ≫ (c ≫ ω') = θ ≫ C.γ by
      rw [← Category.assoc, hc, h]) (by rw [← Category.assoc, hc, h]; exact hθγ))
  · rintro ⟨c, hc⟩
    exact C.caseA hM hω' hρ (ξ := c) (hL _ _ _ (show η ≫ (c ≫ ω') = η ≫ C.γ by
      rw [← Category.assoc, hc, hη]) (by rw [← Category.assoc, hc, hη, ← hη]; exact hαω))
  · rintro ⟨c, hc⟩
    exact C.caseB hM hρ c (hL _ _ _ (show C.α.1 ≫ (c ≫ C.γ) = C.α.1 ≫ ω' by
      rw [← Category.assoc, hc, hη]) (by rw [← Category.assoc, hc, ← hη]; exact hαω))


/-- In case (D), `η` is not invertible (else case (A)). -/
lemma D_η (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) : ¬IsIso η := fun h ↦
  C.caseA hM hω' hρ (ξ := inv η ≫ C.α.1) (by rw [Category.assoc, hη]; simp)

/-- In case (D), `ω' ≫ η` is zero in `P/τ`: otherwise the `D̃₄` star at `a` (in `γ, ω'`,
out `α, η`) cleaves. -/
theorem D_zero (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) : FactorsThroughMorphism C.τ (ω' ≫ η) := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := C.τ_ne_zero
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτη : C.τ = C.γ ≫ η ≫ C.γ ≫ C.α.1 := by
    rw [hτv, ← Category.assoc C.α.1, hη]; simp
  have hαω : C.α.1 ≫ ω' ≠ 0 := fun h0 ↦ hτ0 (by
    rw [hτv, ← Category.assoc C.α.1, h0]; simp)
  by_contra h
  exact hM.not_md4b C.τ C.τ_not_isIso hτ0 C.γ ω' C.α.1 η (C.ftm_α hR)
    (nfp hτ0 C.γ η (C.γ ≫ C.α.1) (Or.inl (C.γ_not_isIso hR)) (by rw [hτη]))
    (C.ftm_γ hR) C.ftm_ω
    (nfp hτ0 (𝟙 _) (C.γ ≫ η) (C.γ ≫ C.α.1) (Or.inr C.ω_not_isIso) (by rw [hτη]; simp))
    (nfp hτ0 (C.γ ≫ C.α.1) ω' C.α.1 (Or.inr C.α.2.2.1) (by rw [hτv]; simp))
    (by rw [← hρ]; exact C.ftm_ρ) h
    (C.γ_not_isIso hR) hω' C.α.2.2.1 (C.D_η hM hω' hρ hη)
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g (hL _ _ _ (show C.α.1 ≫ (g ≫ C.γ) = C.α.1 ≫ ω' by
      rw [← Category.assoc, hg, hη]) (by rw [← Category.assoc, hg, ← hη]; exact hαω)))
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ (ξ := g) (hL _ _ _ (show η ≫ (g ≫ ω') = η ≫ C.γ by
      rw [← Category.assoc, hg, hη]) (by rw [← Category.assoc, hg, hη, ← hη]; exact hαω)))
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g hg) (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ hg)

/-- In case (D), `γ` is an arrow ([mild] figure 2.9, first diagram). -/
theorem D_γirr (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) : IsIrreducible C.γ := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hgd := C.γ_δ_apart hR hL
  by_contra hγ
  have hδ := C.δ_irr hM hω' hρ hγ
  have hv := two_le_length C.v' (C.γ_not_isIso hR) hγ
  obtain ⟨c, p', γl, hv'⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons C.v').1 (by omega)
  have hp'l : 0 < p'.length := by
    have := congrArg Quiver.Path.length hv'; simp at this; omega
  have hγe : C.γ = pathVal p' ≫ γl.1 := by change pathVal C.v' = _; rw [hv']; rfl
  have hp'n : ¬IsIso (pathVal p') := not_isIso_pathVal _ hp'l
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτη : C.τ = C.γ ≫ η ≫ C.γ ≫ C.α.1 := by
    rw [hτv, ← Category.assoc C.α.1, hη]; simp
  have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
  have hτηδ : C.τ = C.γ ≫ η ≫ C.δ ≫ C.β.1 := by rw [hτη, hvw]
  have hτw : C.τ = C.δ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ]
  have hηω : η ≫ C.δ ≫ C.β.1 = C.α.1 ≫ ω' ≫ C.α.1 := by
    rw [← hvw, ← Category.assoc, ← hη]; simp
  have hγn := C.γ_not_isIso hR
  have hηn := C.D_η hM hω' hρ hη
  have hγα := not_isIso_comp_left' C.α.1 hγn
  refine hM.not_md29a C.τ C.τ_not_isIso hτ0 γl.1 η C.δ C.β.1 ω' C.α.1 C.γ
    MD29A.not_isRepresentationFinite hη (by rw [hη])
    (nfp hτ0 C.γ (η ≫ C.γ) C.α.1 (Or.inl hγn) (by rw [hτη]; simp))
    (nfp hτ0 C.γ (η ≫ C.δ) C.β.1 (Or.inl hγn) (by rw [hτηδ]; simp))
    (nfp hτ0 C.γ η (C.γ ≫ C.α.1) (Or.inl hγn) (by rw [hτη]))
    (C.ftm_α hR)
    (nfp hτ0 C.δ (C.β.1 ≫ ω') C.α.1 (Or.inl (C.δ_not_isIso hR)) (by rw [hτw]; simp))
    (C.ftm_β hR)
    (nfp hτ0 (pathVal p') γl.1 (C.α.1 ≫ ω' ≫ C.α.1) (Or.inl hp'n) (by rw [hτv, hγe]; simp))
    (nfp hτ0 (pathVal p') ((γl.1 ≫ η) ≫ C.γ) C.α.1 (Or.inl hp'n)
      (by rw [hτη, hγe]; simp))
    (nfp hτ0 (pathVal p') ((γl.1 ≫ η) ≫ C.δ) C.β.1 (Or.inl hp'n)
      (by rw [hτηδ, hγe]; simp))
    (nfp hτ0 (pathVal p') (γl.1 ≫ η) (C.γ ≫ C.α.1) (Or.inl hp'n)
      (by rw [hτη, hγe]; simp))
    (nfp hτ0 (pathVal p') (γl.1 ≫ C.α.1) (ω' ≫ C.α.1) (Or.inl hp'n)
      (by rw [hτv, hγe]; simp))
    (C.ftm_γ hR) (C.ftm_δ hR)
    (nfp hτ0 (C.γ ≫ C.α.1) ω' C.α.1 (Or.inl hγα) (by rw [hτv]; simp))
    γl.2.2.1 hηn hδ.2.1 C.β.2.2.1 hω' C.α.2.2.1 hγn
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ (ξ := g) (hL _ _ _ (show η ≫ (g ≫ ω') = η ≫ C.γ by
      rw [← Category.assoc, hg, hη]) (by
        rw [← Category.assoc, hg, hη]; intro h0; apply hτ0; rw [hτη, ← Category.assoc η, h0]
        simp)))
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g (hL _ _ _ (show C.α.1 ≫ (g ≫ C.γ) = C.α.1 ≫ ω' by
      rw [← Category.assoc, hg, hη]) (by
        rw [← Category.assoc, hg]; intro h0; apply hτ0; rw [hτη, ← Category.assoc η, h0]
        simp)))
    (fun ⟨g, hg⟩ ↦ C.not_ρ_factor_both hM hρ (ω'' := g) (by
      have e : C.α.1 ≫ (g ≫ C.β.1) = C.α.1 ≫ (ω' ≫ C.α.1) := by
        rw [← Category.assoc, hg, Category.assoc, hηω]
      rw [hρ]; exact (hL _ _ _ e (by rw [e, ← hρ]; exact C.αρ_ne_zero)).symm))
    hgd.2 hgd.1 hap.2 hap.1
    (fun ⟨g, hg⟩ ↦ C.hni (by
      rw [hv']
      have e : (p'.cons γl).cons C.α = (p'.cons γl).comp (Quiver.Path.nil.cons C.α) := rfl
      rw [e]
      refine interlaced_of_factor hR p' hp'l γl _ C.w' C.β
        (by rw [← e, ← hv']; exact C.hval) (by rw [← e, ← hv']; exact C.h0) g ?_
      rw [hg]; simp [pathVal]))
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g hg)
    (fun ⟨g, hg⟩ ↦ C.crownD hM hω' hρ hη C.β.1 g C.δ hvw.symm hg.symm hap.1 hap.2 (C.ftm_β hR))
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ hg)


/-- In case (D), `δ` is an arrow ([mild] figure 2.9, second diagram). -/
theorem D_δirr (hM : MildHyp k P) {ω' : y ⟶ C.sv} (hω' : ¬IsIso ω') (hρ : C.ρ = ω' ≫ C.α.1)
    {η : C.sv ⟶ x} (hη : C.α.1 ≫ ω' = η ≫ C.γ) : IsIrreducible C.δ := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτ0 := C.τ_ne_zero
  have hgd := C.γ_δ_apart hR hL
  have hγi := C.D_γirr hM hω' hρ hη
  by_contra hδ
  have hw := two_le_length C.w' (C.δ_not_isIso hR) hδ
  obtain ⟨c', d', b₀, f₁, r', hr'⟩ := path_two_arrows C.w' hw
  set ξ := f₁.1 ≫ pathVal r' with hξ
  have hδe : C.δ = b₀.1 ≫ ξ := by
    change pathVal C.w' = _; rw [hr', pathVal_comp]; change ((𝟙 _ ≫ b₀.1) ≫ f₁.1) ≫ _ = _
    simp only [Category.id_comp, Category.assoc, hξ]
  have hξn : ¬IsIso ξ := fun h ↦ f₁.2.2.1 (ray_isIso_factors f₁.1 (pathVal r')).1
  have hb₀ := b₀.2.2.1
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_v, hρ]
  have hτη : C.τ = C.γ ≫ η ≫ C.γ ≫ C.α.1 := by
    rw [hτv, ← Category.assoc C.α.1, hη]; simp
  have hvw : C.γ ≫ C.α.1 = C.δ ≫ C.β.1 := C.hval
  have hτηδ : C.τ = C.γ ≫ η ≫ b₀.1 ≫ ξ ≫ C.β.1 := by rw [hτη, hvw, hδe]; simp
  have hτw : C.τ = b₀.1 ≫ ξ ≫ C.β.1 ≫ ω' ≫ C.α.1 := by rw [C.τ_eq_w, hρ, hδe]; simp
  have hηω : η ≫ C.δ ≫ C.β.1 = C.α.1 ≫ ω' ≫ C.α.1 := by
    rw [← hvw, ← Category.assoc, ← hη]; simp
  have hγn := C.γ_not_isIso hR
  have hηn := C.D_η hM hω' hρ hη
  have hγα := not_isIso_comp_left' C.α.1 hγn
  have hw_eq : C.w'.cons C.β = ((Quiver.Path.nil.cons b₀).cons f₁).comp (r'.cons C.β) := by
    rw [hr']; rfl
  have hM2 : ¬∃ g, g ≫ C.α.1 = ξ ≫ C.β.1 := by
    rintro ⟨g, hg⟩
    apply C.hni
    refine Relation.EqvGen.symm _ _ ?_
    rw [hw_eq]
    refine interlaced_of_factor hR _ (by simp) f₁ (r'.cons C.β) C.v' C.α
      (by rw [← hw_eq]; exact C.hval.symm) (by rw [← hw_eq, ← C.hval]; exact C.h0) g ?_
    rw [hg, hξ, Category.assoc]; rfl
  have hL2 : ∀ g : y ⟶ C.sw, C.α.1 ≫ g ≫ C.β.1 = C.α.1 ≫ ω' ≫ C.α.1 → False := fun g e ↦
    C.not_ρ_factor_both hM hρ (ω'' := g)
      (by rw [hρ]; exact (hL _ _ _ e (by rw [e, ← hρ]; exact C.αρ_ne_zero)).symm)
  refine hM.not_md29b C.τ C.τ_not_isIso hτ0 η b₀.1 ξ ξ C.β.1 ω' C.α.1 C.γ
    MD29B.not_isRepresentationFinite hη
    (nfp hτ0 C.γ (η ≫ C.γ) C.α.1 (Or.inl hγn) (by rw [hτη]; simp))
    (nfp hτ0 C.γ ((η ≫ b₀.1) ≫ ξ) C.β.1 (Or.inl hγn) (by rw [hτηδ]; simp))
    (nfp hτ0 C.γ (η ≫ b₀.1) (ξ ≫ C.β.1) (Or.inl hγn) (by rw [hτηδ]; simp))
    (nfp hτ0 C.γ η (C.γ ≫ C.α.1) (Or.inl hγn) (by rw [hτη]))
    (C.ftm_α hR)
    (nfp hτ0 (b₀.1 ≫ ξ) (C.β.1 ≫ ω') C.α.1 (Or.inr C.α.2.2.1) (by rw [hτw]; simp))
    (C.ftm_β hR)
    (nfp hτ0 b₀.1 ξ (C.β.1 ≫ ω' ≫ C.α.1) (Or.inl hb₀) (by rw [hτw]))
    (nfp hτ0 b₀.1 ((ξ ≫ C.β.1) ≫ ω') C.α.1 (Or.inl hb₀) (by rw [hτw]; simp))
    (nfp hτ0 b₀.1 ξ (C.β.1 ≫ ω' ≫ C.α.1) (Or.inl hb₀) (by rw [hτw]))
    (nfp hτ0 b₀.1 (ξ ≫ C.β.1) (ω' ≫ C.α.1) (Or.inl hb₀) (by rw [hτw]; simp))
    (C.ftm_γ hR) (by rw [← hδe]; exact C.ftm_δ hR)
    (nfp hτ0 (𝟙 _) b₀.1 (ξ ≫ C.β.1 ≫ ω' ≫ C.α.1) (Or.inr (not_isIso_comp_left' _ hξn))
      (by rw [hτw]; simp))
    (nfp hτ0 (C.γ ≫ C.α.1) ω' C.α.1 (Or.inl hγα) (by rw [hτv]; simp))
    hηn hb₀ hξn hξn C.β.2.2.1 hω' C.α.2.2.1 hγn
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ (ξ := g) (hL _ _ _ (show η ≫ (g ≫ ω') = η ≫ C.γ by
      rw [← Category.assoc, hg, hη]) (by
        rw [← Category.assoc, hg, hη]; intro h0; apply hτ0; rw [hτη, ← Category.assoc η, h0]
        simp)))
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g (hL _ _ _ (show C.α.1 ≫ (g ≫ C.γ) = C.α.1 ≫ ω' by
      rw [← Category.assoc, hg, hη]) (by
        rw [← Category.assoc, hg]; intro h0; apply hτ0; rw [hτη, ← Category.assoc η, h0]
        simp)))
    (fun ⟨g, hg⟩ ↦ hL2 (g ≫ ξ) (by
      calc C.α.1 ≫ (g ≫ ξ) ≫ C.β.1 = (C.α.1 ≫ g) ≫ ξ ≫ C.β.1 := by simp
        _ = η ≫ (b₀.1 ≫ ξ) ≫ C.β.1 := by rw [hg]; simp
        _ = _ := by rw [← hδe, hηω]))
    (fun ⟨g, hg⟩ ↦ hL2 g (by
      calc C.α.1 ≫ g ≫ C.β.1 = (C.α.1 ≫ g) ≫ C.β.1 := by simp
        _ = η ≫ (b₀.1 ≫ ξ) ≫ C.β.1 := by rw [hg]; simp
        _ = _ := by rw [← hδe, hηω]))
    (fun ⟨g, hg⟩ ↦ hgd.2 ⟨g ≫ ξ, by rw [← Category.assoc, hg, hδe]⟩)
    (fun ⟨g, hg⟩ ↦ hgd.2 ⟨g, by rw [hg, hδe]⟩)
    (fun ⟨g, hg⟩ ↦ by
      rcases hγi.2.2 _ b₀.1 g hg.symm with h | h
      · exact hb₀ h
      · have e : b₀.1 ≫ (g ≫ C.α.1) = b₀.1 ≫ (ξ ≫ C.β.1) := by
          rw [← Category.assoc, hg, hvw, hδe, Category.assoc]
        have e2 := hL _ _ _ e (by rw [e, ← Category.assoc, ← hδe, ← hvw]; exact C.h0)
        rcases C.α.2.2.2 _ (inv g ≫ ξ) C.β.1 (by rw [Category.assoc, ← e2]; simp) with h1 | h1
        · exact hξn (ray_isIso_factors (inv g) ξ).2
        · exact C.β.2.2.1 h1)
    hM2 hap.2 hap.1
    (fun ⟨g, hg⟩ ↦ C.caseB hM hρ g hg)
    (fun ⟨g, hg⟩ ↦ C.crownD hM hω' hρ hη (ξ ≫ C.β.1) g b₀.1 (by rw [← Category.assoc, ← hδe]; exact C.ω_eq_w.symm)
      (by rw [← hg]) (fun ⟨c, hc⟩ ↦ by
        rcases C.α.2.2.2 _ (c ≫ ξ) C.β.1 (by rw [← hc]; simp) with h | h
        · exact hξn (ray_isIso_factors c ξ).2
        · exact C.β.2.2.1 h) hM2
      (nfp hτ0 b₀.1 (ξ ≫ C.β.1) (ω' ≫ C.α.1) (Or.inl hb₀) (by rw [hτw]; simp)))
    (fun ⟨g, hg⟩ ↦ C.crownD hM hω' hρ hη C.β.1 g C.δ hvw.symm hg.symm hap.1 hap.2 (C.ftm_β hR))
    (fun ⟨g, hg⟩ ↦ C.caseA hM hω' hρ hg)

end MildContour

end RayCat

end LargeIndecomposable
