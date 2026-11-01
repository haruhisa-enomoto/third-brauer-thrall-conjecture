module

public import LargeIndecomposable.MildContours.Diamonds.Closure4
public import LargeIndecomposable.Cleaving.Families.FamMD33

/-!
# Diamond closure facts: arrows out of `x`

* `Y3`: the only arrow `e` into `b` with `e ≫ β` nonzero in `P/τ` is `δ` (the dual of
  `X3`, through `DiamondData.op`).
* `X1`: the only arrows out of `x` are `γ` and `δ` ([mild] LD, figure 3.3).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits Opposite RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]
  [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] {k : Type*} [Field k] [Infinite k]

namespace DiamondData

variable (D : DiamondData P)

/-- **The only arrow `e` into `b` with `e ≫ β` nonzero in `P/τ` is `δ`.** -/
theorem Y3 (hMo : MildHyp k Pᵒᵖ) {c : P} (e : c ⟶ D.b) (he : IsIrreducible e)
    (h0 : ¬FactorsThroughMorphism D.τ (e ≫ D.β)) : ∃ g, g ≫ D.δ = e := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨g, hg⟩ := D.op.X3 hMo e.op ((isIrreducible_op e).2 he) (by
    intro h
    apply h0
    refine (ftm_op_iff D.τ (e ≫ D.β)).1 ?_
    have e1 : D.op.δ ≫ e.op = (e ≫ D.β).op := rfl
    rw [e1, D.op_τ] at h
    exact h)
  have h2 := congrArg Quiver.Hom.unop hg
  simp only [unop_comp, Quiver.Hom.unop_op] at h2
  exact ⟨g.unop, h2⟩

/-- **The only arrows out of `x` are `γ` and `δ`** ([mild] LD, figure 3.3). -/
theorem X1 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {c : P} (ε : D.x ⟶ c)
    (hε : IsIrreducible ε) : (∃ h, D.γ ≫ h = ε) ∨ (∃ h, D.δ ≫ h = ε) := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hτ0 := D.τ_ne_zero
  have hγn := D.hγ.2.1
  have hδn := D.hδ.2.1
  have hηn := D.hη
  have n1 : ¬∃ h, D.γ ≫ h = ε := fun ⟨h, hh⟩ ↦ h1 h hh
  have n2 : ¬∃ h, D.δ ≫ h = ε := fun ⟨h, hh⟩ ↦ h2 h hh
  have n3 : ¬∃ h, ε ≫ h = D.γ := by
    rintro ⟨h, hh⟩
    rcases D.hγ.2.2 _ ε h hh.symm with h' | h'
    · exact hε.2.1 h'
    · exact n1 ⟨inv h, by rw [← hh]; simp⟩
  have n4 : ¬∃ h, ε ≫ h = D.δ := by
    rintro ⟨h, hh⟩
    rcases D.hδ.2.2 _ ε h hh.symm with h' | h'
    · exact hε.2.1 h'
    · exact n2 ⟨inv h, by rw [← hh]; simp⟩
  -- the case `ε ≫ ξ = γ ≫ η ≫ δ`
  have hB3 : ¬∃ ξ, ε ≫ ξ = (D.γ ≫ D.η) ≫ D.δ := by
    rintro ⟨ξ, hξ⟩
    have hεξβ : ε ≫ ξ ≫ D.β = D.τ := by rw [D.τ_ηδ, ← Category.assoc, hξ]; simp
    have hξ0 : ξ ≠ 0 := fun h ↦ hτ0 (by rw [← hεξβ, h]; simp)
    by_cases hξi : IsIso ξ
    · rcases hε.2.2 _ D.γ (D.η ≫ D.δ ≫ inv ξ) (by
          rw [← Category.assoc, ← Category.assoc, ← hξ]; simp) with h | h
      · exact hγn h
      · exact hηn (ray_isIso_factors D.η (D.δ ≫ inv ξ)).1
    obtain ⟨c'', p, e, hp⟩ := MildContour.exists_last_arrow ξ hξ0 hξi
    have heβ : ¬FactorsThroughMorphism D.τ (e.1 ≫ D.β) := by
      intro h
      apply (nfp hτ0 ε (ξ ≫ D.β) (𝟙 _) (Or.inl hε.2.1) (by rw [Category.comp_id, hεξβ]))
      rw [hp, Category.assoc]; exact ftm_comp_left h _
    obtain ⟨g, hg⟩ := D.Y3 hMo e.1 e.2 heβ
    set ζ := pathVal p ≫ g with hζ
    have hζδ : ζ ≫ D.δ = ξ := by rw [hζ, Category.assoc, hg, hp]
    have hεζ : ε ≫ ζ = D.γ ≫ D.η := by
      apply hR _ _ D.δ
      · rw [Category.assoc, hζδ, hξ]
      · rw [Category.assoc, hζδ, hξ]; intro h0; apply hτ0
        rw [D.τ_ηδ, show D.γ ≫ D.η ≫ D.δ ≫ D.β = ((D.γ ≫ D.η) ≫ D.δ) ≫ D.β by simp, h0, zero_comp]
    have hτζ : D.τ = ε ≫ ζ ≫ D.γ ≫ D.α := by rw [D.τ_η, ← Category.assoc, ← hεζ]; simp
    have hτζ' : D.τ = ε ≫ ζ ≫ D.δ ≫ D.β := by rw [D.τ_ηδ, ← Category.assoc, ← hεζ]; simp
    have hεζ0 : ε ≫ ζ ≠ 0 := fun h ↦ hτ0 (by rw [hτζ, ← Category.assoc, h, zero_comp])
    have hζn : ¬IsIso ζ := by
      intro h
      rcases hε.2.2 _ D.γ (D.η ≫ inv ζ) (by
          rw [← Category.assoc, ← hεζ]; simp) with h' | h'
      · exact hγn h'
      · exact hηn (ray_isIso_factors D.η (inv ζ)).1
    exact hM.not_md4b D.τ D.τ_not_isIso hτ0 D.η ζ D.γ D.δ
      (nfp hτ0 (𝟙 _) D.γ (D.α ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hα.2.1)) (by simp))
      (nfp hτ0 (𝟙 _) D.δ (D.β ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hβ.2.1))
        (by rw [D.τ_w]; simp))
      (nfp hτ0 D.γ D.η (D.γ ≫ D.α) (Or.inl hγn) D.τ_η.symm)
      (nfp hτ0 D.γ (D.η ≫ D.γ) D.α (Or.inl hγn) (by rw [D.τ_η]; simp))
      (nfp hτ0 D.γ (D.η ≫ D.δ) D.β (Or.inl hγn) (by rw [D.τ_ηδ]; simp))
      (nfp hτ0 ε ζ (D.γ ≫ D.α) (Or.inl hε.2.1) hτζ.symm)
      (nfp hτ0 ε (ζ ≫ D.γ) D.α (Or.inl hε.2.1) (by rw [hτζ]; simp))
      (nfp hτ0 ε (ζ ≫ D.δ) D.β (Or.inl hε.2.1) (by rw [hτζ']; simp))
      hηn hζn hγn hδn D.apγδ D.apδγ
      (fun ⟨g, hg⟩ ↦ n3 ⟨g, hR _ _ _ (show (ε ≫ g) ≫ D.η = D.γ ≫ D.η by
        rw [Category.assoc, hg, hεζ]) (by rw [Category.assoc, hg]; exact hεζ0)⟩)
      (fun ⟨g, hg⟩ ↦ n1 ⟨g, hR _ _ _ (show (D.γ ≫ g) ≫ ζ = ε ≫ ζ by
        rw [Category.assoc, hg, hεζ]) (by rw [Category.assoc, hg, ← hεζ]; exact hεζ0)⟩)
  have hz := D.zero
  refine hM.not_md33 D.τ D.τ_not_isIso hτ0 ε D.γ D.δ D.α D.β D.η D.δ D.ω' D.β
    MD33.not_isRepresentationFinite D.hval.symm
    (by simpa using ftm_comp_right (ftm_comp_left hz D.β) D.δ)
    (by simpa using ftm_comp_left hz D.β)
    (by simpa using ftm_comp_right hz D.δ) hz
    (nfp hτ0 D.γ (D.η ≫ D.δ) D.β (Or.inl hγn) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 D.γ D.η (D.γ ≫ D.α) (Or.inl hγn) D.τ_η.symm)
    (nfp hτ0 D.γ D.α (D.ω' ≫ D.α) (Or.inl hγn) rfl)
    (nfp hτ0 D.δ (D.β ≫ D.ω') D.α (Or.inl hδn) (by rw [D.τ_w]; simp))
    (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl hδn) D.τ_w.symm)
    (nfp hτ0 D.δ ((D.β ≫ D.ω') ≫ D.α) (𝟙 _) (Or.inl hδn) (by rw [D.τ_w]; simp))
    (nfp hτ0 D.δ D.β (D.ω' ≫ D.α) (Or.inl hδn) D.τ_w.symm)
    (nfp hτ0 (D.γ ≫ D.η) D.δ D.β (Or.inl (not_isIso_comp_left' _ hγn)) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) D.γ (D.α ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hα.2.1)) (by simp))
    (nfp hτ0 (𝟙 _) ((D.γ ≫ D.η) ≫ D.δ) D.β (Or.inr D.hβ.2.1) (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) D.δ (D.β ≫ D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hβ.2.1))
      (by rw [D.τ_w]; simp))
    (D.irr_not_ftm' ε hε)
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.η) (D.δ ≫ D.β) (Or.inr (not_isIso_comp_left' _ hδn))
      (by rw [D.τ_ηδ]; simp))
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω'))
      (by simp))
    (nfp hτ0 (D.γ ≫ D.α) D.ω' D.α (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    (nfp hτ0 (D.γ ≫ D.α) (D.ω' ≫ D.α) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    hε.2.1 hγn hδn D.hα.2.1 D.hβ.2.1 hηn hδn D.hω' D.hβ.2.1
    D.nA' D.nB' D.nC' n1 D.apγδ n2 D.apδγ D.nL' (by simpa using D.crownE hM) n3 n4
    (fun ⟨g, hg⟩ ↦ by
      rcases D.uniq ε g hε hg with h | h
      · exact n1 h
      · exact n2 h)
    (fun ⟨g, hg⟩ ↦ hB3 ⟨g ≫ D.δ, by rw [← Category.assoc, hg]⟩) hB3
    D.apαβ D.apβα D.nL (D.no_βρ hM) D.nB D.nC D.nA

end DiamondData

end RayCat

end LargeIndecomposable
