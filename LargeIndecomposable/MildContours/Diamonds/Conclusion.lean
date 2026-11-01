module

public import LargeIndecomposable.MildContours.Diamonds.ClosureHelpers
public import LargeIndecomposable.Cleaving.Families.FamMEX1
public import LargeIndecomposable.Cleaving.Families.FamMEX2
public import LargeIndecomposable.MildContours.Basic.Theorem3

/-!
# Diamond: the exceptional case and the conclusion

In the exceptional case `τ ≫ f ≠ 0` (`f` the first arrow of `ω' = f f'`):
* `mex1`: `η` is an arrow ([mild] figure 4.8, second diagram, completed);
* `mex2`: `f` is the only arrow into its target ([mild] figure 4.9, second
  diagram; its conditions reduce to: `μ ≫ φ = τ ≫ f` forces `φ = f`);
* `P_x` is projective-injective with socle `τ ≫ f`.
`no_projInj`: a diamond gives a projective-injective `P_x` in `P` or in `Pᵒᵖ`.
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

/-- An arrow does not factor through a composite of two non-invertible morphisms. -/
lemma irr_not_ftm_comp {a b c d e : P} (p : a ⟶ b) (q : b ⟶ c) (hp : ¬IsIso p) (hq : ¬IsIso q)
    (f : d ⟶ e) (hf : IsIrreducible f) : ¬FactorsThroughMorphism (p ≫ q) f := by
  rintro ⟨u, v, rfl⟩
  rcases hf.2.2 _ (u ≫ p) (q ≫ v) (by simp) with h | h
  · exact hp (ray_isIso_factors u p).2
  · exact hq (ray_isIso_factors q v).1

namespace DiamondData

variable (D : DiamondData P)

/-- Every nonzero morphism into `y` divides `τ` from the left (outside the dual exceptional
case). -/
theorem div_τ_op (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen)
    (hE' : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬D.op.Exc) {w : P} (ν : w ⟶ D.y)
    (hν : ν ≠ 0) : ∃ g, g ≫ ν = D.τ := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨g, hg⟩ := D.op.div_τ hMo hMo.op hG.op hE' ν.op
    (fun h ↦ hν (Quiver.Hom.op_inj (by rw [h]; rfl)))
  rw [D.op_τ] at hg
  exact ⟨g.unop, Quiver.Hom.op_inj hg⟩

/-- **Uniqueness of the first arrow of `ω'`** among arrows `ν` with `τ ≫ ν ≠ 0`. -/
theorem X4u (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {c c' : P} (f : D.y ⟶ c)
    (ν : D.y ⟶ c') (hf : IsIrreducible f) (hν : IsIrreducible ν) (hτf : D.τ ≫ f ≠ 0)
    (hτν : D.τ ≫ ν ≠ 0) : ∃ g, ν ≫ g = f := by
  by_contra hne
  have hne2 : ¬∃ g, f ≫ g = ν := by
    rintro ⟨g, hg⟩
    rcases hν.2.2 _ f g hg.symm with h | h
    · exact hf.2.1 h
    · exact hne ⟨inv g, by rw [← hg]; simp⟩
  have hτ0 := D.τ_ne_zero
  have n1 := D.not_ftm_ω hMo hG f hτf
  have n2 := D.not_ftm_ω hMo hG ν hτν
  exact hM.not_md4b D.τ D.τ_not_isIso hτ0 D.α D.β f ν (D.irr_not_ftm' f hf)
    (D.irr_not_ftm' ν hν) (D.irr_not_ftm' D.α D.hα)
    (fun h ↦ n1 (by simpa using ftm_comp_left h D.γ))
    (fun h ↦ n2 (by simpa using ftm_comp_left h D.γ))
    (D.irr_not_ftm' D.β D.hβ)
    (fun h ↦ n1 (by rw [D.hval]; simpa using ftm_comp_left h D.δ))
    (fun h ↦ n2 (by rw [D.hval]; simpa using ftm_comp_left h D.δ))
    D.hα.2.1 D.hβ.2.1 hf.2.1 hν.2.1 hne2 hne D.apαβ D.apβα

/-- `σ ≫ σ = 0`. -/
lemma σσ_zero (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) : (D.γ ≫ D.η) ≫ (D.γ ≫ D.η) = 0 := by
  obtain ⟨u, v, huv⟩ := D.zero
  have h : (D.γ ≫ D.η) ≫ (D.γ ≫ D.η) = ((D.γ ≫ D.α) ≫ u) ≫ D.τ ≫ v := by
    calc (D.γ ≫ D.η) ≫ (D.γ ≫ D.η) = D.γ ≫ (D.η ≫ D.γ) ≫ D.η := by simp
      _ = (D.γ ≫ D.α) ≫ (D.ω' ≫ D.η) := by rw [← D.hD]; simp
      _ = _ := by rw [huv]; simp
  rw [h, ← Category.assoc _ D.τ, D.rad_τ hMo hG _
    (not_isIso_comp_left' _ (not_isIso_comp_left' _ D.hγ.2.1)), zero_comp]

/-- **In the exceptional case, `η` is an arrow** ([mild] figure 4.8, second diagram, with the
arrow `ω₁` before `ω₂`). -/
theorem mex1 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {c : P} (f : D.y ⟶ c) (f' : c ⟶ D.a)
    (hf : IsIrreducible f) (hff : f ≫ f' = D.ω') (hf' : ¬IsIso f') (hτf : D.τ ≫ f ≠ 0) :
    IsIrreducible D.η := by
  by_contra hirr
  have hR : RightCancel P := hM.right
  have hη0 : D.η ≠ 0 := fun h ↦ D.hτ0 (by
    rw [show D.γ ≫ D.α ≫ D.ω' ≫ D.α = D.τ from rfl, D.τ_η, h]; simp)
  obtain ⟨c₁, η₁, η₂, hη₁n, hη₂n, hη⟩ : ∃ (c₁ : P) (η₁ : D.a ⟶ c₁) (η₂ : c₁ ⟶ D.x),
      ¬IsIso η₁ ∧ ¬IsIso η₂ ∧ D.η = η₁ ≫ η₂ := by
    by_contra hc
    push Not at hc
    exact hirr ⟨hη0, D.hη, fun z g h hgh ↦ by
      by_contra hh; push Not at hh; exact hc z g h hh.1 hh.2 hgh⟩
  have h₁ : IsIrreducible η₁ := by
    by_contra h; exact D.η_two hM η₁ η₂ hη₁n hη₂n (Or.inl h) hη
  have h₂ : IsIrreducible η₂ := by
    by_contra h; exact D.η_two hM η₁ η₂ hη₁n hη₂n (Or.inr h) hη
  have hf'i : IsIrreducible f' := by
    by_contra h; exact D.ω_two hMo f f' hf.2.1 hf' (Or.inr h) hff.symm
  have hαω := D.αω'_ne_zero
  set τ' := D.τ ≫ f with hτ'
  have hτ'n : ¬IsIso τ' := not_isIso_comp_right' _ hf.2.1
  have e1 : τ' = D.γ ≫ D.α ≫ f ≫ f' ≫ D.α ≫ f := by
    rw [hτ']; change (D.γ ≫ D.α ≫ D.ω' ≫ D.α) ≫ f = _; rw [← hff]; simp
  have e2 : τ' = D.γ ≫ η₁ ≫ η₂ ≫ D.γ ≫ D.α ≫ f := by rw [hτ', D.τ_η, hη]; simp
  have e3 : τ' = D.δ ≫ D.β ≫ f ≫ f' ≫ D.α ≫ f := by rw [hτ', D.τ_w, ← hff]; simp
  have e4 : τ' = D.γ ≫ η₁ ≫ η₂ ≫ D.δ ≫ D.β ≫ f := by rw [hτ', D.τ_ηδ, hη]; simp
  have nf := fun {s t : P} (pp : D.x ⟶ s) (g : s ⟶ t) (q : t ⟶ c) (hpq : ¬IsIso pp ∨ ¬IsIso q)
    (h : pp ≫ g ≫ q = τ') ↦ nfp hτf pp g q hpq h
  have ir := fun {s t : P} (e : s ⟶ t) (he : IsIrreducible e) ↦
    irr_not_ftm_comp (D.γ ≫ D.α ≫ f ≫ f' ≫ D.α) f
      (not_isIso_comp_left' _ D.hγ.2.1) hf.2.1 e he
  have ir' : ∀ {s t : P} (e : s ⟶ t), IsIrreducible e → ¬FactorsThroughMorphism τ' e := by
    intro s t e he; rw [e1, show D.γ ≫ D.α ≫ f ≫ f' ≫ D.α ≫ f =
      (D.γ ≫ D.α ≫ f ≫ f' ≫ D.α) ≫ f by simp]; exact ir e he
  have hγn := D.hγ.2.1
  have hγα := not_isIso_comp_left' D.α hγn
  have hγη₁ := not_isIso_comp_left' η₁ hγn
  have hγαf := not_isIso_comp_left' f hγα
  refine hM.not_mex1 τ' hτ'n hτf η₂ f f' D.γ D.δ D.α D.β f MEX1.not_isRepresentationFinite
    (by rw [← Category.assoc D.δ, ← D.hval]; simp) (by rw [← D.hval])
    (by rw [← Category.assoc D.δ, ← D.hval]; simp) D.hval.symm
    (nf D.γ (D.α ≫ f) (f' ≫ D.α ≫ f) (Or.inl hγn) (by rw [e1]; simp))
    (ir' D.α D.hα)
    (nf D.δ (D.β ≫ f) (f' ≫ D.α ≫ f) (Or.inl D.hδ.2.1) (by rw [e3]; simp))
    (ir' D.β D.hβ)
    (nf (D.γ ≫ η₁) (η₂ ≫ D.γ) (D.α ≫ f) (Or.inl hγη₁) (by rw [e2]; simp))
    (nf (D.γ ≫ η₁) (η₂ ≫ D.δ) (D.β ≫ f) (Or.inl hγη₁) (by rw [e4]; simp))
    (nf (D.γ ≫ η₁) (((η₂ ≫ D.γ) ≫ D.α) ≫ f) (𝟙 _) (Or.inl hγη₁) (by rw [e2]; simp))
    (ir' η₂ h₂)
    (nf (D.γ ≫ η₁) ((η₂ ≫ D.γ) ≫ D.α) f (Or.inl hγη₁) (by rw [e2]; simp))
    (ir' f' hf'i)
    (nf (D.γ ≫ D.α ≫ f) ((f' ≫ D.α) ≫ f) (𝟙 _) (Or.inl (by simpa using hγαf)) (by rw [e1]; simp))
    (nf (D.γ ≫ D.α ≫ f) (f' ≫ D.α) f (Or.inl (by simpa using hγαf)) (by rw [e1]; simp))
    (ir' D.γ D.hγ) (ir' D.δ D.hδ)
    (nf (𝟙 _) ((D.γ ≫ D.α) ≫ f) (f' ≫ D.α ≫ f) (Or.inr (not_isIso_comp_left' _ hf'))
      (by rw [e1]; simp))
    (nf (𝟙 _) (D.γ ≫ D.α) (f ≫ f' ≫ D.α ≫ f) (Or.inr (not_isIso_comp_left' _ hf.2.1))
      (by rw [e1]; simp))
    (nf (D.γ ≫ D.α) (f ≫ f') (D.α ≫ f) (Or.inl hγα) (by rw [e1]; simp))
    (ir' f hf)
    (nf (D.γ ≫ D.α) (((f ≫ f') ≫ D.α) ≫ f) (𝟙 _) (Or.inl hγα) (by rw [e1]; simp))
    (nf (D.γ ≫ D.α) ((f ≫ f') ≫ D.α) f (Or.inl hγα) (by rw [e1]; simp))
    (ir' f hf)
    h₂.2.1 hf.2.1 hf' hγn D.hδ.2.1 D.hα.2.1 D.hβ.2.1 hf.2.1 D.apγδ D.apδγ D.apαβ D.apβα
    (fun ⟨g, hg⟩ ↦ D.nL ⟨g, by rw [hg, hff]⟩)
    (fun ⟨g, hg⟩ ↦ D.nL ⟨f ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hff]⟩)
    ?_ ?_
    (fun ⟨g, hg⟩ ↦ D.nB ⟨g, by rw [hg, hff]⟩)
    (fun ⟨g, hg⟩ ↦ D.nB ⟨f ≫ g, by rw [Category.assoc, hg, hff]⟩)
  · rintro ⟨g, hg⟩
    have e : (η₁ ≫ g) ≫ f' = (D.α ≫ f) ≫ f' := by
      rw [Category.assoc, hg, ← Category.assoc, ← hη, ← D.hD, ← hff]; simp
    exact D.bhv85 hM η₁ η₂ f f' h₁ h₂ hf hf'i hη hff.symm g
      (hR _ _ _ e (by rw [e, Category.assoc, hff]; exact hαω))
  · rintro ⟨g, hg⟩
    have e : (D.η ≫ g) ≫ f' = (D.α ≫ f) ≫ f' := by
      rw [Category.assoc, hg, ← D.hD, ← hff]; simp
    exact D.bhv85 hM η₁ η₂ f f' h₁ h₂ hf hf'i hη hff.symm (η₂ ≫ g)
      (by rw [← Category.assoc, ← hη]; exact hR _ _ _ e (by rw [e, Category.assoc, hff]; exact hαω))

/-- In the exceptional case, `μ ≫ φ = τ ≫ f` for an arrow `φ` forces `φ` to be `f`. -/
lemma reach_socle (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) {c z : P}
    (f : D.y ⟶ c) (f' : c ⟶ D.a) (hf : IsIrreducible f) (hff : f ≫ f' = D.ω')
    (hτf : D.τ ≫ f ≠ 0) (φ : z ⟶ c) (hφ : IsIrreducible φ) (μ : D.x ⟶ z)
    (hμ : μ ≫ φ = D.τ ≫ f) : ∃ g, g ≫ f = φ := by
  have hL : LeftCancel P := hM.left
  have hμ0 : μ ≠ 0 := fun h ↦ hτf (by rw [← hμ, h, zero_comp])
  rcases D.pos_div hM μ (D.pos_all hM hMo hG μ hμ0) with ⟨g, hg⟩ | ⟨ν, ν', hν, hνω, rfl⟩
  · have e : μ ≫ φ = μ ≫ (g ≫ f) := by rw [hμ, ← hg]; simp
    have e2 := hL _ _ _ e (by rw [hμ]; exact hτf)
    exact ⟨g, e2.symm⟩
  · exfalso
    have hτν : D.τ ≫ ν ≠ 0 := hμ0
    have hν' : ¬IsIso ν' := by
      intro h; apply hτν
      rw [show ν = D.ω' ≫ inv ν' by rw [← hνω]; simp, ← Category.assoc, D.τω'_zero hMo hG,
        zero_comp]
    have hνi : IsIrreducible ν := by
      by_contra h; exact D.ω_two hMo ν ν' hν hν' (Or.inl h) hνω.symm
    obtain ⟨g, hg⟩ := D.X4u hM hMo hG f ν hf hνi hτf hτν
    have := iso_of_arrow hνi hf g hg
    have e : D.τ ≫ f = D.τ ≫ f ≫ (inv g ≫ φ) := by
      rw [← hμ, ← hg]; simp
    obtain ⟨-, h2⟩ := IsRayCategory.eq_id_of_two_sided (D.τ ≫ f) hτf (𝟙 _) (inv g ≫ φ)
      (by rw [Category.id_comp]; exact e.trans (Category.assoc D.τ f _).symm)
    have : IsIso (inv g ≫ φ) := by rw [h2]; infer_instance
    exact hφ.2.1 (ray_isIso_factors (inv g) φ).2

/-- **In the exceptional case, `f` is the only arrow into its target** ([mild] figure 4.9,
second diagram). -/
theorem mex2 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen)
    (hE' : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬D.op.Exc) {c z : P}
    (f : D.y ⟶ c) (f' : c ⟶ D.a) (hf : IsIrreducible f) (hff : f ≫ f' = D.ω')
    (hf' : ¬IsIso f') (hτf : D.τ ≫ f ≠ 0) (φ : z ⟶ c) (hφ : IsIrreducible φ) :
    ∃ g, g ≫ f = φ := by
  by_contra hne
  have hf'i : IsIrreducible f' := by
    by_contra h; exact D.ω_two hMo f f' hf.2.1 hf' (Or.inr h) hff.symm
  have hR : RightCancel P := hM.right
  have hαω := D.αω'_ne_zero
  -- the conditions `g ≫ φ = X ≫ f`
  have key : ∀ {s : P} (X : s ⟶ D.y), X ≠ 0 → ¬∃ g, g ≫ φ = X ≫ f := by
    rintro s X hX ⟨g, hg⟩
    obtain ⟨h, hh⟩ := D.div_τ_op hM hMo hG hE' X hX
    exact hne (D.reach_socle hM hMo hG f f' hf hff hτf φ hφ (h ≫ g)
      (by rw [Category.assoc, hg, ← Category.assoc, hh]))
  have hτ0 := D.τ_ne_zero
  have hX : ∀ {s : P} (X : s ⟶ D.y) (Y : D.x ⟶ s), Y ≫ X ≠ 0 → X ≠ 0 :=
    fun X Y h h' ↦ h (by rw [h', comp_zero])
  set τ' := D.τ ≫ f with hτ'
  have hτ'n : ¬IsIso τ' := not_isIso_comp_right' _ hf.2.1
  have e1 : τ' = D.γ ≫ D.α ≫ f ≫ f' ≫ D.α ≫ f := by
    rw [hτ']; change (D.γ ≫ D.α ≫ D.ω' ≫ D.α) ≫ f = _; rw [← hff]; simp
  have e3 : τ' = D.δ ≫ D.β ≫ f ≫ f' ≫ D.α ≫ f := by rw [hτ', D.τ_w, ← hff]; simp
  have nf := fun {s t : P} (pp : D.x ⟶ s) (g : s ⟶ t) (q : t ⟶ c) (hpq : ¬IsIso pp ∨ ¬IsIso q)
    (h : pp ≫ g ≫ q = τ') ↦ nfp hτf pp g q hpq h
  have ir' : ∀ {s t : P} (e : s ⟶ t), IsIrreducible e → ¬FactorsThroughMorphism τ' e := by
    intro s t e he; rw [e1, show D.γ ≫ D.α ≫ f ≫ f' ≫ D.α ≫ f =
      (D.γ ≫ D.α ≫ f ≫ f' ≫ D.α) ≫ f by simp]
    exact irr_not_ftm_comp _ f (not_isIso_comp_left' _ D.hγ.2.1) hf.2.1 e he
  have hγn := D.hγ.2.1
  have hγα := not_isIso_comp_left' D.α hγn
  have hγαf := not_isIso_comp_left' f hγα
  have hτω : (D.γ ≫ D.α) ≫ f ≫ f' ≫ D.α ≠ 0 := by
    rw [← Category.assoc f, hff]; simpa using hτ0
  refine hM.not_mex2 τ' hτ'n hτf f f' D.α f D.γ D.δ D.β φ MEX2.not_isRepresentationFinite
    (by rw [← Category.assoc D.δ, ← D.hval]; simp) D.hval.symm
    (nf D.γ (D.α ≫ f) (f' ≫ D.α ≫ f) (Or.inl hγn) (by rw [e1]; simp))
    (ir' D.α D.hα)
    (nf D.δ (D.β ≫ f) (f' ≫ D.α ≫ f) (Or.inl D.hδ.2.1) (by rw [e3]; simp))
    (ir' D.β D.hβ) (ir' f' hf'i)
    (nf (D.γ ≫ D.α ≫ f) ((f' ≫ D.α) ≫ f) (𝟙 _) (Or.inl (by simpa using hγαf)) (by rw [e1]; simp))
    (nf (D.γ ≫ D.α ≫ f) (f' ≫ D.α) f (Or.inl (by simpa using hγαf)) (by rw [e1]; simp))
    (ir' D.γ D.hγ) (ir' D.δ D.hδ)
    (nf (𝟙 _) ((D.γ ≫ D.α) ≫ f) (f' ≫ D.α ≫ f) (Or.inr (not_isIso_comp_left' _ hf'))
      (by rw [e1]; simp))
    (nf (𝟙 _) (D.γ ≫ D.α) (f ≫ f' ≫ D.α ≫ f) (Or.inr (not_isIso_comp_left' _ hf.2.1))
      (by rw [e1]; simp))
    (nf (D.γ ≫ D.α) (f ≫ f') (D.α ≫ f) (Or.inl hγα) (by rw [e1]; simp))
    (nf (D.γ ≫ D.α) (((f ≫ f') ≫ D.α) ≫ f) (𝟙 _) (Or.inl hγα) (by rw [e1]; simp))
    (ir' f hf)
    (nf (D.γ ≫ D.α) ((f ≫ f') ≫ D.α) f (Or.inl hγα) (by rw [e1]; simp))
    (ir' f hf) (ir' φ hφ)
    hf.2.1 hf' D.hα.2.1 hf.2.1 hγn D.hδ.2.1 D.hβ.2.1 hφ.2.1 D.apγδ D.apδγ D.apαβ D.apβα
    (fun ⟨g, hg⟩ ↦ D.nL ⟨g, by rw [hg, hff]⟩)
    (fun ⟨g, hg⟩ ↦ D.nL ⟨f ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hff]⟩)
    ?_
    (fun ⟨g, hg⟩ ↦ D.nB ⟨g, by rw [hg, hff]⟩)
    (fun ⟨g, hg⟩ ↦ D.nB ⟨f ≫ g, by rw [Category.assoc, hg, hff]⟩)
    (fun ⟨g, hg⟩ ↦ hne ⟨g, hg⟩)
    (key (D.γ ≫ D.α) (hX _ (𝟙 _) (by simpa using fun h ↦ hτ0 (by
      change D.γ ≫ D.α ≫ D.ω' ≫ D.α = 0; rw [← Category.assoc D.γ, h]; simp))))
    (key D.α D.hα.1) (key D.β D.hβ.1)
    (by have := key (𝟙 D.y) (fun h ↦ hτ0 (by rw [← Category.comp_id D.τ, h, comp_zero]))
        simpa using this)
    (key _ (hX ((f ≫ f') ≫ D.α) (D.γ ≫ D.α) (by simpa using hτω)))
    (key _ (hX _ (D.γ ≫ D.α ≫ f) (by simpa using hτω)))
  · -- `g ≫ f' = γ`
    rintro ⟨g, hg⟩
    have e : (D.η ≫ g) ≫ f' = (D.α ≫ f) ≫ f' := by
      rw [Category.assoc, hg, ← D.hD, ← hff]; simp
    have e2 := hR _ _ _ e (by rw [e, Category.assoc, hff]; exact hαω)
    apply hτf
    rw [hτ', D.τ_σω, show ((D.γ ≫ D.η) ≫ D.γ ≫ D.α) ≫ f = ((D.γ ≫ D.η) ≫ (D.γ ≫ D.η)) ≫ g by
      simp only [Category.assoc]; rw [← e2], D.σσ_zero hMo hG, zero_comp]

/-- **In the exceptional case, `P_x` is projective-injective with socle `τ ≫ f`.** -/
theorem exc_projInj (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen)
    (hE' : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬D.op.Exc) {c : P}
    (f : D.y ⟶ c) (f' : c ⟶ D.a) (hf : IsIrreducible f) (hff : f ≫ f' = D.ω')
    (hf' : ¬IsIso f') (hτf : D.τ ≫ f ≠ 0) : ProjInjAt (D.τ ≫ f) := by
  refine projInjAt_of_div (D.τ ≫ f) hτf ?_ ?_
  · intro w μ hμ
    rcases D.pos_div hM μ (D.pos_all hM hMo hG μ hμ) with ⟨g, hg⟩ | ⟨ν, ν', hν, hνω, rfl⟩
    · exact ⟨g ≫ f, by rw [← Category.assoc, hg]⟩
    · have hν' : ¬IsIso ν' := by
        intro h; apply hμ
        rw [show ν = D.ω' ≫ inv ν' by rw [← hνω]; simp, ← Category.assoc, D.τω'_zero hMo hG,
          zero_comp]
      have hνi : IsIrreducible ν := by
        by_contra h; exact D.ω_two hMo ν ν' hν hν' (Or.inl h) hνω.symm
      obtain ⟨g, hg⟩ := D.X4u hM hMo hG f ν hf hνi hτf hμ
      exact ⟨g, by rw [Category.assoc, hg]⟩
  · intro w ν hν
    by_cases hνi : IsIso ν
    · exact ⟨(D.τ ≫ f) ≫ inv ν, by simp⟩
    obtain ⟨c', p, φ, hp⟩ := MildContour.exists_last_arrow ν hν hνi
    obtain ⟨g₀, hg₀⟩ := D.mex2 hM hMo hG hE' f f' hf hff hf' hτf φ.1 φ.2
    have hX : pathVal p ≫ g₀ ≠ 0 := fun h ↦ hν (by rw [hp, ← hg₀, ← Category.assoc, h, zero_comp])
    obtain ⟨h, hh⟩ := D.div_τ_op hM hMo hG hE' _ hX
    exact ⟨h, by rw [hp, ← hg₀, ← Category.assoc (pathVal p) g₀ f, ← Category.assoc h, hh]⟩

/-- The exceptional case does not happen on both sides. -/
theorem excl (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hE : D.Exc) :
    letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
    letI : DecidableEq Pᵒᵖ := Classical.decEq _; ¬D.op.Exc := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨c, f, f', hf, hff, hf', hτf⟩ := hE
  have hη := D.mex1 hM hMo f f' hf hff hf' hτf
  rintro ⟨c', g, g', hg, hgg, hg', -⟩
  have e : D.η = g'.unop ≫ g.unop := Quiver.Hom.op_inj hgg.symm
  rcases hη.2.2 _ g'.unop g.unop e with h | h
  · exact hg' ((isIso_unop_iff g').1 h)
  · exact hg.2.1 ((isIso_unop_iff g).1 h)

/-- **A diamond gives a projective-injective `P_x` in `P` or in `Pᵒᵖ`.** -/
theorem no_projInj (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen)
    (hN : NoProjInj P) : False := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  by_cases hE : D.Exc
  · obtain ⟨c, f, f', hf, hff, hf', hτf⟩ := hE
    exact hN _ (D.exc_projInj hM hMo hG (D.excl hM hMo ⟨c, f, f', hf, hff, hf', hτf⟩) f f' hf hff
      hf' hτf)
  · by_cases hE' : D.op.Exc
    · obtain ⟨c, f, f', hf, hff, hf', hτf⟩ := hE'
      exact hN.op _ (D.op.exc_projInj hMo hMo.op hG.op
        (D.op.excl hMo hMo.op ⟨c, f, f', hf, hff, hf', hτf⟩) f f' hf hff hf' hτf)
    · exact hN _ (D.projInjAt_τ hM hMo hG hE hE')

end DiamondData

/-- **[mild] Theorem 3, diamond case**: `DiamondStmt` holds. -/
theorem diamondStmt : DiamondStmt P k := by
  intro x y C ω' hω' hρ hM hMo hE hNPI _ _
  have hR : RightCancel P := hM.right
  rcases C.diamond_cases hM hω' hρ with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
  · exact C.caseA hM hω' hρ hg
  · exact C.caseB hM hρ g hg
  · exact (C.diamondData hM hω' hρ hg.symm).no_projInj hM hMo (by
      refine ⟨fun f hf ↦ ?_, ?_⟩
      · obtain ⟨n, hn, h⟩ := C.hρ f hf; exact ⟨n, hn, by rw [h, hρ]; rfl⟩
      · obtain ⟨π, hπ⟩ := hE x
        exact (C.diamondData hM hω' hρ hg.symm).genσ hM hMo (fun f hf ↦ by
          obtain ⟨n, hn, h⟩ := C.hρ f hf; exact ⟨n, hn, by rw [h, hρ]; rfl⟩) π hπ) hNPI
  · by_cases hD : ∃ η, η ≫ C.γ = C.α.1 ≫ ω'
    · obtain ⟨η, hη⟩ := hD
      exact (C.diamondData hM hω' hρ hη.symm).no_projInj hM hMo (by
        refine ⟨fun f hf ↦ ?_, ?_⟩
        · obtain ⟨n, hn, h⟩ := C.hρ f hf; exact ⟨n, hn, by rw [h, hρ]; rfl⟩
        · obtain ⟨π, hπ⟩ := hE x
          exact (C.diamondData hM hω' hρ hη.symm).genσ hM hMo (fun f hf ↦ by
            obtain ⟨n, hn, h⟩ := C.hρ f hf; exact ⟨n, hn, by rw [h, hρ]; rfl⟩) π hπ) hNPI
    · exact C.caseC hM hω' hρ hg.symm hD

end RayCat

end LargeIndecomposable
