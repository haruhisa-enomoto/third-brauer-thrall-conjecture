module

public import LargeIndecomposable.MildContours.Diamonds.Closure6
public import LargeIndecomposable.MildContours.Contours.Assembly
public import LargeIndecomposable.Cleaving.Shapes.ShapeD4B

/-!
# Diamond: generators and deep vanishing

`DiamondData.Gen D`: `ρ = ω' α` generates the radical of `End y` and `σ = γ η` that of
`End x` (self-dual). With it, the morphisms of `P_x` and `I_y` beyond `τ` vanish by
power counting:
* `τρ_zero`: `τ ≫ ρ = 0` (from `ω' ≫ η ∈ (τ)`), `στ_zero`: `σ ≫ τ = 0` (dual);
* `rad_τ`: `u ≫ τ = 0` for `u` in the radical of `End x`, `τ_rad`: `τ ≫ v = 0` for `v`
  in the radical of `End y`.
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

/-- The radical generators at `y` and at `x`. -/
structure Gen : Prop where
  hρ : ∀ f : D.y ⟶ D.y, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow (D.ω' ≫ D.α) n
  hσ : ∀ f : D.x ⟶ D.x, ¬IsIso f → ∃ n, 0 < n ∧ f = rpow (D.γ ≫ D.η) n

lemma Gen.op {D : DiamondData P} (hG : D.Gen) : D.op.Gen where
  hρ := by
    intro f hf
    obtain ⟨n, hn, h⟩ := hG.hσ f.unop (fun h' ↦ hf ((isIso_unop_iff f).1 h'))
    refine ⟨n, hn, ?_⟩
    change f = rpow (D.η.op ≫ D.γ.op) n
    rw [← op_comp, ← op_rpow, ← h]; rfl
  hσ := by
    intro f hf
    obtain ⟨n, hn, h⟩ := hG.hρ f.unop (fun h' ↦ hf ((isIso_unop_iff f).1 h'))
    refine ⟨n, hn, ?_⟩
    change f = rpow (D.α.op ≫ D.ω'.op) n
    rw [← op_comp, ← op_rpow, ← h]; rfl

/-- **`τ ≫ ρ = 0`.** -/
theorem τρ_zero (hM : MildHyp k P) (hG : D.Gen) : D.τ ≫ (D.ω' ≫ D.α) = 0 := by
  by_contra h
  have hL : LeftCancel P := hM.left
  obtain ⟨u, v, huv⟩ := D.zero
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = D.ω' ≫ D.α := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω, ω = D.γ ≫ D.α := ⟨_, rfl⟩
  have hρn : ¬IsIso ρ := by rw [hρ]; exact not_isIso_comp_left' _ D.hω'
  have hωn : ¬IsIso ω := by rw [hω]; exact not_isIso_comp_left' _ D.hγ.2.1
  obtain ⟨i, hi, hi'⟩ := hG.hρ (u ≫ ω) (not_isIso_comp_right' u hωn)
  obtain ⟨j, hj, hj'⟩ := hG.hρ (v ≫ ω) (not_isIso_comp_right' v hωn)
  rw [← hρ] at hi' hj'
  have hτρ : D.τ ≫ (D.ω' ≫ D.α) = ω ≫ rpow ρ 2 := by
    rw [hω, hρ]; simp [rpow_succ]
  have e : ω ≫ rpow ρ 2 = ω ≫ rpow ρ (i + 1 + j) := by
    have h1 : ω ≫ rpow ρ 2 = ω ≫ (D.ω' ≫ D.η) ≫ ω := by
      calc ω ≫ rpow ρ 2 = (D.γ ≫ D.α) ≫ D.ω' ≫ (D.α ≫ D.ω') ≫ D.α := by
            rw [hω, hρ]; simp [rpow_succ]
        _ = (D.γ ≫ D.α) ≫ D.ω' ≫ (D.η ≫ D.γ) ≫ D.α := by rw [D.hD]
        _ = ω ≫ (D.ω' ≫ D.η) ≫ ω := by rw [hω]; simp
    rw [h1, huv]
    have h2 : ω ≫ (u ≫ D.τ ≫ v) ≫ ω = ω ≫ (u ≫ ω) ≫ ρ ≫ (v ≫ ω) := by
      rw [hω, hρ]; simp
    rw [h2, hi', hj', rpow_comp_self_assoc, rpow_comp_rpow]
  have hne : ω ≫ rpow ρ 2 ≠ 0 := by rw [← hτρ]; exact h
  have e2 := hL _ _ _ e hne
  have h3 := MildContour.rpow_le_of_eq ρ hρn (m := 2) (n := i + 1 + j)
    (fun h0 ↦ hne (by rw [h0, comp_zero])) e2
  omega

/-- **`σ ≫ τ = 0`** (dual of `τρ_zero`). -/
theorem στ_zero (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) : (D.γ ≫ D.η) ≫ D.τ = 0 := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  have := D.op.τρ_zero hMo hG.op
  rw [op_τ] at this
  apply Quiver.Hom.op_inj
  rw [op_comp, op_zero]
  change D.τ.op ≫ (D.η.op ≫ D.γ.op) = 0 at this
  rw [← op_comp] at this
  exact this

/-- `u ≫ τ = 0` for `u` in the radical of `End x`. -/
lemma rad_τ (hMo : MildHyp k Pᵒᵖ) (hG : D.Gen) (u : D.x ⟶ D.x) (hu : ¬IsIso u) :
    u ≫ D.τ = 0 := by
  obtain ⟨n, hn, rfl⟩ := hG.hσ u hu
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rpow_succ, Category.assoc, D.στ_zero hMo hG, comp_zero]

/-- `τ ≫ v = 0` for `v` in the radical of `End y`. -/
lemma τ_rad (hM : MildHyp k P) (hG : D.Gen) (v : D.y ⟶ D.y) (hv : ¬IsIso v) :
    D.τ ≫ v = 0 := by
  obtain ⟨n, hn, rfl⟩ := hG.hρ v hv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rpow_succ', ← Category.assoc, D.τρ_zero hM hG, zero_comp]

/-- **`ω' ≫ η₁ ∈ (τ)`** for an arrow `η₁` beginning `η` (the `D̃₄` star at `a`). -/
theorem zero₁ (hM : MildHyp k P) {c : P} (η₁ : D.a ⟶ c) (h₁ : IsIrreducible η₁) (r : c ⟶ D.x)
    (hη : D.η = η₁ ≫ r) : FactorsThroughMorphism D.τ (D.ω' ≫ η₁) := by
  by_contra h
  have hτ0 := D.τ_ne_zero
  have hγn := D.hγ.2.1
  have hτ1 : D.τ = D.γ ≫ η₁ ≫ r ≫ D.γ ≫ D.α := by rw [D.τ_η, hη]; simp
  have n1 : ¬∃ g, D.α ≫ g = η₁ := fun ⟨g, hg⟩ ↦ D.nB' ⟨g ≫ r, by rw [← Category.assoc, hg, hη]⟩
  have n2 : ¬∃ g, η₁ ≫ g = D.α := by
    rintro ⟨g, hg⟩
    rcases D.hα.2.2 _ η₁ g hg.symm with h' | h'
    · exact h₁.2.1 h'
    · exact D.nB' ⟨inv g ≫ r, by rw [hη, ← hg]; simp⟩
  exact hM.not_md4b D.τ D.τ_not_isIso hτ0 D.γ D.ω' D.α η₁
    (D.irr_not_ftm' D.α D.hα) (D.irr_not_ftm' η₁ h₁) (D.irr_not_ftm' D.γ D.hγ)
    (nfp hτ0 (𝟙 _) (D.γ ≫ D.α) (D.ω' ≫ D.α) (Or.inr (not_isIso_comp_left' _ D.hω')) (by simp))
    (nfp hτ0 (𝟙 _) (D.γ ≫ η₁) (r ≫ D.γ ≫ D.α)
      (Or.inr (not_isIso_comp_right' _ (not_isIso_comp_left' _ hγn))) (by rw [hτ1]; simp))
    (nfp hτ0 (D.γ ≫ D.α) D.ω' D.α (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    (nfp hτ0 (D.γ ≫ D.α) (D.ω' ≫ D.α) (𝟙 _) (Or.inl (not_isIso_comp_left' _ hγn)) (by simp))
    h hγn D.hω' D.hα.2.1 h₁.2.1 n1 n2 D.nB D.nA

end DiamondData

end RayCat

end LargeIndecomposable
