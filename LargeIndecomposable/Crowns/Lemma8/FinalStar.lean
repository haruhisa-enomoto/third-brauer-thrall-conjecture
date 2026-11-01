module

public import LargeIndecomposable.Crowns.Basic.CrownSix
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8S04
public import LargeIndecomposable.Cleaving.Shapes.ShapeF89
public import LargeIndecomposable.Cleaving.Shapes.ShapeF8S31
public import LargeIndecomposable.Cleaving.Shapes.ShapeF810
public import LargeIndecomposable.Cleaving.Shapes.ShapeF810D

/-!
# BO13a Lemma 8, the final star (step R5)

Three morphisms `V₁, σ₂', r` into `a` and three `V₂, ρ₁', t` out of `a` with
`σ₂' ≫ V₂ = r ≫ ρ₁' = V₁ ≫ t = 0`, whose other six composites form a crown
`(σ₂, ρ₁, σ₁, ρₙ, μ, ν)` of length six (`μ = r ≫ t`, `ν = σ₂' ≫ t`), with
`σ₁` long and `ρ₁, ρₙ, ν` not long, are impossible (`MulBasis.l8_star`).
Reconstruction: `notes/2026-10-30-074207-bo13a-lemma8-reconstruction.md`.

* `RayCat.contour_through`: a long morphism with a factorization `f ≫ g` has a
  contour one of whose paths passes through the middle object.
* `RayCat.contour_first_cross`: the first arrow of the other path is incomparable with
  the first part of that path.
* `MulBasis.l8_gout`, `MulBasis.l8_gin` (and `_path` forms): figure 8.10 or a `D̃₄` star,
  and the duals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- **A contour through a factorization.** -/
lemma contour_through {X a Y : P} {μ : X ⟶ Y} (hμ : IsLong μ) (hc : ¬NotInContour μ)
    (f : X ⟶ a) (g : a ⟶ Y) (hfg : f ≫ g = μ) :
    ∃ (p₁ : Quiver.Path (RayVert.mk X) (RayVert.mk a)) (p₂ : Quiver.Path (RayVert.mk a)
      (RayVert.mk Y)) (q : Quiver.Path (RayVert.mk X) (RayVert.mk Y)),
      pathVal p₁ = f ∧ pathVal p₂ = g ∧ pathVal q = μ ∧ ¬Interlaced (p₁.comp p₂) q := by
  have hf0 : f ≠ 0 := fun h ↦ hμ.1 (by rw [← hfg, h, zero_comp])
  have hg0 : g ≠ 0 := fun h ↦ hμ.1 (by rw [← hfg, h, comp_zero])
  obtain ⟨p₁, hp₁⟩ := exists_path f hf0
  obtain ⟨p₂, hp₂⟩ := exists_path g hg0
  obtain ⟨v, w, hv, hw, hni⟩ : ∃ v w : Quiver.Path (RayVert.mk X) (RayVert.mk Y),
      pathVal v = μ ∧ pathVal w = μ ∧ ¬Interlaced v w := by
    by_contra h
    exact hc fun v w hv hw ↦ by
      by_contra hi
      exact h ⟨v, w, hv, hw, hi⟩
  by_cases h1 : Interlaced (p₁.comp p₂) v
  · refine ⟨p₁, p₂, w, hp₁, hp₂, hw, fun h2 ↦ hni ?_⟩
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) h2
  · exact ⟨p₁, p₂, v, hp₁, hp₂, hv, h1⟩

omit [IsRayCategory P] in
/-- A path of positive length if its value is not invertible. -/
lemma length_pos_of_not_isIso {x y : RayVert P} (p : Quiver.Path x y)
    (h : ¬IsIso (pathVal p)) : 0 < p.length := by
  cases p with
  | nil => exact absurd (IsIso.id _) h
  | cons _ _ => simp

/-- **The first arrow of the second path of a contour** through `a` is not comparable with
the part `i` of the first path up to `a`. -/
lemma contour_first_cross (hL : LeftCancel P) (hR : RightCancel P) {X₁ Z₁ : P} {a : RayVert P}
    {i : X₁ ⟶ a.out}
    {l : X₁ ⟶ Z₁} (hl : IsLong l) (p₁ : Quiver.Path (RayVert.mk X₁) a)
    (p₂ : Quiver.Path a (RayVert.mk Z₁)) (q : Quiver.Path (RayVert.mk X₁) (RayVert.mk Z₁))
    (hp₁ : pathVal p₁ = i)
    (hval : pathVal (p₁.comp p₂) = l) (hq : pathVal q = l) (hni : ¬Interlaced (p₁.comp p₂) q)
    (h₁ : 0 < p₁.length) (h₂ : 0 < p₂.length) :
    ∃ (T : P) (ψ : X₁ ⟶ T) (q'' : T ⟶ Z₁), IsIrreducible ψ ∧ ψ ≫ q'' = l ∧
      ¬IsIso q'' ∧ (¬∃ g, i ≫ g = ψ) ∧ ¬∃ g, ψ ≫ g = i := by
  obtain ⟨b, β, q', rfl⟩ := exists_first_arrow q (by rw [hq]; exact hl.2.1)
  have hq'0 : 0 < q'.length := by
    cases q' with
    | cons _ _ => simp
    | nil =>
      exfalso
      apply hl.2.2.1
      rw [← hq, Quiver.Path.comp_nil, pathVal_toPath]
      exact β.2
  have hv : pathVal (p₁.comp p₂) = pathVal (β.toPath.comp q') := by rw [hval, hq]
  have h0 : pathVal (p₁.comp p₂) ≠ 0 := by rw [hval]; exact hl.1
  refine ⟨b.out, β.1, pathVal q', β.2, by rw [← hq, pathVal_comp, pathVal_toPath],
    not_isIso_pathVal q' hq'0, ?_, ?_⟩
  · have := prefix_cross hL hR _ _ hv h0 hni p₁ p₂ β.toPath q' rfl rfl h₁ hq'0
    simpa only [pathVal_toPath, hp₁] using this
  · have := prefix_cross hL hR _ _ hv.symm (by rw [← hv]; exact h0) (fun h ↦ hni h.symm)
      β.toPath q' p₁ p₂ rfl rfl (by simp) h₂
    simpa only [pathVal_toPath, hp₁] using this

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **The star with an out-split** (BO13a figure 8.10 and the `D̃₄` star `v₁, ρ₃', σ₂', a`):
in-arrows `i₁, i₂, i₃` and out-arrows `o`, `A ≫ e` at `a`; the long `Λ = i₁ ≫ A ≫ e` with
its valley neighbour `Π = i₁ ≫ o` and peak neighbour `Ξ = i₃ ≫ A ≫ e`, the long
`Θ = i₂ ≫ o` with `i₃ ≫ o = i₂ ≫ A ≫ e = 0`; `β` is the first arrow of a second path of `Λ`. -/
theorem l8_gout
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {a X₁ X₂ X₃ Y c Z T : P} (i₁ : X₁ ⟶ a) (i₂ : X₂ ⟶ a) (i₃ : X₃ ⟶ a) (o : a ⟶ Y)
    (A : a ⟶ c) (e : c ⟶ Z) (hiA : ¬IsIso A) (hie : ¬IsIso e)
    (hΛ : IsLong (i₁ ≫ A ≫ e)) (hΘ : IsLong (i₂ ≫ o))
    (hΘΛ : ¬FactorsThroughMorphism (i₁ ≫ A ≫ e) (i₂ ≫ o))
    (hPil : ¬IsLong (i₁ ≫ o)) (hPi0 : i₁ ≫ o ≠ 0) (hΞ0 : i₃ ≫ A ≫ e ≠ 0)
    (hv1 : ¬∃ g, (i₁ ≫ A ≫ e) ≫ g = i₁ ≫ o) (hv2 : ¬∃ g, (i₁ ≫ o) ≫ g = i₁ ≫ A ≫ e)
    (hq1 : ¬∃ g, g ≫ (i₁ ≫ A ≫ e) = i₃ ≫ A ≫ e) (hq2 : ¬∃ g, g ≫ (i₃ ≫ A ≫ e) = i₁ ≫ A ≫ e)
    (hp1 : ¬∃ g, g ≫ (i₂ ≫ o) = i₁ ≫ o) (hp2 : ¬∃ g, g ≫ (i₁ ≫ o) = i₂ ≫ o)
    (hz₃ : i₃ ≫ o = 0) (hz₂ : i₂ ≫ A ≫ e = 0)
    (β : X₁ ⟶ T) (hiβ : ¬IsIso β) (h0β : ¬FactorsThroughMorphism (i₁ ≫ A ≫ e) β)
    (hβV : ¬∃ g, β ≫ g = i₁) (hVβ : ¬∃ g, i₁ ≫ g = β) (hβA : ¬∃ g, β ≫ g = i₁ ≫ A)
    (hβPi : ¬∃ g, β ≫ g = i₁ ≫ o)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810.thin) k)) : False := by
  have hΘ0 := hΘ.1
  have hΛ0 := hΛ.1
  have r12 : ¬∃ g, g ≫ i₁ = i₂ := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hg, Category.assoc]⟩
  have r21 : ¬∃ g, g ≫ i₂ = i₁ := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hg, Category.assoc]⟩
  have r13 : ¬∃ g, g ≫ i₁ = i₃ := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hg, Category.assoc]⟩
  have r31 : ¬∃ g, g ≫ i₃ = i₁ := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hg, Category.assoc]⟩
  have r23 : ¬∃ g, g ≫ i₂ = i₃ := fun ⟨g, hg⟩ ↦
    hΞ0 (by rw [← hg, Category.assoc, hz₂, comp_zero])
  have r32 : ¬∃ g, g ≫ i₃ = i₂ := fun ⟨g, hg⟩ ↦
    hΘ0 (by rw [← hg, Category.assoc, hz₃, comp_zero])
  have hi₁ : ¬IsIso i₁ := fun _ ↦ r13 ⟨i₃ ≫ inv i₁, by simp⟩
  have hi₂ : ¬IsIso i₂ := fun _ ↦ r21 ⟨i₁ ≫ inv i₂, by simp⟩
  have hi₃ : ¬IsIso i₃ := fun _ ↦ r31 ⟨i₁ ≫ inv i₃, by simp⟩
  have hio : ¬IsIso o := fun _ ↦ hv2 ⟨inv o ≫ A ≫ e, by simp⟩
  have hAe0 : A ≫ e ≠ 0 := fun h ↦ hΛ0 (by rw [h, comp_zero])
  have hrA0 : i₃ ≫ A ≠ 0 := fun h ↦ hΞ0 (by rw [← Category.assoc, h, zero_comp])
  have hVA0 : (i₁ ≫ A) ≫ e ≠ 0 := by rw [Category.assoc]; exact hΛ0
  have hrA0' : (i₃ ≫ A) ≫ e ≠ 0 := by rw [Category.assoc]; exact hΞ0
  by_cases hz : i₂ ≫ A = 0
  · exact B.not_f810 hmin hL hR (i₁ ≫ A ≫ e) hΛ.2.1 hΛ0 β i₁ i₃ i₂ A o hD hz₃ hz
      (h0_a_c := not_ftm_prefix_of_long hΛ hie hAe0)
      (h0_a_y₁ := not_ftm_suffix_of_long hΛ hi₁ hPi0)
      (h0_x_a := not_ftm_prefix_of_long hΛ hio hPi0)
      (h0_x_c := not_ftm_prefix_of_long hΛ hie hVA0) (h0_x_c' := h0β)
      (h0_x_y₁ := not_factorsThrough_of_not_isLong hΛ hPi0 hPil)
      (h0_xn_a := not_ftm_prefix_of_long hΛ hiA hrA0)
      (h0_xn_c := not_ftm_prefix_of_long hΛ hie hrA0')
      (h0_x₂_a := not_ftm_prefix_of_long hΛ hio hΘ0) (h0_x₂_y₁ := hΘΛ)
      (hi_W₁ := hiβ) (hi_V₁ := hi₁) (hi_r := hi₃) (hi_σ₂' := hi₂) (hi_A := hiA) (hi_ρ₁' := hio)
      (hlft_a_c_y₁ := fun ⟨g, hg⟩ ↦ hΘ0 (by rw [← hg, ← Category.assoc, hz, zero_comp]))
      (hlft_a_y₁_c := fun ⟨g, hg⟩ ↦ hv2 ⟨g ≫ e, by rw [← hg]; simp⟩)
      (hlft_x_a_c' := hVβ) (hlft_x_c'_a := hβV) (hlft_x_c'_c := hβA) (hlft_x_c'_y₁ := hβPi)
      (hrgt_xn_x_a := r13) (hrgt_x₂_x_a := r12) (hrgt_x_xn_a := r31) (hrgt_x₂_xn_a := r32)
      (hrgt_x_x₂_a := r21) (hrgt_xn_x₂_a := r23)
  · refine B.not_f8s31 hmin hL hR (i₂ ≫ o) hΘ.2.1 hΘ0 i₁ i₃ i₂ A
      (h0_a_c := not_ftm_prefix_of_long hΘ hie hAe0)
      (h0_x_a := not_ftm_prefix_of_long hΘ hio hPi0)
      (h0_x_c := not_ftm_prefix_of_long hΘ hie hVA0)
      (h0_xn_a := not_ftm_prefix_of_long hΘ hiA hrA0)
      (h0_xn_c := not_ftm_prefix_of_long hΘ hie hrA0')
      (h0_x₂_a := not_ftm_prefix_of_long hΘ hio hΘ0) (h0_x₂_c := ?_)
      (hi_V₁ := hi₁) (hi_r := hi₃) (hi_σ₂' := hi₂) (hi_A := hiA)
      (hr_V₁_r_xn := r13) (hr_V₁_σ₂'_x₂ := r12) (hr_r_V₁_x := r31) (hr_r_σ₂'_x₂ := r32)
      (hr_σ₂'_V₁_x := r21) (hr_σ₂'_r_xn := r23)
    intro h
    obtain ⟨hx, hy, he⟩ := hΘ.2.2.2 (i₂ ≫ A) hz h
    subst hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    have hAo : A = o := hL i₂ A o he hz
    exact hv2 ⟨e, by rw [hAo]; simp⟩

include B in
/-- **The star with an in-split** (the dual of `l8_gout`): out-arrows `o₁, o₂, o₃` and
in-arrows `j`, `e ≫ d` at `a`; the long `Λ = e ≫ d ≫ o₁` with its peak neighbour
`Π = j ≫ o₁` and valley neighbour `Ξ = e ≫ d ≫ o₃`, the long `Θ = j ≫ o₂` with
`j ≫ o₃ = e ≫ d ≫ o₂ = 0`; `ω` is the last arrow of a second path of `Λ`. -/
theorem l8_gin
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {a Y₁ Y₂ Y₃ X J m T : P} (o₁ : a ⟶ Y₁) (o₂ : a ⟶ Y₂) (o₃ : a ⟶ Y₃) (j : J ⟶ a)
    (e : X ⟶ m) (d : m ⟶ a) (hie : ¬IsIso e) (hid : ¬IsIso d)
    (hΛ : IsLong (e ≫ d ≫ o₁)) (hΘ : IsLong (j ≫ o₂))
    (hΘΛ : ¬FactorsThroughMorphism (e ≫ d ≫ o₁) (j ≫ o₂))
    (hPil : ¬IsLong (j ≫ o₁)) (hPi0 : j ≫ o₁ ≠ 0) (hΞ0 : e ≫ d ≫ o₃ ≠ 0)
    (hp1 : ¬∃ g, g ≫ (e ≫ d ≫ o₁) = j ≫ o₁) (hp2 : ¬∃ g, g ≫ (j ≫ o₁) = e ≫ d ≫ o₁)
    (hq1 : ¬∃ g, (e ≫ d ≫ o₁) ≫ g = e ≫ d ≫ o₃) (hq2 : ¬∃ g, (e ≫ d ≫ o₃) ≫ g = e ≫ d ≫ o₁)
    (hv1 : ¬∃ g, (j ≫ o₂) ≫ g = j ≫ o₁) (hv2 : ¬∃ g, (j ≫ o₁) ≫ g = j ≫ o₂)
    (hz₃ : j ≫ o₃ = 0) (hz₂ : e ≫ d ≫ o₂ = 0)
    (ω : T ⟶ Y₁) (hiω : ¬IsIso ω) (h0ω : ¬FactorsThroughMorphism (e ≫ d ≫ o₁) ω)
    (hωo : ¬∃ g, g ≫ ω = o₁) (hoω : ¬∃ g, g ≫ o₁ = ω) (hωd : ¬∃ g, g ≫ ω = d ≫ o₁)
    (hωPi : ¬∃ g, g ≫ ω = j ≫ o₁)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810D.thin) k)) : False := by
  have hΘ0 := hΘ.1
  have hΛ0 := hΛ.1
  have l12 : ¬∃ g, o₁ ≫ g = o₂ := fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hg, Category.assoc]⟩
  have l21 : ¬∃ g, o₂ ≫ g = o₁ := fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hg, Category.assoc]⟩
  have l13 : ¬∃ g, o₁ ≫ g = o₃ := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hg]; simp⟩
  have l31 : ¬∃ g, o₃ ≫ g = o₁ := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hg]; simp⟩
  have l23 : ¬∃ g, o₂ ≫ g = o₃ := fun ⟨g, hg⟩ ↦
    hΞ0 (by rw [← hg, ← Category.assoc, ← Category.assoc, Category.assoc e, hz₂, zero_comp])
  have l32 : ¬∃ g, o₃ ≫ g = o₂ := fun ⟨g, hg⟩ ↦
    hΘ0 (by rw [← hg, ← Category.assoc, hz₃, zero_comp])
  have hio₁ : ¬IsIso o₁ := fun _ ↦ l13 ⟨inv o₁ ≫ o₃, by simp⟩
  have hio₂ : ¬IsIso o₂ := fun _ ↦ l21 ⟨inv o₂ ≫ o₁, by simp⟩
  have hio₃ : ¬IsIso o₃ := fun _ ↦ l31 ⟨inv o₃ ≫ o₁, by simp⟩
  have hij : ¬IsIso j := fun _ ↦ hp2 ⟨e ≫ d ≫ inv j, by simp⟩
  have hed0 : e ≫ d ≠ 0 := fun h ↦ hΛ0 (by rw [← Category.assoc, h, zero_comp])
  have hdo₃0 : d ≫ o₃ ≠ 0 := fun h ↦ hΞ0 (by rw [h, comp_zero])
  by_cases hz : d ≫ o₂ = 0
  · exact B.not_f810d hmin hL hR (e ≫ d ≫ o₁) hΛ.2.1 hΛ0 ω o₁ o₂ o₃ d j hD hz hz₃
      (h0_a_y₀ := not_ftm_suffix_of_long hΛ hij hΘ0)
      (h0_a_y₁ := not_ftm_suffix_of_long hΛ hij hPi0)
      (h0_a_z₂ := not_ftm_suffix_of_long hΛ hid hdo₃0)
      (h0_m_a := not_ftm_suffix_of_long hΛ hie hed0)
      (h0_m_y₁ := not_ftm_suffix_of_long hΛ hie hΛ0)
      (h0_m_z₂ := not_ftm_suffix_of_long hΛ hie hΞ0) (h0_tω_y₁ := h0ω)
      (h0_x_a := not_ftm_prefix_of_long hΛ hio₁ hPi0) (h0_x_y₀ := hΘΛ)
      (h0_x_y₁ := not_factorsThrough_of_not_isLong hΛ hPi0 hPil)
      (hi_ω := hiω) (hi_ρ₁' := hio₁) (hi_V₂ := hio₂) (hi_ρ₂' := hio₃) (hi_d := hid) (hi_V₁ := hij)
      (hlft_a_y₀_y₁ := l21) (hlft_a_y₀_z₂ := l23) (hlft_a_y₁_y₀ := l12) (hlft_a_y₁_z₂ := l13)
      (hlft_a_z₂_y₁ := l31) (hlft_a_z₂_y₀ := l32) (hrgt_tω_a_y₁ := hoω)
      (hrgt_x_m_a := fun ⟨g, hg⟩ ↦ hΘ0 (by rw [← hg, Category.assoc, hz, comp_zero]))
      (hrgt_a_tω_y₁ := hωo) (hrgt_m_tω_y₁ := hωd) (hrgt_x_tω_y₁ := hωPi)
      (hrgt_m_x_a := fun ⟨g, hg⟩ ↦ hΞ0 (by rw [← hg, Category.assoc, hz₃, comp_zero, comp_zero]))
  · refine B.not_f8s13 hmin hL hR (j ≫ o₂) hΘ.2.1 hΘ0 d o₁ o₂ o₃
      (h0_c_y₀ := not_ftm_suffix_of_long hΘ hij hPi0)
      (h0_c_y₁ := not_ftm_suffix_of_long hΘ hij hΘ0)
      (h0_c_z₂ := not_ftm_suffix_of_long hΘ hid hdo₃0)
      (h0_a_c := not_ftm_suffix_of_long hΘ hie hed0)
      (h0_a_y₀ := not_ftm_suffix_of_long hΘ hie hΛ0) (h0_a_y₁ := ?_)
      (h0_a_z₂ := not_ftm_suffix_of_long hΘ hie hΞ0)
      (hi_A := hid) (hi_Bm := hio₁) (hi_r₁ := hio₂) (hi_r₂ := hio₃)
      (hl_Bm_r₁_y₁ := l12) (hl_Bm_r₂_z₂ := l13) (hl_r₁_Bm_y₀ := l21) (hl_r₁_r₂_z₂ := l23)
      (hl_r₂_Bm_y₀ := l31) (hl_r₂_r₁_y₁ := l32)
    intro h
    obtain ⟨hx, hy, he⟩ := hΘ.2.2.2 (d ≫ o₂) hz h
    subst hx
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    have hdj : d = j := hR d j o₂ he hz
    exact hp2 ⟨e, by rw [hdj]⟩

include B in
/-- `l8_gout` from a contour `(p₁ p₂, q)` of `Λ = i₁ ≫ U` through `a` with `Π ≤ Λ`. -/
theorem l8_gout_path
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    {a : RayVert P} {X₁ X₂ X₃ Y Z : P} (i₁ : X₁ ⟶ a.out) (i₂ : X₂ ⟶ a.out) (i₃ : X₃ ⟶ a.out)
    (o : a.out ⟶ Y) (U : a.out ⟶ Z)
    (hΛ : IsLong (i₁ ≫ U)) (hΘ : IsLong (i₂ ≫ o))
    (hΘΛ : ¬FactorsThroughMorphism (i₁ ≫ U) (i₂ ≫ o))
    (hPil : ¬IsLong (i₁ ≫ o)) (hPi0 : i₁ ≫ o ≠ 0) (hΞ0 : i₃ ≫ U ≠ 0)
    (hv1 : ¬∃ g, (i₁ ≫ U) ≫ g = i₁ ≫ o) (hv2 : ¬∃ g, (i₁ ≫ o) ≫ g = i₁ ≫ U)
    (hq1 : ¬∃ g, g ≫ (i₁ ≫ U) = i₃ ≫ U) (hq2 : ¬∃ g, g ≫ (i₃ ≫ U) = i₁ ≫ U)
    (hp1 : ¬∃ g, g ≫ (i₂ ≫ o) = i₁ ≫ o) (hp2 : ¬∃ g, g ≫ (i₁ ≫ o) = i₂ ≫ o)
    (hz₃ : i₃ ≫ o = 0) (hz₂ : i₂ ≫ U = 0)
    (hle : FactorsThroughMorphism (i₁ ≫ o) (i₁ ≫ U))
    (p₁ : Quiver.Path (RayVert.mk X₁) a) (p₂ : Quiver.Path a (RayVert.mk Z))
    (q : Quiver.Path (RayVert.mk X₁) (RayVert.mk Z)) (hp₁ : pathVal p₁ = i₁)
    (hp₂ : pathVal p₂ = U) (hq : pathVal q = i₁ ≫ U) (hni : ¬Interlaced (p₁.comp p₂) q)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810.thin) k)) : False := by
  have hΛ0 := hΛ.1
  have hiU : ¬IsIso U := fun _ ↦ hv1 ⟨inv U ≫ o, by simp⟩
  have hi₁ : ¬IsIso i₁ := fun _ ↦ hq1 ⟨i₃ ≫ inv i₁, by simp⟩
  obtain ⟨φ, ψ, hφψ⟩ := hle
  obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR hv2 i₁ U o rfl rfl φ ψ hφψ.symm hΛ0
  obtain ⟨c, p₂', e, rfl⟩ := exists_last_arrow p₂ (by rw [hp₂]; exact hiU)
  have hp₂'0 : 0 < p₂'.length := by
    cases p₂' with
    | cons _ _ => simp
    | nil =>
      exfalso
      have hUe : U = e.1 := by rw [← hp₂]; exact Category.id_comp _
      rcases e.2.2.2 m' d₁ d₂ (by rw [← hUe, hd]) with h | h
      · exact hd₁ h
      · exact hd₂ h
  obtain ⟨b, β, q', rfl⟩ := exists_first_arrow q (by rw [hq]; exact hΛ.2.1)
  have hq'0 : 0 < q'.length := by
    cases q' with
    | cons _ _ => simp
    | nil =>
      exfalso
      apply hΛ.2.2.1
      rw [← hq, Quiver.Path.comp_nil, pathVal_toPath]
      exact β.2
  obtain ⟨b₁, α, p₁', rfl⟩ := exists_first_arrow p₁ (by rw [hp₁]; exact hi₁)
  have hp₁0 : 0 < (α.toPath.comp p₁').length := by simp
  have hval : pathVal ((α.toPath.comp p₁').comp (p₂'.cons e)) = pathVal (β.toPath.comp q') := by
    rw [hq, pathVal_comp, hp₁, hp₂]
  have h0 : pathVal ((α.toPath.comp p₁').comp (p₂'.cons e)) ≠ 0 := by rw [hval, hq]; exact hΛ0
  have h0' : pathVal (β.toPath.comp q') ≠ 0 := by rw [hq]; exact hΛ0
  have hβV : ¬∃ g, β.1 ≫ g = i₁ := by
    have := prefix_cross hL hR _ _ hval.symm h0' (fun h ↦ hni h.symm) β.toPath q'
      (α.toPath.comp p₁') (p₂'.cons e) rfl rfl (by simp) (by simp)
    simpa only [pathVal_toPath, hp₁] using this
  have hVβ : ¬∃ g, i₁ ≫ g = β.1 := by
    have := prefix_cross hL hR _ _ hval h0 hni (α.toPath.comp p₁') (p₂'.cons e) β.toPath q'
      rfl rfl hp₁0 hq'0
    simpa only [pathVal_toPath, hp₁] using this
  have hβA : ¬∃ g, β.1 ≫ g = i₁ ≫ pathVal p₂' := by
    have := prefix_cross hL hR _ _ hval.symm h0' (fun h ↦ hni h.symm) β.toPath q'
      ((α.toPath.comp p₁').comp p₂') e.toPath rfl rfl (by simp) (by simp)
    simpa only [pathVal_toPath, pathVal_comp, hp₁] using this
  have hΛv : pathVal (α.toPath.comp (p₁'.comp (p₂'.cons e))) = i₁ ≫ U := by
    rw [← Quiver.Path.comp_assoc, pathVal_comp, hp₁, hp₂]
  have hβPi : ¬∃ g, β.1 ≫ g = i₁ ≫ o := by
    rintro ⟨g, hg⟩
    refine B.not_factors_both hmin hL hR α β (p₁'.comp (p₂'.cons e)) q'
      (by rw [hΛv, hq]) (by rw [hΛv]; exact hΛ0) (by rw [← Quiver.Path.comp_assoc]; exact hni)
      ⟨Y, i₁ ≫ o⟩ hPi0 (fun ⟨c', hc'⟩ ↦ hv1 ⟨c', by rw [← hΛv]; exact hc'⟩)
      (fun ⟨c', hc'⟩ ↦ hv2 ⟨c', by rw [← hΛv]; exact hc'⟩) ⟨pathVal p₁' ≫ o, ?_⟩ ⟨g, hg⟩
    change α.1 ≫ pathVal p₁' ≫ o = i₁ ≫ o
    rw [← hp₁, pathVal_comp, pathVal_toPath, Category.assoc]
  have hβq : β.1 ≫ pathVal q' = i₁ ≫ U := by rw [← hq, pathVal_comp, pathVal_toPath]
  have h0β : ¬FactorsThroughMorphism (i₁ ≫ U) β.1 :=
    not_ftm_prefix_of_long hΛ (not_isIso_pathVal q' hq'0) (by rw [hβq]; exact hΛ0)
  have hU : U = pathVal p₂' ≫ e.1 := hp₂.symm
  subst hU
  exact B.l8_gout hmin hL hR i₁ i₂ i₃ o (pathVal p₂') e.1 (not_isIso_pathVal p₂' hp₂'0) e.2.2.1
    hΛ hΘ hΘΛ hPil hPi0 hΞ0 hv1 hv2 hq1 hq2 hp1 hp2 hz₃ hz₂ β.1 β.2.2.1 h0β hβV hVβ hβA hβPi hD

include B in
/-- `l8_gin` from a contour `(p₁ p₂, q)` of `Λ = D ≫ o₁` through `a` with `Π ≤ Λ`. -/
theorem l8_gin_path
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    {a : RayVert P} {Y₁ Y₂ Y₃ X J : P} (o₁ : a.out ⟶ Y₁) (o₂ : a.out ⟶ Y₂) (o₃ : a.out ⟶ Y₃)
    (j : J ⟶ a.out) (D : X ⟶ a.out)
    (hΛ : IsLong (D ≫ o₁)) (hΘ : IsLong (j ≫ o₂))
    (hΘΛ : ¬FactorsThroughMorphism (D ≫ o₁) (j ≫ o₂))
    (hPil : ¬IsLong (j ≫ o₁)) (hPi0 : j ≫ o₁ ≠ 0) (hΞ0 : D ≫ o₃ ≠ 0)
    (hp1 : ¬∃ g, g ≫ (D ≫ o₁) = j ≫ o₁) (hp2 : ¬∃ g, g ≫ (j ≫ o₁) = D ≫ o₁)
    (hq1 : ¬∃ g, (D ≫ o₁) ≫ g = D ≫ o₃) (hq2 : ¬∃ g, (D ≫ o₃) ≫ g = D ≫ o₁)
    (hv1 : ¬∃ g, (j ≫ o₂) ≫ g = j ≫ o₁) (hv2 : ¬∃ g, (j ≫ o₁) ≫ g = j ≫ o₂)
    (hz₃ : j ≫ o₃ = 0) (hz₂ : D ≫ o₂ = 0)
    (hle : FactorsThroughMorphism (j ≫ o₁) (D ≫ o₁))
    (p₁ : Quiver.Path (RayVert.mk X) a) (p₂ : Quiver.Path a (RayVert.mk Y₁))
    (q : Quiver.Path (RayVert.mk X) (RayVert.mk Y₁)) (hp₁ : pathVal p₁ = D)
    (hp₂ : pathVal p₂ = o₁) (hq : pathVal q = D ≫ o₁) (hni : ¬Interlaced (p₁.comp p₂) q)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810D.thin) k)) : False := by
  have hΛ0 := hΛ.1
  have hiD : ¬IsIso D := fun _ ↦ hp1 ⟨j ≫ inv D, by simp⟩
  have hio₁ : ¬IsIso o₁ := fun _ ↦ hq1 ⟨inv o₁ ≫ o₃, by simp⟩
  obtain ⟨φ, ψ, hφψ⟩ := hle
  obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL hp2 o₁ D j rfl rfl ψ φ hφψ.symm hΛ0
  obtain ⟨c, e, p₁', rfl⟩ := exists_first_arrow p₁ (by rw [hp₁]; exact hiD)
  have hp₁'0 : 0 < p₁'.length := by
    cases p₁' with
    | cons _ _ => simp
    | nil =>
      exfalso
      have hDe : D = e.1 := by rw [← hp₁, Quiver.Path.comp_nil, pathVal_toPath]
      rcases e.2.2.2 m' d₁ d₂ (by rw [← hDe, hd]) with h | h
      · exact hd₁ h
      · exact hd₂ h
  obtain ⟨b, q', ω, rfl⟩ := exists_last_arrow q (by rw [hq]; exact hΛ.2.1)
  have hq'0 : 0 < q'.length := by
    cases q' with
    | cons _ _ => simp
    | nil =>
      exfalso
      apply hΛ.2.2.1
      rw [← hq]
      change IsIrreducible (𝟙 _ ≫ ω.1)
      rw [Category.id_comp]
      exact ω.2
  obtain ⟨c₂, p₂'', l, rfl⟩ := exists_last_arrow p₂ (by rw [hp₂]; exact hio₁)
  have hval : pathVal ((e.toPath.comp p₁').comp (p₂''.cons l)) = pathVal (q'.comp ω.toPath) := by
    change _ = pathVal (q'.cons ω)
    rw [hq, pathVal_comp, hp₁, hp₂]
  have hni' : ¬Interlaced ((e.toPath.comp p₁').comp (p₂''.cons l)) (q'.comp ω.toPath) := hni
  have h0 : pathVal ((e.toPath.comp p₁').comp (p₂''.cons l)) ≠ 0 := by
    rw [pathVal_comp, hp₁, hp₂]; exact hΛ0
  have hωo : ¬∃ g, g ≫ ω.1 = o₁ := by
    have := (contour_cross hL hR (e.toPath.comp p₁') (p₂''.cons l) q' ω.toPath hval h0 hni'
      (by simp) (by simp)).1
    simpa only [pathVal_toPath, hp₂] using this
  have hoω : ¬∃ g, g ≫ o₁ = ω.1 := by
    have := (contour_cross hL hR q' ω.toPath (e.toPath.comp p₁') (p₂''.cons l) hval.symm
      (by rw [← hval]; exact h0) (fun h ↦ hni' h.symm) hq'0 (by simp)).1
    simpa only [pathVal_toPath, hp₂] using this
  have hωd : ¬∃ g, g ≫ ω.1 = pathVal p₁' ≫ o₁ := by
    have := (contour_cross hL hR e.toPath (p₁'.comp (p₂''.cons l)) q' ω.toPath
      (by rw [← Quiver.Path.comp_assoc]; exact hval) (by rw [← Quiver.Path.comp_assoc]; exact h0)
      (by rw [← Quiver.Path.comp_assoc]; exact hni') (by simp) (by simp)).1
    simpa only [pathVal_toPath, pathVal_comp, hp₂] using this
  have hΛv : pathVal (((e.toPath.comp p₁').comp p₂'').cons l) = D ≫ o₁ := by
    change pathVal ((e.toPath.comp p₁').comp (p₂''.cons l)) = _
    rw [pathVal_comp, hp₁, hp₂]
  have hωPi : ¬∃ g, g ≫ ω.1 = j ≫ o₁ := by
    rintro ⟨g, hg⟩
    refine B.not_factors_both_last hmin hL hR l ω ((e.toPath.comp p₁').comp p₂'') q'
      (by rw [hΛv, ← hq]) (by rw [hΛv]; exact hΛ0) hni (j ≫ o₁) hPi0
      (fun ⟨c', hc'⟩ ↦ hp1 ⟨c', by rw [← hΛv]; exact hc'⟩)
      (fun ⟨c', hc'⟩ ↦ hp2 ⟨c', by rw [← hΛv]; exact hc'⟩) ⟨j ≫ pathVal p₂'', ?_⟩ ⟨g, hg⟩
    rw [← hp₂, Category.assoc]
    rfl
  have hqω : pathVal q' ≫ ω.1 = D ≫ o₁ := hq
  have h0ω : ¬FactorsThroughMorphism (D ≫ o₁) ω.1 :=
    not_ftm_suffix_of_long hΛ (not_isIso_pathVal q' hq'0) (by rw [hqω]; exact hΛ0)
  have hDe : D = e.1 ≫ pathVal p₁' := by rw [← hp₁, pathVal_comp, pathVal_toPath]
  subst hDe
  exact B.l8_gin hmin hL hR o₁ o₂ o₃ j e.1 (pathVal p₁') e.2.2.1 (not_isIso_pathVal p₁' hp₁'0)
    (by simpa only [Category.assoc] using hΛ) hΘ (by simpa only [Category.assoc] using hΘΛ) hPil
    hPi0 (by simpa only [Category.assoc] using hΞ0) (by simpa only [Category.assoc] using hp1)
    (by simpa only [Category.assoc] using hp2) (by simpa only [Category.assoc] using hq1)
    (by simpa only [Category.assoc] using hq2) hv1 hv2 hz₃
    (by simpa only [Category.assoc] using hz₂) ω.1 ω.2.2.1
    (by simpa only [Category.assoc] using h0ω) hωo hoω hωd hωPi hD

include B in
/-- **BO13a Lemma 8, the final star.** In-arrows `V₁, σ₂', r` and out-arrows `V₂, ρ₁', t`
of `a` with `σ₂' ≫ V₂ = r ≫ ρ₁' = V₁ ≫ t = 0`, `σ₁ = V₁ ≫ V₂` long with a contour through
`a`, and `(σ₂, ρ₁, σ₁, ρₙ)` part of a chain: `(σ₂, ρ₁, σ₁, ρₙ, r ≫ t, σ₂' ≫ t)` is a crown,
and Lemma 5 c) with figures 8.9, 8.10 and their duals give a contradiction. -/
theorem l8_star
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {a : RayVert P} {x x₂ xn y₀ y₁ z : P} (V₁ : x ⟶ a.out) (σ₂' : x₂ ⟶ a.out)
    (r : xn ⟶ a.out) (V₂ : a.out ⟶ y₀) (ρ₁' : a.out ⟶ y₁) (t : a.out ⟶ z)
    (v₁ : Quiver.Path (RayVert.mk x) a) (v₂ : Quiver.Path a (RayVert.mk y₀))
    (q : Quiver.Path (RayVert.mk x) (RayVert.mk y₀)) (hv₁ : pathVal v₁ = V₁)
    (hv₂ : pathVal v₂ = V₂) (hq : pathVal q = V₁ ≫ V₂) (hni : ¬Interlaced (v₁.comp v₂) q)
    (hσ : IsLong (V₁ ≫ V₂)) (hρ₁l : ¬IsLong (V₁ ≫ ρ₁')) (hρnl : ¬IsLong (r ≫ V₂))
    (hνl : ¬IsLong (σ₂' ≫ t))
    (hz1 : σ₂' ≫ V₂ = 0) (hz2 : r ≫ ρ₁' = 0) (hz3 : V₁ ≫ t = 0)
    (hρ₁0 : V₁ ≫ ρ₁' ≠ 0) (hσ₂0 : σ₂' ≫ ρ₁' ≠ 0) (hρn0 : r ≫ V₂ ≠ 0) (hμ0 : r ≫ t ≠ 0)
    (hν0 : σ₂' ≫ t ≠ 0)
    (hp1 : ¬∃ c, c ≫ (V₁ ≫ ρ₁') = σ₂' ≫ ρ₁') (hp2 : ¬∃ c, c ≫ (σ₂' ≫ ρ₁') = V₁ ≫ ρ₁')
    (hv1 : ¬∃ c, (V₁ ≫ ρ₁') ≫ c = V₁ ≫ V₂) (hv2 : ¬∃ c, (V₁ ≫ V₂) ≫ c = V₁ ≫ ρ₁')
    (hq1 : ¬∃ c, c ≫ (r ≫ V₂) = V₁ ≫ V₂) (hq2 : ¬∃ c, c ≫ (V₁ ≫ V₂) = r ≫ V₂)
    (htV : ¬∃ g, t ≫ g = V₂) (hVt : ¬∃ g, V₂ ≫ g = t) (htρ : ¬∃ g, t ≫ g = ρ₁')
    (hρt : ¬∃ g, ρ₁' ≫ g = t)
    (hD810 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810.thin) k))
    (hD810D : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810D.thin) k)) :
    False := by
  have hσ0 := hσ.1
  -- the crown relations at `xn`, `z` and `x₂`
  have v3 : ¬∃ c, (r ≫ V₂) ≫ c = r ≫ t := fun ⟨c, hc⟩ ↦ hVt ⟨c, hL r _ _
    (by rw [← hc, Category.assoc]) (by rw [← Category.assoc, hc]; exact hμ0)⟩
  have v4 : ¬∃ c, (r ≫ t) ≫ c = r ≫ V₂ := fun ⟨c, hc⟩ ↦ htV ⟨c, hL r _ _
    (by rw [← hc, Category.assoc]) (by rw [← Category.assoc, hc]; exact hρn0)⟩
  have p5 : ¬∃ c, c ≫ (σ₂' ≫ t) = r ≫ t := fun ⟨c, hc⟩ ↦ hρn0 (by
    rw [← hR (c ≫ σ₂') r t (by rw [Category.assoc, hc]) (by rw [Category.assoc, hc]; exact hμ0),
      Category.assoc, hz1, comp_zero])
  have p6 : ¬∃ c, c ≫ (r ≫ t) = σ₂' ≫ t := fun ⟨c, hc⟩ ↦ hσ₂0 (by
    rw [← hR (c ≫ r) σ₂' t (by rw [Category.assoc, hc]) (by rw [Category.assoc, hc]; exact hν0),
      Category.assoc, hz2, comp_zero])
  have v5 : ¬∃ c, (σ₂' ≫ t) ≫ c = σ₂' ≫ ρ₁' := fun ⟨c, hc⟩ ↦ htρ ⟨c, hL σ₂' _ _
    (by rw [← hc, Category.assoc]) (by rw [← Category.assoc, hc]; exact hσ₂0)⟩
  have v6 : ¬∃ c, (σ₂' ≫ ρ₁') ≫ c = σ₂' ≫ t := fun ⟨c, hc⟩ ↦ hρt ⟨c, hL σ₂' _ _
    (by rw [← hc, Category.assoc]) (by rw [← Category.assoc, hc]; exact hν0)⟩
  -- non-invertibility
  have hiV₁ : ¬IsIso V₁ := fun _ ↦ hq2 ⟨r ≫ inv V₁, by simp⟩
  have hiV₂ : ¬IsIso V₂ := fun _ ↦ hv2 ⟨inv V₂ ≫ ρ₁', by simp⟩
  have hiσ₂' : ¬IsIso σ₂' := fun _ ↦ hp2 ⟨V₁ ≫ inv σ₂', by simp⟩
  have hiρ₁' : ¬IsIso ρ₁' := fun _ ↦ hv1 ⟨inv ρ₁' ≫ V₂, by simp⟩
  have hir : ¬IsIso r := fun _ ↦ p6 ⟨σ₂' ≫ inv r, by simp⟩
  have hit : ¬IsIso t := fun _ ↦ v4 ⟨inv t ≫ V₂, by simp⟩
  -- the crown of length six
  let C' := Crown.mk6 (σ₂' ≫ ρ₁') (V₁ ≫ ρ₁') (V₁ ≫ V₂) (r ≫ V₂) (r ≫ t) (σ₂' ≫ t) hp1 hp2 hv1
    hv2 hq1 hq2 v3 v4 p5 p6 v5 v6 hσ₂0 hρ₁0 hσ0 hρn0 hμ0 hν0
  have key : ∀ s : ℕ, C'.f s = Crown.mk6f (σ₂' ≫ ρ₁') (V₁ ≫ ρ₁') (V₁ ≫ V₂) (r ≫ V₂) (r ≫ t)
      (σ₂' ≫ t) (s % 6) := fun s ↦ Crown.mk6f_mod _ _ _ _ _ _ s
  -- every long morphism is `σ₂`, `σ₁` or `μ`
  have hin : ∀ {a' b' : P} (l : a' ⟶ b'), IsLong l →
      (⟨a', b', l⟩ : RayMor P) = ⟨x₂, y₁, σ₂' ≫ ρ₁'⟩ ∨ (⟨a', b', l⟩ : RayMor P) = ⟨x, y₀, V₁ ≫ V₂⟩ ∨
        (⟨a', b', l⟩ : RayMor P) = ⟨xn, z, r ≫ t⟩ := by
    intro a' b' l hl
    obtain ⟨s, hs⟩ := B.long_entry hmin C' l hl
    rw [key s] at hs
    have hb : s % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize s % 6 = u at hs hb
    interval_cases u
    · exact Or.inl hs.symm
    · exact absurd (isLong_of_rayMor_eq hs.symm hl) hρ₁l
    · exact Or.inr (Or.inl hs.symm)
    · exact absurd (isLong_of_rayMor_eq hs.symm hl) hρnl
    · exact Or.inr (Or.inr hs.symm)
    · exact absurd (isLong_of_rayMor_eq hs.symm hl) hνl
  -- a second long morphism (Lemma 5 c))
  have two : (IsLong (σ₂' ≫ ρ₁') ∧ (⟨x₂, y₁, σ₂' ≫ ρ₁'⟩ : RayMor P) ≠ ⟨x, y₀, V₁ ≫ V₂⟩) ∨
      (IsLong (r ≫ t) ∧ (⟨xn, z, r ≫ t⟩ : RayMor P) ≠ ⟨x, y₀, V₁ ≫ V₂⟩) := by
    obtain ⟨s, hl, hne⟩ := B.lemma5c hmin hL hR hQ hcont C' 2 hσ
    rw [key s] at hl hne
    have hb : s % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize s % 6 = u at hl hne hb
    interval_cases u
    · exact Or.inl ⟨hl, hne⟩
    · exact absurd hl hρ₁l
    · exact absurd rfl hne
    · exact absurd hl hρnl
    · exact Or.inr ⟨hl, hne⟩
    · exact absurd hl hνl
  -- a reducible non-long morphism lies below `σ₂`, `σ₁` or `μ`
  have hle_of : ∀ {X Y : P} (f : X ⟶ Y), f ≠ 0 → ¬IsIso f → ¬IsIrreducible f →
      (IsLong (σ₂' ≫ ρ₁') ∧ FactorsThroughMorphism f (σ₂' ≫ ρ₁')) ∨
        FactorsThroughMorphism f (V₁ ≫ V₂) ∨
          (IsLong (r ≫ t) ∧ FactorsThroughMorphism f (r ≫ t)) := by
    intro X Y f hf0 hfi hfr
    obtain ⟨a', b', l, hl, hfl⟩ := exists_isLong_above hf0 hfi hfr
    rcases hin l hl with h | h | h
    · cases h
      exact Or.inl ⟨hl, hfl⟩
    · cases h
      exact Or.inr (Or.inl hfl)
    · cases h
      exact Or.inr (Or.inr ⟨hl, hfl⟩)
  have hv : pathVal (v₁.comp v₂) = V₁ ≫ V₂ := by rw [pathVal_comp, hv₁, hv₂]
  by_cases hσ₂l : IsLong (σ₂' ≫ ρ₁') <;> by_cases hμl : IsLong (r ≫ t)
  · -- figure 8.9
    obtain ⟨p₂₁, p₂₂, q₂, hp₂₁, hp₂₂, hq₂, hni₂⟩ :=
      contour_through hσ₂l (hcont _ hσ₂l) σ₂' ρ₁' rfl
    obtain ⟨p₃₁, p₃₂, q₃, hp₃₁, hp₃₂, hq₃, hni₃⟩ := contour_through hμl (hcont _ hμl) r t rfl
    obtain ⟨T₁, ψ₁, c₁, hψ₁, hψc₁, hic₁, hl₁, hl₁'⟩ := contour_first_cross hL hR hσ v₁ v₂ q
      hv₁ hv hq hni (length_pos_of_not_isIso v₁ (by rw [hv₁]; exact hiV₁))
      (length_pos_of_not_isIso v₂ (by rw [hv₂]; exact hiV₂))
    obtain ⟨T₂, ψ₂, c₂, hψ₂, hψc₂, hic₂, hl₂, hl₂'⟩ := contour_first_cross hL hR hσ₂l p₂₁
      p₂₂ q₂ hp₂₁ (by rw [pathVal_comp, hp₂₁, hp₂₂]) hq₂ hni₂
      (length_pos_of_not_isIso p₂₁ (by rw [hp₂₁]; exact hiσ₂'))
      (length_pos_of_not_isIso p₂₂ (by rw [hp₂₂]; exact hiρ₁'))
    obtain ⟨T₃, ψ₃, c₃, hψ₃, hψc₃, hic₃, hl₃, hl₃'⟩ := contour_first_cross hL hR hμl p₃₁
      p₃₂ q₃ hp₃₁ (by rw [pathVal_comp, hp₃₁, hp₃₂]) hq₃ hni₃
      (length_pos_of_not_isIso p₃₁ (by rw [hp₃₁]; exact hir))
      (length_pos_of_not_isIso p₃₂ (by rw [hp₃₂]; exact hit))
    exact B.not_f89 hmin hL hR (V₁ ≫ V₂) hσ.2.1 hσ0 V₁ ψ₁ r ψ₃ σ₂' ψ₂
      (h0_x_a := not_ftm_prefix_of_long hσ hiV₂ hσ0)
      (h0_x_t₁ := not_ftm_prefix_of_long hσ hic₁ (by rw [hψc₁]; exact hσ0))
      (h0_xn_a := not_ftm_prefix_of_long hσ hit hμ0)
      (h0_xn_t₃ := not_ftm_prefix_of_long hσ hic₃ (by rw [hψc₃]; exact hμ0))
      (h0_x₂_a := not_ftm_prefix_of_long hσ hiρ₁' hσ₂0)
      (h0_x₂_t₂ := not_ftm_prefix_of_long hσ hic₂ (by rw [hψc₂]; exact hσ₂0))
      (hi_V₁ := hiV₁) (hi_ψ₁ := hψ₁.2.1) (hi_r := hir) (hi_ψ₃ := hψ₃.2.1) (hi_σ₂' := hiσ₂')
      (hi_ψ₂ := hψ₂.2.1) (hl_V₁_ψ₁_t₁ := hl₁) (hl_ψ₁_V₁_a := hl₁') (hl_r_ψ₃_t₃ := hl₃)
      (hl_ψ₃_r_a := hl₃') (hl_σ₂'_ψ₂_t₂ := hl₂) (hl_ψ₂_σ₂'_a := hl₂')
      (hr_V₁_r_xn := fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hg, Category.assoc]⟩)
      (hr_V₁_σ₂'_x₂ := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hg, Category.assoc]⟩)
      (hr_r_V₁_x := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hg, Category.assoc]⟩)
      (hr_r_σ₂'_x₂ := fun ⟨g, hg⟩ ↦ p6 ⟨g, by rw [← hg, Category.assoc]⟩)
      (hr_σ₂'_V₁_x := fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hg, Category.assoc]⟩)
      (hr_σ₂'_r_xn := fun ⟨g, hg⟩ ↦ p5 ⟨g, by rw [← hg, Category.assoc]⟩)
  · -- `σ₁, σ₂` are the only long morphisms: `ρ₁ ≤ σ₁` or `ρ₁ ≤ σ₂`
    have hne₂ : (⟨x₂, y₁, σ₂' ≫ ρ₁'⟩ : RayMor P) ≠ ⟨x, y₀, V₁ ≫ V₂⟩ := by
      rcases two with h | h
      · exact h.2
      · exact absurd h.1 hμl
    have hiρ₁ : ¬IsIso (V₁ ≫ ρ₁') := fun _ ↦ hv1 ⟨inv (V₁ ≫ ρ₁') ≫ V₁ ≫ V₂, by simp⟩
    have hrρ₁ : ¬IsIrreducible (V₁ ≫ ρ₁') := fun h ↦ by
      rcases h.2.2 _ V₁ ρ₁' rfl with h' | h'
      · exact hiV₁ h'
      · exact hiρ₁' h'
    rcases hle_of _ hρ₁0 hiρ₁ hrρ₁ with ⟨-, hle⟩ | hle | ⟨h', -⟩
    · obtain ⟨p₁, p₂, q₂, hp₁, hp₂, hq₂, hni₂⟩ := contour_through hσ₂l (hcont _ hσ₂l) σ₂' ρ₁' rfl
      exact B.l8_gin_path hmin hL hR hQ ρ₁' V₂ t V₁ σ₂' hσ₂l hσ (not_ftm_of_ne hσ₂l hσ0 hne₂.symm)
        hρ₁l hρ₁0 hν0 hp2 hp1 v6 v5 hv2 hv1 hz3 hz1 hle p₁ p₂ q₂ hp₁ hp₂ hq₂ hni₂ hD810D
    · exact B.l8_gout_path hmin hL hR hQ V₁ σ₂' r ρ₁' V₂ hσ hσ₂l (not_ftm_of_ne hσ hσ₂0 hne₂)
        hρ₁l hρ₁0 hρn0 hv2 hv1 hq2 hq1 hp2 hp1 hz2 hz1 hle v₁ v₂ q hv₁ hv₂ hq hni hD810
    · exact hμl h'
  · -- `σ₁, μ` are the only long morphisms: `ρₙ ≤ σ₁` or `ρₙ ≤ μ`
    have hneμ : (⟨xn, z, r ≫ t⟩ : RayMor P) ≠ ⟨x, y₀, V₁ ≫ V₂⟩ := by
      rcases two with h | h
      · exact absurd h.1 hσ₂l
      · exact h.2
    have hiρn : ¬IsIso (r ≫ V₂) := fun _ ↦ hq1 ⟨(V₁ ≫ V₂) ≫ inv (r ≫ V₂), by simp⟩
    have hrρn : ¬IsIrreducible (r ≫ V₂) := fun h ↦ by
      rcases h.2.2 _ r V₂ rfl with h' | h'
      · exact hir h'
      · exact hiV₂ h'
    rcases hle_of _ hρn0 hiρn hrρn with ⟨h', -⟩ | hle | ⟨-, hle⟩
    · exact hσ₂l h'
    · exact B.l8_gin_path hmin hL hR hQ V₂ t ρ₁' r V₁ hσ hμl (not_ftm_of_ne hσ hμ0 hneμ)
        hρnl hρn0 hρ₁0 hq2 hq1 hv2 hv1 v4 v3 hz2 hz3 hle v₁ v₂ q hv₁ hv₂ hq hni hD810D
    · obtain ⟨p₁, p₂, q₃, hp₁, hp₂, hq₃, hni₃⟩ := contour_through hμl (hcont _ hμl) r t rfl
      exact B.l8_gout_path hmin hL hR hQ r V₁ σ₂' V₂ t hμl hσ (not_ftm_of_ne hμl hσ0 hneμ.symm)
        hρnl hρn0 hν0 v4 v3 p6 p5 hq2 hq1 hz1 hz3 hle p₁ p₂ q₃ hp₁ hp₂ hq₃ hni₃ hD810
  · rcases two with h | h
    · exact hσ₂l h.1
    · exact hμl h.1

include B in
/-- **BO13a Lemma 8, reflecting case** (steps R2–R5): `l8_mid` with its last step done by the
out-star `V₂, ρ₁', ρ₂', s'` (`D̃₄`) and `l8_star`. -/
theorem l8_refl
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (h4 : NoCrown4 P) (Z : ZChain P) (s : ℕ) (hσ : IsLong (Z.σ (s + 2)))
    (hρ₁l : ¬IsLong (Z.ρ (s + 3))) (hρnl : ¬IsLong (Z.ρ (s + 2)))
    (hnbr : IsLong (Z.ρ (s + 1)) → ¬IsLong (Z.σ (s + 1)) ∧ ¬IsLong (Z.σ s))
    {a' b' : P} (τ' : a' ⟶ b') (hτ' : IsLong τ')
    (hτσ : (⟨_, _, Z.σ (s + 2)⟩ : RayMor P) ≠ ⟨_, _, τ'⟩)
    {a d : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (s + 3))) a)
    (v₂ : Quiver.Path a (RayVert.mk (Z.z (s + 2))))
    (β : RayVert.mk (Z.x (s + 3)) ⟶ d) (w' : Quiver.Path d (RayVert.mk (Z.z (s + 2))))
    (hv₁ : 0 < v₁.length) (hv₂ : 0 < v₂.length)
    (hv : pathVal (v₁.comp v₂) = Z.σ (s + 2))
    (hw : pathVal (β.toPath.comp w') = Z.σ (s + 2))
    (hni : ¬Interlaced (v₁.comp v₂) (β.toPath.comp w'))
    (hβρ : ¬∃ g, β.1 ≫ g = Z.ρ (s + 3))
    (ρ₁' : a.out ⟶ Z.z (s + 3)) (hρ₁' : pathVal v₁ ≫ ρ₁' = Z.ρ (s + 3))
    (σ₂' : Z.x (s + 4) ⟶ a.out) (hσ₂' : σ₂' ≫ ρ₁' = Z.σ (s + 3))
    (hz : σ₂' ≫ pathVal v₂ = 0) (r : Z.x (s + 2) ⟶ a.out) (hr : r ≫ pathVal v₂ = Z.ρ (s + 2))
    (hD86 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F86.thin) k))
    (hD87 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F87.thin) k))
    (hD810 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810.thin) k))
    (hD810D : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F810D.thin) k)) :
    False := by
  refine B.l8_mid hmin hL hR hQ hcont h4 Z s hσ hρ₁l hρnl hnbr τ' hτ' hτσ v₁ v₂ β w' hv₁ hv₂ hv hw
    hni hβρ ρ₁' hρ₁' σ₂' hσ₂' hz r hr hD86 hD87 ?_
  intro s' ρ₂' hs' hρ₂' hz2 hzV hzs hρ₂l
  have hv1 : ¬∃ c, Z.σ (s + 2) ≫ c = Z.ρ (s + 3) := Z.valley₁ (s + 2)
  have hv2 : ¬∃ c, Z.ρ (s + 3) ≫ c = Z.σ (s + 2) := Z.valley₂ (s + 2)
  have hp1 : ¬∃ c, c ≫ Z.σ (s + 3) = Z.ρ (s + 3) := Z.peak₁ (s + 3)
  have hp2 : ¬∃ c, c ≫ Z.ρ (s + 3) = Z.σ (s + 3) := Z.peak₂ (s + 3)
  have hw1 : ¬∃ c, Z.σ (s + 3) ≫ c = Z.ρ (s + 4) := Z.valley₁ (s + 3)
  have hw2 : ¬∃ c, Z.ρ (s + 4) ≫ c = Z.σ (s + 3) := Z.valley₂ (s + 3)
  have hq1 : ¬∃ c, c ≫ Z.σ (s + 2) = Z.ρ (s + 2) := Z.peak₁ (s + 2)
  have hq2 : ¬∃ c, c ≫ Z.ρ (s + 2) = Z.σ (s + 2) := Z.peak₂ (s + 2)
  have hu1 : ¬∃ c, Z.σ (s + 1) ≫ c = Z.ρ (s + 2) := Z.valley₁ (s + 1)
  have hu2 : ¬∃ c, Z.ρ (s + 2) ≫ c = Z.σ (s + 1) := Z.valley₂ (s + 1)
  have hV : pathVal v₁ ≫ pathVal v₂ = Z.σ (s + 2) := by rw [← pathVal_comp]; exact hv
  have hq : pathVal (β.toPath.comp w') = pathVal v₁ ≫ pathVal v₂ := by rw [hw, hV]
  -- the out-arrows `V₂, ρ₁', ρ₂', s'` of `a`
  have l_Vρ : ¬∃ g, pathVal v₂ ≫ g = ρ₁' := fun ⟨g, hg⟩ ↦
    hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ₁']⟩
  have l_ρV : ¬∃ g, ρ₁' ≫ g = pathVal v₂ := fun ⟨g, hg⟩ ↦
    hv2 ⟨g, by rw [← hρ₁', Category.assoc, hg, hV]⟩
  have l_Vρ₂ : ¬∃ g, pathVal v₂ ≫ g = ρ₂' := fun ⟨g, hg⟩ ↦
    Z.ρ_ne (s + 4) (by rw [← hρ₂', ← hg, ← Category.assoc, hz, zero_comp])
  have l_ρ₂V : ¬∃ g, ρ₂' ≫ g = pathVal v₂ := fun ⟨g, hg⟩ ↦
    hσ.1 (by rw [← hV, ← hg, ← Category.assoc, hzV, zero_comp])
  have l_Vs : ¬∃ g, pathVal v₂ ≫ g = s' := fun ⟨g, hg⟩ ↦
    hu2 ⟨g, by rw [← hr, Category.assoc, hg, hs']⟩
  have l_sV : ¬∃ g, s' ≫ g = pathVal v₂ := fun ⟨g, hg⟩ ↦
    hu1 ⟨g, by rw [← hs', Category.assoc, hg, hr]⟩
  have l_ρρ₂ : ¬∃ g, ρ₁' ≫ g = ρ₂' := fun ⟨g, hg⟩ ↦
    hw1 ⟨g, by rw [← hσ₂', Category.assoc, hg, hρ₂']⟩
  have l_ρ₂ρ : ¬∃ g, ρ₂' ≫ g = ρ₁' := fun ⟨g, hg⟩ ↦
    hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂']⟩
  have l_ρs : ¬∃ g, ρ₁' ≫ g = s' := fun ⟨g, hg⟩ ↦
    Z.σ_ne (s + 1) (by rw [← hs', ← hg, ← Category.assoc, hz2, zero_comp])
  have l_sρ : ¬∃ g, s' ≫ g = ρ₁' := fun ⟨g, hg⟩ ↦
    Z.ρ_ne (s + 3) (by rw [← hρ₁', ← hg, ← Category.assoc, hzs, zero_comp])
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hiσ₂' : ¬IsIso σ₂' := fun _ ↦ hp1 ⟨pathVal v₁ ≫ inv σ₂', by rw [← hσ₂', ← hρ₁']; simp⟩
  have hir : ¬IsIso r := fun _ ↦ hq2 ⟨pathVal v₁ ≫ inv r, by rw [← hr, ← hV]; simp⟩
  -- R5 a): `ρ₂'` and `s'` are comparable (else a `D̃₄` in `P/σ₁`)
  have hcmp : (∃ ξ, ρ₂' ≫ ξ = s') ∨ ∃ ξ, s' ≫ ξ = ρ₂' := by
    by_contra hno
    obtain ⟨h1, h2⟩ := not_or.1 hno
    exact B.not_f8s04 hmin hL hR (Z.σ (s + 2)) hσ.2.1 hσ.1 (pathVal v₂) ρ₁' ρ₂' s'
      (h0_a_y₀ := not_ftm_suffix_of_long hσ hiV₁ (by rw [hV]; exact hσ.1))
      (h0_a_y₁ := not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ₁']; exact Z.ρ_ne _))
      (h0_a_z₂ := not_ftm_suffix_of_long hσ hiσ₂' (by rw [hρ₂']; exact Z.ρ_ne _))
      (h0_a_yn1 := not_ftm_suffix_of_long hσ hir (by rw [hs']; exact Z.σ_ne _))
      (hi_V₂ := not_isIso_pathVal v₂ hv₂) (hi_ρ₁' := fun _ ↦ l_ρV ⟨inv ρ₁' ≫ pathVal v₂, by simp⟩)
      (hi_ρ₂' := fun _ ↦ l_ρ₂V ⟨inv ρ₂' ≫ pathVal v₂, by simp⟩)
      (hi_s := fun _ ↦ l_sV ⟨inv s' ≫ pathVal v₂, by simp⟩)
      (hl_V₂_ρ₁'_y₁ := l_Vρ) (hl_V₂_ρ₂'_z₂ := l_Vρ₂) (hl_V₂_s_yn1 := l_Vs)
      (hl_ρ₁'_V₂_y₀ := l_ρV) (hl_ρ₁'_ρ₂'_z₂ := l_ρρ₂) (hl_ρ₁'_s_yn1 := l_ρs)
      (hl_ρ₂'_V₂_y₀ := l_ρ₂V) (hl_ρ₂'_ρ₁'_y₁ := l_ρ₂ρ) (hl_ρ₂'_s_yn1 := h1)
      (hl_s_V₂_y₀ := l_sV) (hl_s_ρ₁'_y₁ := l_sρ) (hl_s_ρ₂'_z₂ := h2)
  have hσ' : IsLong (pathVal v₁ ≫ pathVal v₂) := by rw [hV]; exact hσ
  have hρ₁l' : ¬IsLong (pathVal v₁ ≫ ρ₁') := by rw [hρ₁']; exact hρ₁l
  have hρnl' : ¬IsLong (r ≫ pathVal v₂) := by rw [hr]; exact hρnl
  have hρ₁0 : pathVal v₁ ≫ ρ₁' ≠ 0 := by rw [hρ₁']; exact Z.ρ_ne _
  have hσ₂0 : σ₂' ≫ ρ₁' ≠ 0 := by rw [hσ₂']; exact Z.σ_ne _
  have hρn0 : r ≫ pathVal v₂ ≠ 0 := by rw [hr]; exact Z.ρ_ne _
  have cp1 : ¬∃ c, c ≫ (pathVal v₁ ≫ ρ₁') = σ₂' ≫ ρ₁' := by rw [hρ₁', hσ₂']; exact hp2
  have cp2 : ¬∃ c, c ≫ (σ₂' ≫ ρ₁') = pathVal v₁ ≫ ρ₁' := by rw [hρ₁', hσ₂']; exact hp1
  have cv1 : ¬∃ c, (pathVal v₁ ≫ ρ₁') ≫ c = pathVal v₁ ≫ pathVal v₂ := by
    rw [hρ₁', hV]; exact hv2
  have cv2 : ¬∃ c, (pathVal v₁ ≫ pathVal v₂) ≫ c = pathVal v₁ ≫ ρ₁' := by
    rw [hρ₁', hV]; exact hv1
  have cq1 : ¬∃ c, c ≫ (r ≫ pathVal v₂) = pathVal v₁ ≫ pathVal v₂ := by rw [hr, hV]; exact hq2
  have cq2 : ¬∃ c, c ≫ (pathVal v₁ ≫ pathVal v₂) = r ≫ pathVal v₂ := by rw [hr, hV]; exact hq1
  rcases hcmp with ⟨ξ, hξ⟩ | ⟨ξ, hξ⟩
  · -- the crown `(σ₂, ρ₁, σ₁, ρₙ, r ≫ ρ₂', ρ₂)`
    exact B.l8_star hmin hL hR hQ hcont (pathVal v₁) σ₂' r (pathVal v₂) ρ₁' ρ₂' v₁ v₂
      (β.toPath.comp w') rfl rfl hq hni hσ' hρ₁l' hρnl' (by rw [hρ₂']; exact hρ₂l) hz hz2 hzV
      hρ₁0 hσ₂0 hρn0
      (fun h ↦ Z.σ_ne (s + 1) (by rw [← hs', ← hξ, ← Category.assoc, h, zero_comp]))
      (by rw [hρ₂']; exact Z.ρ_ne _) cp1 cp2 cv1 cv2 cq1 cq2 l_ρ₂V l_Vρ₂ l_ρ₂ρ l_ρρ₂ hD810 hD810D
  · -- the crown `(σ₂, ρ₁, σ₁, ρₙ, σₙ, σ₂' ≫ s')`
    have hν0 : σ₂' ≫ s' ≠ 0 := fun h ↦
      Z.ρ_ne (s + 4) (by rw [← hρ₂', ← hξ, ← Category.assoc, h, zero_comp])
    have hνl : ¬IsLong (σ₂' ≫ s') := fun h ↦ hρ₂l (by
      rw [← hρ₂', ← hξ, ← Category.assoc]
      exact h.of_factorsThrough (by rw [Category.assoc, hξ, hρ₂']; exact Z.ρ_ne _)
        ⟨𝟙 _, ξ, by simp⟩)
    exact B.l8_star hmin hL hR hQ hcont (pathVal v₁) σ₂' r (pathVal v₂) ρ₁' s' v₁ v₂
      (β.toPath.comp w') rfl rfl hq hni hσ' hρ₁l' hρnl' hνl hz hz2 hzs hρ₁0 hσ₂0 hρn0
      (by rw [hs']; exact Z.σ_ne _) hν0 cp1 cp2 cv1 cv2 cq1 cq2 l_sV l_Vs l_sρ l_ρs hD810 hD810D

end MulBasis

end RayQuiver

end LargeIndecomposable
