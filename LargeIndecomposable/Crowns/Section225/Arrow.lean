module

public import LargeIndecomposable.Crowns.Section225.NoThirdLong
public import LargeIndecomposable.Cleaving.Shapes.ShapeF95A
public import LargeIndecomposable.Cleaving.Shapes.ShapeF95B
public import LargeIndecomposable.Cleaving.Shapes.ShapeF95C

/-!
# BO13a §2.2.5: the two parts of a split contour are arrows

For a long `σ` with a contour `(v₁ v₂, w)`, `ρ = V₁ ≫ ρ'` its valley neighbour and
`ρn = r ≫ V₂` its peak neighbour:

* `MulBasis.arrow_v1`: `v₁ = B α` with `B` nonempty gives the `Ẽ₈` tree `F95A` in `P/σ`
  (with the next four entries `σ₂, ρ₂, σ₃, ρ₃` of the chain);
* `MulBasis.arrow_v2`: `v₂ = β C'` with `C'` nonempty gives the `Ẽ₈` tree `F95B` in
  `P/σ` (with the previous four entries).
* `MulBasis.arrow_v2f`: the same with the next four entries (tree `F95C`), when `v₁` is the
  longest prefix through which `ρ` factors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **`v₁` is an arrow** (BO13a §2.2.5, the `Ẽ₈` tree in `P/σ₁`). -/
theorem arrow_v1
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {X Y₀ Y₁ X₂ Y₂ X₃ Y₃ : P} (σ : X ⟶ Y₀) (hσ : IsLong σ) (ρ : X ⟶ Y₁) (hρ0 : ρ ≠ 0)
    (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (σ₂ : X₂ ⟶ Y₁) (ρ₂ : X₂ ⟶ Y₂) (σ₃ : X₃ ⟶ Y₂) (ρ₃ : X₃ ⟶ Y₃)
    (hp1 : ¬∃ c, c ≫ σ₂ = ρ) (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (hs1 : ¬∃ c, c ≫ σ₃ = ρ₂) (hs2 : ¬∃ c, c ≫ ρ₂ = σ₃)
    (ht1 : ¬∃ c, σ₃ ≫ c = ρ₃) (ht2 : ¬∃ c, ρ₃ ≫ c = σ₃)
    (h0σ₂ : ¬FactorsThroughMorphism σ σ₂) (h0ρ₂ : ¬FactorsThroughMorphism σ ρ₂)
    (h0σ₃ : ¬FactorsThroughMorphism σ σ₃) (h0ρ₃ : ¬FactorsThroughMorphism σ ρ₃)
    {m a b : RayVert P} (Bp : Quiver.Path (RayVert.mk X) m) (α : m ⟶ a)
    (v₂ : Quiver.Path a (RayVert.mk Y₀)) (w₁ : Quiver.Path (RayVert.mk X) b)
    (w₂ : Quiver.Path b (RayVert.mk Y₀)) (hBp : 0 < Bp.length) (hv₂ : 0 < v₂.length)
    (hw₁ : 0 < w₁.length) (hw₂ : 0 < w₂.length)
    (hv : pathVal ((Bp.cons α).comp v₂) = σ) (hw : pathVal (w₁.comp w₂) = σ)
    (hni : ¬Interlaced ((Bp.cons α).comp v₂) (w₁.comp w₂))
    (ρ' : a.out ⟶ Y₁) (hρ' : pathVal (Bp.cons α) ≫ ρ' = ρ)
    (L8a : ¬∃ c, c ≫ ρ' = σ₂) : False := by
  have hσ0 := hσ.1
  have hval : pathVal ((Bp.cons α).comp v₂) = pathVal (w₁.comp w₂) := by rw [hv, hw]
  have h0 : pathVal ((Bp.cons α).comp v₂) ≠ 0 := by rw [hv]; exact hσ0
  have hV : pathVal (Bp.cons α) ≫ pathVal v₂ = σ := by rw [← pathVal_comp]; exact hv
  have hW : pathVal w₁ ≫ pathVal w₂ = σ := by rw [← pathVal_comp]; exact hw
  have hiB := not_isIso_pathVal Bp hBp
  have hiV₁ := not_isIso_pathVal (Bp.cons α) (by simp)
  have hiW₁ := not_isIso_pathVal w₁ hw₁
  have hBα : pathVal (Bp.cons α) = pathVal Bp ≫ α.1 := rfl
  have hl1 : ¬∃ g, ρ' ≫ g = pathVal v₂ := fun ⟨g, hg⟩ ↦
    hv2 ⟨g, by rw [← hρ', Category.assoc, hg, hV]⟩
  have hiρ' : ¬IsIso ρ' := fun _ ↦ hl1 ⟨inv ρ' ≫ pathVal v₂, by simp⟩
  have hc1 := (contour_cross hL hR (Bp.cons α) v₂ w₁ w₂ hval h0 hni (by simp) hw₂).1
  have hc2 := (contour_cross hL hR w₁ w₂ (Bp.cons α) v₂ hval.symm (by rw [← hval]; exact h0)
    (fun h ↦ hni h.symm) hw₁ hv₂).1
  have e3 : (Bp.cons α).comp v₂ = Bp.comp (α.toPath.comp v₂) := by
    rw [← Quiver.Path.comp_assoc]; rfl
  have hc3 := (contour_cross hL hR Bp (α.toPath.comp v₂) w₁ w₂ (by rw [← e3]; exact hval)
    (by rw [← e3]; exact h0) (by rw [← e3]; exact hni) hBp hw₂).1
  rw [pathVal_comp, pathVal_toPath] at hc3
  have hBαV : pathVal Bp ≫ α.1 ≫ pathVal v₂ ≠ 0 := by
    rw [← Category.assoc, ← hBα, hV]; exact hσ0
  have hBαρ : pathVal Bp ≫ α.1 ≫ ρ' ≠ 0 := by
    rw [← Category.assoc, ← hBα, hρ']; exact hρ0
  exact B.not_f95a hmin hL hR σ hσ.2.1 hσ0 α.1 (pathVal v₂) (pathVal w₂) ρ' σ₂ ρ₂ σ₃ ρ₃
    (h0_a_y₀ := not_ftm_suffix_of_long hσ hiV₁ (by rw [hV]; exact hσ0))
    (h0_a_y₁ := not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ']; exact hρ0))
    (h0_mid_a := not_ftm_suffix_of_long hσ hiB
      (fun h ↦ hσ0 (by rw [← hV, hBα, h, zero_comp])))
    (h0_mid_y₀ := not_ftm_suffix_of_long hσ hiB hBαV)
    (h0_mid_y₁ := not_ftm_suffix_of_long hσ hiB hBαρ)
    (h0_wm_y₀ := not_ftm_suffix_of_long hσ hiW₁ (by rw [hW]; exact hσ0))
    (h0_x₂_y₁ := h0σ₂) (h0_x₂_y₂ := h0ρ₂) (h0_x₃_y₂ := h0σ₃) (h0_x₃_y₃ := h0ρ₃)
    (hi_α := α.2.2.1) (hi_V₂ := not_isIso_pathVal v₂ hv₂) (hi_W₂ := not_isIso_pathVal w₂ hw₂)
    (hi_ρ₁' := hiρ') (hi_σ₂ := fun _ ↦ hp1 ⟨ρ ≫ inv σ₂, by simp⟩)
    (hi_ρ₂ := fun _ ↦ hw2 ⟨inv ρ₂ ≫ σ₂, by simp⟩)
    (hi_σ₃ := fun _ ↦ hs1 ⟨ρ₂ ≫ inv σ₃, by simp⟩)
    (hi_ρ₃ := fun _ ↦ ht2 ⟨inv ρ₃ ≫ σ₃, by simp⟩)
    (hl_V₂_ρ₁'_y₁ := fun ⟨g, hg⟩ ↦ hv1 ⟨g, by rw [← hV, Category.assoc, hg, hρ']⟩)
    (hl_ρ₁'_V₂_y₀ := hl1) (hl_σ₂_ρ₂_y₂ := hw1) (hl_ρ₂_σ₂_y₁ := hw2)
    (hl_σ₃_ρ₃_y₃ := ht1) (hl_ρ₃_σ₃_y₂ := ht2)
    (hr_V₂_W₂_wm := hc2) (hr_W₂_V₂_a := hc1) (hr_W₂_V₂_mid := hc3) (hr_ρ₁'_σ₂_x₂ := L8a)
    (hr_σ₂_ρ₁'_a := fun ⟨g, hg⟩ ↦ hp1 ⟨pathVal (Bp.cons α) ≫ g, by
      rw [Category.assoc, hg, hρ']⟩)
    (hr_σ₂_ρ₁'_mid := fun ⟨g, hg⟩ ↦ hp1 ⟨pathVal Bp ≫ g, by
      rw [Category.assoc, hg, ← Category.assoc, ← hBα, hρ']⟩)
    (hr_ρ₂_σ₃_x₃ := hs2) (hr_σ₃_ρ₂_x₂ := hs1)

include B in
/-- **`v₂` is an arrow** (the mirror `Ẽ₈` tree in `P/σ₁`). -/
theorem arrow_v2
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {X Y₀ Xn Y₁ X₂ Y₂ X₃ : P} (σ : X ⟶ Y₀) (hσ : IsLong σ) (ρn : Xn ⟶ Y₀) (hρn0 : ρn ≠ 0)
    (hq1 : ¬∃ c, c ≫ σ = ρn) (hq2 : ¬∃ c, c ≫ ρn = σ)
    (σn : Xn ⟶ Y₁) (ρn₁ : X₂ ⟶ Y₁) (σn₁ : X₂ ⟶ Y₂) (ρn₂ : X₃ ⟶ Y₂)
    (hu1 : ¬∃ c, σn ≫ c = ρn) (hp1 : ¬∃ c, c ≫ σn = ρn₁) (hp2 : ¬∃ c, c ≫ ρn₁ = σn)
    (hv1 : ¬∃ c, ρn₁ ≫ c = σn₁) (hv2 : ¬∃ c, σn₁ ≫ c = ρn₁)
    (hs1 : ¬∃ c, c ≫ σn₁ = ρn₂) (hs2 : ¬∃ c, c ≫ ρn₂ = σn₁)
    (h0σn : ¬FactorsThroughMorphism σ σn) (h0ρn₁ : ¬FactorsThroughMorphism σ ρn₁)
    (h0σn₁ : ¬FactorsThroughMorphism σ σn₁) (h0ρn₂ : ¬FactorsThroughMorphism σ ρn₂)
    {a m b : RayVert P} (v₁ : Quiver.Path (RayVert.mk X) a) (β : a ⟶ m)
    (Cp : Quiver.Path m (RayVert.mk Y₀)) (w₁ : Quiver.Path (RayVert.mk X) b)
    (w₂ : Quiver.Path b (RayVert.mk Y₀)) (hv₁ : 0 < v₁.length) (hCp : 0 < Cp.length)
    (hw₁ : 0 < w₁.length) (hw₂ : 0 < w₂.length)
    (hv : pathVal (v₁.comp (β.toPath.comp Cp)) = σ) (hw : pathVal (w₁.comp w₂) = σ)
    (hni : ¬Interlaced (v₁.comp (β.toPath.comp Cp)) (w₁.comp w₂))
    (r : Xn ⟶ a.out) (hr : r ≫ pathVal (β.toPath.comp Cp) = ρn)
    (L8b : ¬∃ c, r ≫ c = σn) : False := by
  have hσ0 := hσ.1
  have hval : pathVal (v₁.comp (β.toPath.comp Cp)) = pathVal (w₁.comp w₂) := by rw [hv, hw]
  have h0 : pathVal (v₁.comp (β.toPath.comp Cp)) ≠ 0 := by rw [hv]; exact hσ0
  have hβC : pathVal (β.toPath.comp Cp) = β.1 ≫ pathVal Cp := by
    rw [pathVal_comp, pathVal_toPath]
  have hV : pathVal v₁ ≫ β.1 ≫ pathVal Cp = σ := by rw [← hβC, ← pathVal_comp]; exact hv
  have hW : pathVal w₁ ≫ pathVal w₂ = σ := by rw [← pathVal_comp]; exact hw
  have hiC := not_isIso_pathVal Cp hCp
  have hiV₂ := not_isIso_pathVal (β.toPath.comp Cp) (by simp)
  have hrv : ¬∃ g, g ≫ r = pathVal v₁ := fun ⟨g, hg⟩ ↦
    hq2 ⟨g, by rw [← hr, hβC, ← Category.assoc, hg, hV]⟩
  have hp1' := prefix_cross hL hR _ _ hval h0 hni v₁ (β.toPath.comp Cp) w₁ w₂ rfl rfl hv₁ hw₂
  have hp2' := prefix_cross hL hR _ _ hval.symm (by rw [← hval]; exact h0)
    (fun h ↦ hni h.symm) w₁ w₂ v₁ (β.toPath.comp Cp) rfl rfl hw₁ (by simp)
  have e3 : v₁.comp (β.toPath.comp Cp) = (v₁.comp β.toPath).comp Cp := by
    rw [Quiver.Path.comp_assoc]
  have hp3' := prefix_cross hL hR _ _ hval.symm (by rw [← hval]; exact h0)
    (fun h ↦ hni h.symm) w₁ w₂ (v₁.comp β.toPath) Cp rfl e3.symm hw₁ hCp
  rw [pathVal_comp, pathVal_toPath] at hp3'
  exact B.not_f95b hmin hL hR σ hσ.2.1 hσ0 β.1 (pathVal v₁) (pathVal w₁) r σn ρn₁ σn₁ ρn₂
    (h0_a_m := not_ftm_prefix_of_long hσ hiC (fun h ↦ hσ0 (by rw [← hV, h, comp_zero])))
    (h0_x_a := not_ftm_prefix_of_long hσ hiV₂ (by rw [hβC, hV]; exact hσ0))
    (h0_x_m := not_ftm_prefix_of_long hσ hiC (by rw [Category.assoc, hV]; exact hσ0))
    (h0_x_wm := not_ftm_prefix_of_long hσ (not_isIso_pathVal w₂ hw₂) (by rw [hW]; exact hσ0))
    (h0_xn_a := not_ftm_prefix_of_long hσ hiV₂ (by rw [hr]; exact hρn0))
    (h0_xn_m := not_ftm_prefix_of_long hσ hiC (by rw [Category.assoc, ← hβC, hr]; exact hρn0))
    (h0_xn_y₁ := h0σn) (h0_x₂_y₁ := h0ρn₁) (h0_x₂_y₂ := h0σn₁) (h0_x₃_y₂ := h0ρn₂)
    (hi_β := β.2.2.1) (hi_V₁ := not_isIso_pathVal v₁ hv₁) (hi_W₁ := not_isIso_pathVal w₁ hw₁)
    (hi_r := fun _ ↦ hrv ⟨pathVal v₁ ≫ inv r, by simp⟩)
    (hi_σn := fun _ ↦ hp1 ⟨ρn₁ ≫ inv σn, by simp⟩)
    (hi_ρn₁ := fun _ ↦ hp2 ⟨σn ≫ inv ρn₁, by simp⟩)
    (hi_σn₁ := fun _ ↦ hv2 ⟨inv σn₁ ≫ ρn₁, by simp⟩)
    (hi_ρn₂ := fun _ ↦ hs2 ⟨σn₁ ≫ inv ρn₂, by simp⟩)
    (hl_V₁_W₁_wm := hp1') (hl_W₁_V₁_a := hp2') (hl_W₁_V₁_m := hp3') (hl_r_σn_y₁ := L8b)
    (hl_σn_r_a := fun ⟨g, hg⟩ ↦ hu1 ⟨g ≫ pathVal (β.toPath.comp Cp), by
      rw [← Category.assoc, hg, hr]⟩)
    (hl_σn_r_m := fun ⟨g, hg⟩ ↦ hu1 ⟨g ≫ pathVal Cp, by
      rw [← Category.assoc, hg, Category.assoc, ← hβC, hr]⟩)
    (hl_ρn₁_σn₁_y₂ := hv1) (hl_σn₁_ρn₁_y₁ := hv2)
    (hr_V₁_r_xn := fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hV, ← Category.assoc, hg, ← hβC, hr]⟩)
    (hr_r_V₁_x := hrv) (hr_σn_ρn₁_x₂ := hp1) (hr_ρn₁_σn_xn := hp2)
    (hr_σn₁_ρn₂_x₃ := hs1) (hr_ρn₂_σn₁_x₂ := hs2)

include B in
/-- **`v₂` is an arrow, valley side** (the `Ẽ₈` tree `F95C` in `P/σ₁`; uses that `v₁` is the
longest prefix through which `ρ₁` factors). -/
theorem arrow_v2f
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {X Y₀ Y₁ X₂ Y₂ X₃ Y₃ : P} (σ : X ⟶ Y₀) (hσ : IsLong σ) (ρ : X ⟶ Y₁) (hρ0 : ρ ≠ 0)
    (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (σ₂ : X₂ ⟶ Y₁) (ρ₂ : X₂ ⟶ Y₂) (σ₃ : X₃ ⟶ Y₂) (ρ₃ : X₃ ⟶ Y₃)
    (hp1 : ¬∃ c, c ≫ σ₂ = ρ) (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (hs1 : ¬∃ c, c ≫ σ₃ = ρ₂) (hs2 : ¬∃ c, c ≫ ρ₂ = σ₃)
    (ht1 : ¬∃ c, σ₃ ≫ c = ρ₃) (ht2 : ¬∃ c, ρ₃ ≫ c = σ₃)
    (h0σ₂ : ¬FactorsThroughMorphism σ σ₂) (h0ρ₂ : ¬FactorsThroughMorphism σ ρ₂)
    (h0σ₃ : ¬FactorsThroughMorphism σ σ₃) (h0ρ₃ : ¬FactorsThroughMorphism σ ρ₃)
    {a m b : RayVert P} (v₁ : Quiver.Path (RayVert.mk X) a) (β : a ⟶ m)
    (Cp : Quiver.Path m (RayVert.mk Y₀)) (w₁ : Quiver.Path (RayVert.mk X) b)
    (w₂ : Quiver.Path b (RayVert.mk Y₀)) (hv₁ : 0 < v₁.length) (hCp : 0 < Cp.length)
    (hw₁ : 0 < w₁.length) (hw₂ : 0 < w₂.length)
    (hv : pathVal (v₁.comp (β.toPath.comp Cp)) = σ) (hw : pathVal (w₁.comp w₂) = σ)
    (hni : ¬Interlaced (v₁.comp (β.toPath.comp Cp)) (w₁.comp w₂))
    (ρ' : a.out ⟶ Y₁) (hρ' : pathVal v₁ ≫ ρ' = ρ)
    (hmax : ¬∃ g, (pathVal v₁ ≫ β.1) ≫ g = ρ)
    (L8a : ¬∃ c, c ≫ ρ' = σ₂) : False := by
  have hσ0 := hσ.1
  have hval : pathVal (v₁.comp (β.toPath.comp Cp)) = pathVal (w₁.comp w₂) := by rw [hv, hw]
  have h0 : pathVal (v₁.comp (β.toPath.comp Cp)) ≠ 0 := by rw [hv]; exact hσ0
  have hβC : pathVal (β.toPath.comp Cp) = β.1 ≫ pathVal Cp := by
    rw [pathVal_comp, pathVal_toPath]
  have hV : pathVal v₁ ≫ β.1 ≫ pathVal Cp = σ := by rw [← hβC, ← pathVal_comp]; exact hv
  have hiC := not_isIso_pathVal Cp hCp
  have hiV₁ := not_isIso_pathVal v₁ hv₁
  have hp1' := prefix_cross hL hR _ _ hval h0 hni v₁ (β.toPath.comp Cp) w₁ w₂ rfl rfl hv₁ hw₂
  have hp2' := prefix_cross hL hR _ _ hval.symm (by rw [← hval]; exact h0)
    (fun h ↦ hni h.symm) w₁ w₂ v₁ (β.toPath.comp Cp) rfl rfl hw₁ (by simp)
  have e3 : v₁.comp (β.toPath.comp Cp) = (v₁.comp β.toPath).comp Cp := by
    rw [Quiver.Path.comp_assoc]
  have hp3' := prefix_cross hL hR _ _ hval.symm (by rw [← hval]; exact h0)
    (fun h ↦ hni h.symm) w₁ w₂ (v₁.comp β.toPath) Cp rfl e3.symm hw₁ hCp
  rw [pathVal_comp, pathVal_toPath] at hp3'
  -- `ρ` does not factor through `w₁` (Lemma 4 b))
  have hwρ : ¬∃ g, pathVal w₁ ≫ g = ρ := by
    rintro ⟨g, hg⟩
    obtain ⟨c₁, α, v₁', rfl⟩ := exists_first_arrow v₁ hiV₁
    obtain ⟨c₂, α', w₁', rfl⟩ := exists_first_arrow w₁ (not_isIso_pathVal _ hw₁)
    have ev : (α.toPath.comp v₁').comp (β.toPath.comp Cp) =
        α.toPath.comp (v₁'.comp (β.toPath.comp Cp)) := Quiver.Path.comp_assoc _ _ _
    have ew : (α'.toPath.comp w₁').comp w₂ = α'.toPath.comp (w₁'.comp w₂) :=
      Quiver.Path.comp_assoc _ _ _
    refine B.not_factors_both hmin hL hR α α' (v₁'.comp (β.toPath.comp Cp)) (w₁'.comp w₂)
      (by rw [← ev, ← ew]; exact hval) (by rw [← ev]; exact h0) (by rw [← ev, ← ew]; exact hni)
      ⟨Y₁, ρ⟩ hρ0 (fun ⟨c', hc'⟩ ↦ hv1 ⟨c', by rw [← hv, ev]; exact hc'⟩)
      (fun ⟨c', hc'⟩ ↦ hv2 ⟨c', by rw [← hv, ev]; exact hc'⟩) ⟨pathVal v₁' ≫ ρ', ?_⟩
      ⟨pathVal w₁' ≫ g, ?_⟩
    · change α.1 ≫ pathVal v₁' ≫ ρ' = ρ
      rw [← hρ', pathVal_comp, pathVal_toPath, Category.assoc]
    · change α'.1 ≫ pathVal w₁' ≫ g = ρ
      rw [← hg, pathVal_comp, pathVal_toPath, Category.assoc]
  have hl1 : ¬∃ g, ρ' ≫ g = β.1 := fun ⟨g, hg⟩ ↦
    hv2 ⟨g ≫ pathVal Cp, by rw [← hρ', Category.assoc, ← Category.assoc ρ', hg, hV]⟩
  have hiρ' : ¬IsIso ρ' := fun _ ↦ hl1 ⟨inv ρ' ≫ β.1, by simp⟩
  have hVβ0 : pathVal v₁ ≫ β.1 ≠ 0 := fun h ↦ hσ0 (by rw [← hV, ← Category.assoc, h, zero_comp])
  exact B.not_f95c hmin hL hR σ hσ.2.1 hσ0 β.1 (pathVal v₁) (pathVal w₁) ρ' σ₂ ρ₂ σ₃ ρ₃
    (h0_a_m := not_ftm_prefix_of_long hσ hiC (fun h ↦ hσ0 (by rw [← hV, h, comp_zero])))
    (h0_a_y₁ := not_ftm_suffix_of_long hσ hiV₁ (by rw [hρ']; exact hρ0))
    (h0_x_a := not_ftm_prefix_of_long hσ (not_isIso_pathVal (β.toPath.comp Cp) (by simp))
      (by rw [hβC, hV]; exact hσ0))
    (h0_x_m := not_ftm_prefix_of_long hσ hiC (by rw [Category.assoc, hV]; exact hσ0))
    (h0_x_y₁ := by
      rw [hρ']
      intro h
      obtain ⟨hx, hy, he⟩ := hσ.2.2.2 ρ hρ0 h
      exact hv1 ⟨eqToHom hy.symm, by rw [he]; simp⟩)
    (h0_x_wm := not_ftm_prefix_of_long hσ (not_isIso_pathVal w₂ hw₂)
      (by rw [← pathVal_comp, hw]; exact hσ0))
    (h0_x₂_y₁ := h0σ₂) (h0_x₂_y₂ := h0ρ₂) (h0_x₃_y₂ := h0σ₃) (h0_x₃_y₃ := h0ρ₃)
    (hi_β := β.2.2.1) (hi_V₁ := hiV₁) (hi_W₁ := not_isIso_pathVal w₁ hw₁) (hi_ρ₁' := hiρ')
    (hi_σ₂ := fun _ ↦ hp1 ⟨ρ ≫ inv σ₂, by simp⟩)
    (hi_ρ₂ := fun _ ↦ hw2 ⟨inv ρ₂ ≫ σ₂, by simp⟩)
    (hi_σ₃ := fun _ ↦ hs1 ⟨ρ₂ ≫ inv σ₃, by simp⟩)
    (hi_ρ₃ := fun _ ↦ ht2 ⟨inv ρ₃ ≫ σ₃, by simp⟩)
    (hl_β_ρ₁'_y₁ := fun ⟨g, hg⟩ ↦ hmax ⟨g, by rw [Category.assoc, hg, hρ']⟩)
    (hl_ρ₁'_β_m := hl1) (hl_V₁_W₁_wm := hp1') (hl_W₁_V₁_a := hp2') (hl_W₁_V₁_m := hp3')
    (hl_W₁_V₁_y₁ := by rw [hρ']; exact hwρ)
    (hl_σ₂_ρ₂_y₂ := hw1) (hl_ρ₂_σ₂_y₁ := hw2) (hl_σ₃_ρ₃_y₃ := ht1) (hl_ρ₃_σ₃_y₂ := ht2)
    (hr_ρ₁'_σ₂_x₂ := L8a)
    (hr_σ₂_ρ₁'_a := fun ⟨g, hg⟩ ↦ hp1 ⟨pathVal v₁ ≫ g, by rw [Category.assoc, hg, hρ']⟩)
    (hr_σ₂_ρ₁'_x := fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [hg, hρ']⟩)
    (hr_ρ₂_σ₃_x₃ := hs2) (hr_σ₃_ρ₂_x₂ := hs1)

end MulBasis

end RayQuiver

end LargeIndecomposable
