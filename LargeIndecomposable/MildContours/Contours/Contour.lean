module

public import LargeIndecomposable.MildContours.Contours.Lemma11
public import LargeIndecomposable.Cleaving.Shapes.ShapeIn4
public import LargeIndecomposable.MildContours.Setup.EndCyclic

/-!
# Mild contours: data and first consequences

`MildContour x y`: a contour `v = v'·α`, `w = w'·β` from `x` to `y` (equal
nonzero values, not interlaced) with the generator `ρ = π(y)` of the
non-invertible endomorphisms of `y` and `ω ≫ ρ ≠ 0` (non-deep, transit side).
Basic facts, and [mild] Lemma 2.1, steps 1–2 (`MildContour.rho_sq`,
`MildContour.step2`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A contour `{v'·α, w'·β}` from `x` to `y` with `ρ = π(y)` and `ω ≫ ρ ≠ 0`. -/
structure MildContour (x y : P) where
  sv : P
  sw : P
  v' : Quiver.Path (RayVert.mk x) (RayVert.mk sv)
  α : (RayVert.mk sv : RayVert P) ⟶ RayVert.mk y
  w' : Quiver.Path (RayVert.mk x) (RayVert.mk sw)
  β : (RayVert.mk sw : RayVert P) ⟶ RayVert.mk y
  hval : pathVal (v'.cons α) = pathVal (w'.cons β)
  h0 : pathVal (v'.cons α) ≠ 0
  hni : ¬Interlaced (v'.cons α) (w'.cons β)
  ρ : y ⟶ y
  hρ : ∀ e : y ⟶ y, ¬IsIso e → ∃ n, 0 < n ∧ e = rpow ρ n
  hωρ : pathVal (v'.cons α) ≫ ρ ≠ 0

namespace MildContour

variable {x y : P} (C : MildContour x y)

/-- The common value. -/
abbrev ω : x ⟶ y := pathVal (C.v'.cons C.α)

/-- The value of `v'`. -/
abbrev γ : x ⟶ C.sv := pathVal C.v'

/-- The value of `w'`. -/
abbrev δ : x ⟶ C.sw := pathVal C.w'

/-- The killed morphism `ω ≫ ρ`. -/
abbrev τ : x ⟶ y := C.ω ≫ C.ρ

lemma ω_eq_v : C.ω = C.γ ≫ C.α.1 := rfl

lemma ω_eq_w : C.ω = C.δ ≫ C.β.1 := C.hval

lemma zero_not_isIso (z : P) : ¬IsIso (0 : z ⟶ z) := fun h ↦
  IsRayCategory.id_ne_zero z (by rw [← IsIso.hom_inv_id (0 : z ⟶ z), zero_comp])

lemma rpow_id (z : P) : ∀ n, rpow (𝟙 z) n = 𝟙 z
  | 0 => rfl
  | n + 1 => by rw [rpow_succ, rpow_id z n, Category.comp_id]

lemma ρ_not_isIso : ¬IsIso C.ρ := by
  intro hρ
  obtain ⟨n, -, hn⟩ := C.hρ 0 (zero_not_isIso y)
  obtain ⟨hxy, he⟩ := RayQuiver.eq_id_of_isIso C.ρ
  have hρ1 : C.ρ = 𝟙 y := by rw [he]; rfl
  rw [hρ1, rpow_id] at hn
  exact IsRayCategory.id_ne_zero y hn.symm

lemma τ_ne_zero : C.τ ≠ 0 := C.hωρ

lemma isIso_pathVal_of_length_zero {a b : RayVert P} (p : Quiver.Path a b) (h : p.length = 0) :
    IsIso (pathVal p) := by
  cases p with
  | nil => exact isIso_pathVal_nil
  | cons _ _ => simp at h

/-- The last arrows of a contour are apart. -/
lemma apart (hR : RightCancel P) : ArrowsApart C.α C.β :=
  ⟨not_last_of_contour hR C.α C.β C.v' C.w' C.hval C.h0 C.hni,
    not_last_of_contour hR C.β C.α C.w' C.v' C.hval.symm (by rw [← C.hval]; exact C.h0)
      (fun h ↦ C.hni (Relation.EqvGen.symm _ _ h))⟩

lemma ω_not_irreducible (hR : RightCancel P) : ¬IsIrreducible C.ω := by
  intro hirr
  have hv0 := length_eq_zero_of_irreducible_cons C.v' C.α hirr
  have hw0 := length_eq_zero_of_irreducible_cons C.w' C.β (by
    change IsIrreducible (pathVal (C.w'.cons C.β)); rw [← C.hval]; exact hirr)
  haveI := isIso_pathVal_of_length_zero C.v' hv0
  haveI := isIso_pathVal_of_length_zero C.w' hw0
  apply (C.apart hR).1
  refine ⟨inv C.γ ≫ C.δ, ?_⟩
  rw [Category.assoc, ← C.ω_eq_w, C.ω_eq_v, IsIso.inv_hom_id_assoc]

lemma v'_pos (hR : RightCancel P) : 0 < C.v'.length :=
  length_pos_of_not_irreducible C.v' C.α (C.ω_not_irreducible hR)

lemma w'_pos (hR : RightCancel P) : 0 < C.w'.length :=
  length_pos_of_not_irreducible C.w' C.β (by
    change ¬IsIrreducible (pathVal (C.w'.cons C.β)); rw [← C.hval]; exact C.ω_not_irreducible hR)

lemma γ_not_isIso (hR : RightCancel P) : ¬IsIso C.γ := not_isIso_pathVal _ (C.v'_pos hR)

lemma δ_not_isIso (hR : RightCancel P) : ¬IsIso C.δ := not_isIso_pathVal _ (C.w'_pos hR)

lemma ω_not_isIso : ¬IsIso C.ω := not_isIso_pathVal _ (Nat.succ_pos _)

variable [Fintype P] [DecidableEq P] [IsFiniteRayCategory P]

lemma τ_not_isIso : ¬IsIso C.τ := not_isIso_comp_of_right _ _ C.ρ_not_isIso

/-- Middle factors of `τ` with nontrivial left part do not factor through `τ`. -/
lemma ftm_ρ : ¬FactorsThroughMorphism C.τ C.ρ :=
  not_ftm_mid C.hωρ (q := 𝟙 _) C.ω_not_isIso (by rw [Category.comp_id])

lemma ftm_α (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ C.α.1 :=
  not_ftm_mid C.hωρ (C.γ_not_isIso hR) (by rw [← Category.assoc, ← C.ω_eq_v])

lemma ftm_αρ (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ (C.α.1 ≫ C.ρ) :=
  not_ftm_mid C.hωρ (q := 𝟙 _) (C.γ_not_isIso hR)
    (by rw [Category.comp_id, ← Category.assoc, ← C.ω_eq_v])

lemma ftm_β (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ C.β.1 :=
  not_ftm_mid C.hωρ (C.δ_not_isIso hR) (by rw [← Category.assoc, ← C.ω_eq_w])

lemma ftm_βρ (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ (C.β.1 ≫ C.ρ) :=
  not_ftm_mid C.hωρ (q := 𝟙 _) (C.δ_not_isIso hR)
    (by rw [Category.comp_id, ← Category.assoc, ← C.ω_eq_w])

variable {k : Type*} [Field k] [Infinite k]

/-- An irreducible arrow factoring through `ρ` is impossible when `ρ` does not
factor through it. -/
lemma not_arrow_factor_ρ {s : P} (e : (RayVert.mk s : RayVert P) ⟶ RayVert.mk y)
    (hn : ¬∃ ξ, ξ ≫ e.1 = C.ρ) : ¬∃ g, g ≫ C.ρ = e.1 := by
  rintro ⟨g, hg⟩
  have hiso : IsIso g := by
    rcases e.2.2.2 _ g C.ρ hg.symm with h | h
    · exact h
    · exact absurd h C.ρ_not_isIso
  exact hn ⟨inv g, by rw [← hg, IsIso.inv_hom_id_assoc]⟩

lemma rpow_not_isIso {z : P} (r : z ⟶ z) (hr : ¬IsIso r) : ∀ n, 0 < n → ¬IsIso (rpow r n)
  | n + 1, _ => by rw [rpow_succ]; exact not_isIso_comp_of_right _ _ hr

/-- Nonzero powers of a non-invertible endomorphism are distinct. -/
lemma rpow_le_of_eq {z : P} (r : z ⟶ z) (hr : ¬IsIso r) {m n : ℕ} (hm : rpow r m ≠ 0)
    (h : rpow r m = rpow r n) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  have e : rpow r m = rpow r m ≫ rpow r (n - m) := by
    rw [← rpow_add, show m + (n - m) = n by omega, h]
  refine hm (IsRayCategory.eq_zero_of_comp_end _ _ (fun h1 ↦ rpow_not_isIso r hr (n - m) (by omega) ?_) e.symm)
  rw [h1]; infer_instance

/-- **[mild] Lemma 2.1, step 1**: if `ρ` factors through neither last arrow,
then `ρ ≫ ρ = 0`. -/
theorem rho_sq (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ) :
    C.ρ ≫ C.ρ = 0 := by
  by_contra hρρ
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  have hρ2 : rpow C.ρ 2 = C.ρ ≫ C.ρ := by rw [rpow_succ, rpow_succ, rpow_zero, Category.id_comp]
  -- `ρ ≫ ρ` does not factor through `τ`
  have h0ρρ : ¬FactorsThroughMorphism C.τ (C.ρ ≫ C.ρ) := by
    rintro ⟨a', b', hab⟩
    obtain ⟨i, hi, hi'⟩ := C.hρ (a' ≫ C.ω) (not_isIso_comp_of_right _ _ C.ω_not_isIso)
    have hab' : C.ρ ≫ C.ρ = rpow C.ρ i ≫ C.ρ ≫ b' := by
      rw [hab, ← hi']; simp only [Category.assoc]
    by_cases hb : IsIso b'
    · obtain ⟨hyy, hb1⟩ := RayQuiver.eq_id_of_isIso b'
      have hb1' : b' = 𝟙 y := by rw [hb1]; rfl
      rw [hb1', Category.comp_id, ← rpow_succ, ← hρ2] at hab'
      have hle := rpow_le_of_eq C.ρ C.ρ_not_isIso (by rw [hρ2]; exact hρρ) hab'
      have hi1 : i = 1 := by omega
      subst hi1
      apply hn1
      refine ⟨a' ≫ C.γ, ?_⟩
      rw [Category.assoc, ← C.ω_eq_v, hi']
      change 𝟙 y ≫ C.ρ = C.ρ
      rw [Category.id_comp]
    · obtain ⟨j, hj, hj'⟩ := C.hρ b' hb
      rw [hj', ← Category.assoc, ← rpow_succ, ← rpow_add, ← hρ2] at hab'
      have hle := rpow_le_of_eq C.ρ C.ρ_not_isIso (by rw [hρ2]; exact hρρ) hab'
      omega
  exact hM.not_in3 C.τ C.τ_not_isIso C.τ_ne_zero C.α.1 C.β.1 C.ρ C.ρ C.ftm_ρ (C.ftm_α hR)
    (C.ftm_αρ hR) (C.ftm_β hR) (C.ftm_βρ hR) C.ftm_ρ h0ρρ C.α.2.2.1 C.β.2.2.1 C.ρ_not_isIso
    C.ρ_not_isIso hap.2 hn1 hap.1 hn2 (C.not_arrow_factor_ρ C.α hn1) (C.not_arrow_factor_ρ C.β hn2)

lemma αρ_ne_zero : C.α.1 ≫ C.ρ ≠ 0 := fun h ↦ C.τ_ne_zero (by
  change C.ω ≫ C.ρ = 0; rw [C.ω_eq_v, Category.assoc, h, comp_zero])

lemma βρ_ne_zero : C.β.1 ≫ C.ρ ≠ 0 := fun h ↦ C.τ_ne_zero (by
  change C.ω ≫ C.ρ = 0; rw [C.ω_eq_w, Category.assoc, h, comp_zero])

/-- `f ≫ ρ` does not factor onto an arrow `e` through a factor of `f`. -/
lemma not_comp_ρ_eq_arrow {s t : P} (f : (RayVert.mk s : RayVert P).out ⟶ y)
    (hf : ¬IsIso f) (e : (RayVert.mk t : RayVert P) ⟶ RayVert.mk y) :
    ¬∃ g, g ≫ f ≫ C.ρ = e.1 := by
  rintro ⟨g, hg⟩
  rcases e.2.2.2 _ (g ≫ f) C.ρ (by rw [← hg, Category.assoc]) with h | h
  · exact hf (ray_isIso_factors g f).2
  · exact C.ρ_not_isIso h

/-- **[mild] Lemma 2.1, step 2**: the four arms `α, β, α ≫ ρ, β ≫ ρ` into `y`
do not form a cleaving `D̃₄`, so one of four factorizations holds. -/
theorem step2 (hM : MildHyp k P) :
    (∃ t, t ≫ C.α.1 = C.α.1 ≫ C.ρ) ∨ (∃ t, t ≫ C.β.1 = C.β.1 ≫ C.ρ) ∨
      (∃ φ, φ ≫ C.β.1 = C.α.1 ≫ C.ρ) ∨ (∃ φ, φ ≫ C.α.1 = C.β.1 ≫ C.ρ) := by
  by_contra h
  push Not at h
  obtain ⟨hI, hI', hII, hII'⟩ := h
  have hR : RightCancel P := hM.right
  have hap := C.apart hR
  exact hM.not_in4 C.τ C.τ_not_isIso C.τ_ne_zero C.α.1 C.β.1 (C.α.1 ≫ C.ρ) (C.β.1 ≫ C.ρ)
    (C.ftm_α hR) (C.ftm_β hR) (C.ftm_αρ hR) (C.ftm_βρ hR) C.α.2.2.1 C.β.2.2.1
    (not_isIso_comp_of_right _ _ C.ρ_not_isIso) (not_isIso_comp_of_right _ _ C.ρ_not_isIso)
    hap.2 (fun ⟨g, hg⟩ ↦ hI g hg) (fun ⟨g, hg⟩ ↦ hII' g hg) hap.1 (fun ⟨g, hg⟩ ↦ hII g hg)
    (fun ⟨g, hg⟩ ↦ hI' g hg) (C.not_comp_ρ_eq_arrow _ C.α.2.2.1 C.α)
    (C.not_comp_ρ_eq_arrow _ C.α.2.2.1 C.β)
    (fun ⟨g, hg⟩ ↦ hap.2 ⟨g, hR _ _ C.ρ (by rw [Category.assoc, hg]) (by
      rw [Category.assoc, hg]; exact C.βρ_ne_zero)⟩)
    (C.not_comp_ρ_eq_arrow _ C.β.2.2.1 C.α) (C.not_comp_ρ_eq_arrow _ C.β.2.2.1 C.β)
    (fun ⟨g, hg⟩ ↦ hap.1 ⟨g, hR _ _ C.ρ (by rw [Category.assoc, hg]) (by
      rw [Category.assoc, hg]; exact C.αρ_ne_zero)⟩)

lemma not_isIso_of_endo_comp {z : P} (t : z ⟶ z) (e : (RayVert.mk z : RayVert P) ⟶ RayVert.mk y)
    (ht : t ≫ e.1 = e.1 ≫ C.ρ) : ¬IsIso t := by
  intro hti
  obtain ⟨hzz, he⟩ := RayQuiver.eq_id_of_isIso t
  have : t = 𝟙 z := by rw [he]; rfl
  rw [this, Category.id_comp] at ht
  exact e.2.1 (IsRayCategory.eq_zero_of_comp_end _ _ (fun h ↦ C.ρ_not_isIso (by rw [h]; infer_instance))
    ht.symm)

/-- **[mild] Lemma 2.1, Case I(a)**: `α ≫ ρ = τ' ≫ α` and `β ≫ ρ = ψ ≫ α` give the crown
`Ã(β, ψ, τ', α)` in `P/τ`. -/
theorem caseIa (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) {τ' : C.sv ⟶ C.sv}
    (hτ' : τ' ≫ C.α.1 = C.α.1 ≫ C.ρ) {ψ : C.sw ⟶ C.sv} (hψ : ψ ≫ C.α.1 = C.β.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hτi := C.not_isIso_of_endo_comp τ' C.α hτ'
  have h0τ' : ¬FactorsThroughMorphism C.τ τ' := not_ftm_mid C.hωρ (C.γ_not_isIso hR)
    (by rw [hτ', ← Category.assoc, ← C.ω_eq_v])
  have h0ψ : ¬FactorsThroughMorphism C.τ ψ := not_ftm_mid C.hωρ (C.δ_not_isIso hR)
    (by rw [hψ, ← Category.assoc, ← C.ω_eq_w])
  refine hM.not_crown2 C.τ C.τ_not_isIso C.τ_ne_zero ψ τ' C.α.1 C.β.1 h0ψ h0τ' (C.ftm_α hR)
    (C.ftm_β hR) ?_ ?_ hap.1 hap.2 ?_ ?_ ?_ ?_
  · -- `ψ = c ≫ τ'` gives `β = c ≫ α`
    rintro ⟨c, hc⟩
    have e : (c ≫ C.α.1) ≫ C.ρ = C.β.1 ≫ C.ρ := by
      rw [Category.assoc, ← hτ', ← Category.assoc, hc, hψ]
    exact hap.2 ⟨c, hR _ _ C.ρ e (by rw [e]; exact C.βρ_ne_zero)⟩
  · -- `τ' = c ≫ ψ` gives `α = c ≫ β`
    rintro ⟨c, hc⟩
    have e : (c ≫ C.β.1) ≫ C.ρ = C.α.1 ≫ C.ρ := by
      rw [Category.assoc, ← hψ, ← Category.assoc, hc, hτ']
    exact hap.1 ⟨c, hR _ _ C.ρ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · -- `α = τ' ≫ c`
    rintro ⟨c, hc⟩
    rcases C.α.2.2.2 _ τ' c hc.symm with h | h
    · exact hτi h
    · have hτ'' : τ' = C.α.1 ≫ inv c := by
        rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have e : C.α.1 ≫ inv c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, ← hτ'', hτ']
      exact hn1 ⟨inv c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · -- `τ' = α ≫ c` gives `ρ = c ≫ α`
    rintro ⟨c, hc⟩
    have e : C.α.1 ≫ c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, hc, hτ']
    exact hn1 ⟨c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · -- `ψ = β ≫ c` gives `ρ = c ≫ α`
    rintro ⟨c, hc⟩
    have e : C.β.1 ≫ c ≫ C.α.1 = C.β.1 ≫ C.ρ := by rw [← Category.assoc, hc, hψ]
    exact hn1 ⟨c, hL _ _ _ e (by rw [e]; exact C.βρ_ne_zero)⟩
  · -- `β = ψ ≫ c`
    rintro ⟨c, hc⟩
    rcases C.β.2.2.2 _ ψ c hc.symm with h | h
    · have hα : C.α.1 = (inv ψ ≫ C.β.1) ≫ C.ρ := by
        rw [Category.assoc, ← hψ, IsIso.inv_hom_id_assoc]
      rcases C.α.2.2.2 _ (inv ψ ≫ C.β.1) C.ρ hα with h' | h'
      · exact C.β.2.2.1 (ray_isIso_factors (inv ψ) C.β.1).2
      · exact C.ρ_not_isIso h'
    · have hψ' : ψ = C.β.1 ≫ inv c := by
        rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have e : C.β.1 ≫ inv c ≫ C.α.1 = C.β.1 ≫ C.ρ := by
        rw [← Category.assoc, ← hψ', hψ]
      exact hn1 ⟨inv c, hL _ _ _ e (by rw [e]; exact C.βρ_ne_zero)⟩

/-- A left factor `g` of a nonzero `f = g ≫ q` with `q` non-invertible does not factor
through `f`. -/
lemma not_ftm_left {a b d : P} {f : a ⟶ d} (hf0 : f ≠ 0) {g : a ⟶ b} {q : b ⟶ d}
    (hq : ¬IsIso q) (h : g ≫ q = f) : ¬FactorsThroughMorphism f g := by
  rintro ⟨u, v, rfl⟩
  have e : f = u ≫ f ≫ (v ≫ q) := by
    conv_lhs => rw [← h]
    simp only [Category.assoc]
  obtain ⟨-, hvq⟩ := IsRayCategory.eq_id_of_two_sided _ hf0 u (v ≫ q) e
  haveI : IsIso (v ≫ q) := by rw [hvq]; infer_instance
  exact hq (ray_isIso_factors v q).2

lemma ftm_γ (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ C.γ :=
  not_ftm_left C.hωρ (not_isIso_comp_of_left _ _ C.α.2.2.1)
    (by rw [← Category.assoc, ← C.ω_eq_v])

lemma ftm_δ (hR : RightCancel P) : ¬FactorsThroughMorphism C.τ C.δ :=
  not_ftm_left C.hωρ (not_isIso_comp_of_left _ _ C.β.2.2.1)
    (by rw [← Category.assoc, ← C.ω_eq_w])

/-- `γ` and `δ` do not factor through each other. -/
lemma γ_δ_apart (hR : RightCancel P) (hL : LeftCancel P) :
    (¬∃ c, C.δ ≫ c = C.γ) ∧ ¬∃ c, C.γ ≫ c = C.δ := by
  have hap := C.apart hR
  constructor
  · rintro ⟨c, hc⟩
    have e : C.δ ≫ c ≫ C.α.1 = C.δ ≫ C.β.1 := by
      rw [← Category.assoc, hc, ← C.ω_eq_v, C.ω_eq_w]
    exact hap.2 ⟨c, hL _ _ _ e (by rw [e, ← C.ω_eq_w]; exact C.h0)⟩
  · rintro ⟨c, hc⟩
    have e : C.γ ≫ c ≫ C.β.1 = C.γ ≫ C.α.1 := by
      rw [← Category.assoc, hc, ← C.ω_eq_w, C.ω_eq_v]
    exact hap.1 ⟨c, hL _ _ _ e (by rw [e, ← C.ω_eq_v]; exact C.h0)⟩

/-- **[mild] Lemma 2.1, Case I(b)**: `α ≫ ρ = τ' ≫ α` and `β ≫ ρ = ψ ≫ β` give the crown
`Ã(β, ψ, δ, γ, τ', α)` in `P/τ`, unless `ρ ≫ ρ ≠ 0` or (2) holds. -/
theorem caseIb (hM : MildHyp k P) (hn1 : ¬∃ ξ, ξ ≫ C.α.1 = C.ρ) (hn2 : ¬∃ ξ, ξ ≫ C.β.1 = C.ρ)
    (hn3γ : ¬∃ ξ, C.τ = (C.γ ≫ ξ) ≫ C.ω) (hn3δ : ¬∃ ξ, C.τ = (C.δ ≫ ξ) ≫ C.ω)
    (hρρ : C.ρ ≫ C.ρ = 0) {τ' : C.sv ⟶ C.sv} (hτ' : τ' ≫ C.α.1 = C.α.1 ≫ C.ρ)
    {ψ : C.sw ⟶ C.sw} (hψ : ψ ≫ C.β.1 = C.β.1 ≫ C.ρ) : False := by
  have hR : RightCancel P := hM.right
  have hL : LeftCancel P := hM.left
  have hap := C.apart hR
  have hγδ := C.γ_δ_apart hR hL
  have hτi := C.not_isIso_of_endo_comp τ' C.α hτ'
  have hψi := C.not_isIso_of_endo_comp ψ C.β hψ
  have h0τ' : ¬FactorsThroughMorphism C.τ τ' := not_ftm_mid C.hωρ (C.γ_not_isIso hR)
    (by rw [hτ', ← Category.assoc, ← C.ω_eq_v])
  have h0ψ : ¬FactorsThroughMorphism C.τ ψ := not_ftm_mid C.hωρ (C.δ_not_isIso hR)
    (by rw [hψ, ← Category.assoc, ← C.ω_eq_w])
  have hτv : C.τ = C.γ ≫ C.α.1 ≫ C.ρ := by
    change C.ω ≫ C.ρ = _; rw [C.ω_eq_v, Category.assoc]
  have hτw : C.τ = C.δ ≫ C.β.1 ≫ C.ρ := by
    change C.ω ≫ C.ρ = _; rw [C.ω_eq_w, Category.assoc]
  refine hM.not_crown3 C.τ C.τ_not_isIso C.τ_ne_zero ψ C.δ C.γ τ' C.α.1 C.β.1 h0ψ (C.ftm_δ hR)
    (C.ftm_γ hR) h0τ' (C.ftm_α hR) (C.ftm_β hR) ?_ ?_ ?_ ?_ hap.1 hap.2 hγδ.1 hγδ.2 ?_ ?_ ?_ ?_
  · -- `ψ = c ≫ δ`: (2) through `δ`
    rintro ⟨c, hc⟩
    exact hn3δ ⟨c, by rw [hτw, ← hψ, ← hc, C.ω_eq_w]; simp only [Category.assoc]⟩
  · -- `δ = c ≫ ψ`: `τ = 0`
    rintro ⟨c, hc⟩
    apply C.τ_ne_zero
    rw [hτw, ← hc, Category.assoc, ← Category.assoc ψ, hψ, Category.assoc, hρρ, comp_zero,
      comp_zero]
  · -- `γ = c ≫ τ'`: `τ = 0`
    rintro ⟨c, hc⟩
    apply C.τ_ne_zero
    rw [hτv, ← hc, Category.assoc, ← Category.assoc τ', hτ', Category.assoc, hρρ, comp_zero,
      comp_zero]
  · -- `τ' = c ≫ γ`: (2) through `γ`
    rintro ⟨c, hc⟩
    exact hn3γ ⟨c, by rw [hτv, ← hτ', ← hc, C.ω_eq_v]; simp only [Category.assoc]⟩
  · -- `α = τ' ≫ c`
    rintro ⟨c, hc⟩
    rcases C.α.2.2.2 _ τ' c hc.symm with h | h
    · exact hτi h
    · have hτ'' : τ' = C.α.1 ≫ inv c := by
        rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have e : C.α.1 ≫ inv c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, ← hτ'', hτ']
      exact hn1 ⟨inv c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · -- `τ' = α ≫ c`
    rintro ⟨c, hc⟩
    have e : C.α.1 ≫ c ≫ C.α.1 = C.α.1 ≫ C.ρ := by rw [← Category.assoc, hc, hτ']
    exact hn1 ⟨c, hL _ _ _ e (by rw [e]; exact C.αρ_ne_zero)⟩
  · -- `ψ = β ≫ c`: `ρ = c ≫ β`
    rintro ⟨c, hc⟩
    have e : C.β.1 ≫ c ≫ C.β.1 = C.β.1 ≫ C.ρ := by rw [← Category.assoc, hc, hψ]
    exact hn2 ⟨c, hL _ _ _ e (by rw [e]; exact C.βρ_ne_zero)⟩
  · -- `β = ψ ≫ c`
    rintro ⟨c, hc⟩
    rcases C.β.2.2.2 _ ψ c hc.symm with h | h
    · exact hψi h
    · have hψ' : ψ = C.β.1 ≫ inv c := by
        rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have e : C.β.1 ≫ inv c ≫ C.β.1 = C.β.1 ≫ C.ρ := by rw [← Category.assoc, ← hψ', hψ]
      exact hn2 ⟨inv c, hL _ _ _ e (by rw [e]; exact C.βρ_ne_zero)⟩

end MildContour

end RayCat

end LargeIndecomposable
