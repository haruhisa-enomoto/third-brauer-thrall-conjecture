module

public import LargeIndecomposable.MildContours.DumbBells.Morphisms
public import LargeIndecomposable.Cleaving.Families.FamMI42B
public import LargeIndecomposable.Cleaving.Families.FamMI42C
public import LargeIndecomposable.Cleaving.Families.FamMI42A

/-!
# Dumb-bells: the remaining [mild] MIDB facts (figure 4.2)

* `midb_d2`: if `μ t ≠ 0` (so `α t = 0`), only `t` ends in `z` (figure 4.2, second diagram).
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

namespace DBN

variable {x y : P} (N : DBN x y)

/-- A nonzero morphism from `x` to another object is `χⁿ μ g'`. -/
lemma fact_x_μ (hMo : MildHyp k Pᵒᵖ) :
    ∀ n : ℕ, ∀ {w : P} (g : x ⟶ w), w ≠ x → g ≠ 0 → depth g ≤ n →
      ∃ (m : ℕ) (g' : y ⟶ w), g = rpow N.χ m ≫ N.μ ≫ g' := by
  intro n
  induction n with
  | zero =>
    intro w g hw hg hd
    have hi : ¬IsIso g := fun h ↦ hw (eq_of_isIso h).symm
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg hi
    have := depth_lt_comp_left e r hg he.2.1
    omega
  | succ n ih =>
    intro w g hw hg hd
    have hi : ¬IsIso g := fun h ↦ hw (eq_of_isIso h).symm
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg hi
    rcases N.out_x hMo e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact ⟨0, u ≫ r, by simp⟩
    · have hd' := depth_lt_comp_left N.χ (u ≫ r) (by simpa using hg) N.hχ.2.1
      obtain ⟨m, g', hg'⟩ := ih (u ≫ r) hw (fun h ↦ hg (by rw [Category.assoc, h, comp_zero]))
        (by simp only [Category.assoc] at hd hd'; omega)
      exact ⟨m + 1, g', by rw [Category.assoc, hg', rpow_succ']; simp⟩

/-- The target of an extra arrow `t` with `μ t ≠ 0`, `α t = 0` is neither `x` nor `y`. -/
lemma z_ne {z : P} (t : y ⟶ z) (ht : IsIrreducible t) (hαt : N.α ≫ t = 0) :
    z ≠ x ∧ z ≠ y := by
  refine ⟨fun h ↦ by subst h; exact ht.1 (N.hyx t), fun h ↦ ?_⟩
  subst h
  obtain ⟨n, hn, hn'⟩ := N.hρ t ht.2.1
  rcases n with _ | _ | m
  · omega
  · apply N.hτ
    have e : t = N.α := by rw [hn']; simp [rpow_succ]
    rw [e] at hαt; rw [hαt, comp_zero]
  · rcases ht.2.2 _ (rpow N.α (m + 1)) N.α (by rw [hn', rpow_succ]) with h | h
    · exact MildContour.rpow_not_isIso N.α N.hα.2.1 (m + 1) (by omega) h
    · exact N.hα.2.1 h

/-- **[mild] MIDB d), second part**: if `μ t ≠ 0` and `α t = 0`, only `t` ends in `z`. -/
theorem midb_d2 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {z : P} (t : y ⟶ z)
    (ht : IsIrreducible t) (hta : ¬∃ g, N.α ≫ g = t) (hμt : N.μ ≫ t ≠ 0) (hαt : N.α ≫ t = 0)
    {w : P} (ζ : w ⟶ z) (hζ : IsIrreducible ζ) : ∃ u, u ≫ t = ζ := by
  by_contra hζt
  have hL : LeftCancel P := hM.left
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  have hχn := N.hχ.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  obtain ⟨hzx, hzy⟩ := N.z_ne t ht hαt
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hχχ : N.χ ≫ N.χ ≠ 0 := fun h ↦ hτ0 (by
    rw [show N.μ ≫ N.α ≫ N.α = N.χ ≫ N.χ ≫ N.μ from N.τ_χχ.symm, ← Category.assoc, h, zero_comp])
  have y1 : ¬∃ g, N.μ ≫ g = N.χ := fun ⟨g, hg⟩ ↦ N.hχ.1 (by rw [← hg, N.hyx g, comp_zero])
  have y2 : ¬∃ g, N.μ ≫ g = N.χ ≫ N.χ := fun ⟨g, hg⟩ ↦ hχχ (by rw [← hg, N.hyx g, comp_zero])
  have y3 : ¬∃ g, g ≫ N.μ = N.α := fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])
  have y4 : ¬∃ g, g ≫ N.μ = N.α ≫ N.α := fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp])
  -- `α^m ≫ g = t` forces `m = 0`
  have αpow : ∀ (m : ℕ) (g : y ⟶ z), rpow N.α m ≫ g = t → m = 0 := by
    intro m g hg
    rcases m with _ | m
    · rfl
    · exact absurd ⟨rpow N.α m ≫ g, by rw [← hg, rpow_succ', Category.assoc]⟩ hta
  -- `μ αᵐ g = μ t` forces `m = 0` and `g = t`
  have μpow : ∀ (m : ℕ) (g : y ⟶ z), N.μ ≫ rpow N.α m ≫ g = N.μ ≫ t → m = 0 ∧ g = t := by
    intro m g hg
    have e := hL _ _ _ hg (by rw [hg]; exact hμt)
    obtain rfl := αpow m g e
    exact ⟨rfl, by simpa using e⟩
  have hχμ : ∀ (m : ℕ) {v : P} (g : y ⟶ v), rpow N.χ m ≫ N.μ ≫ g = N.μ ≫ rpow N.α m ≫ g := by
    intro m v g; rw [← Category.assoc, N.rpow_χ_μ, Category.assoc]
  have l1 : ¬∃ g, N.χ ≫ g = N.μ ≫ t := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hμt (by rw [← hg, h, comp_zero])
    obtain ⟨m, g', rfl⟩ := N.fact_x_μ hMo _ g hzx hg0 le_rfl
    have := (μpow (m + 1) g' (by rw [← hg, ← hχμ, rpow_succ']; simp)).1
    omega
  have r1 : ¬∃ g, g ≫ ζ = N.μ ≫ t := by
    rintro ⟨g, hg⟩
    by_cases hwx : w = x
    · subst hwx
      by_cases hgi : IsIso g
      · obtain ⟨hh, rfl⟩ := RayQuiver.eq_id_of_isIso g
        rcases hζ.2.2 _ N.μ t (by simpa using hg) with h | h
        · exact hμn h
        · exact ht.2.1 h
      obtain ⟨n, hn, rfl⟩ := N.hρx g hgi
      rcases N.out_x hMo ζ hζ with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · have := (μpow n u (by rw [← hg, ← hχμ])).1
        omega
      · rcases hζ.2.2 _ N.χ u rfl with h | h
        · exact hχn h
        · exact hzx (eq_of_isIso h).symm
    · have hg0 : g ≠ 0 := fun h ↦ hμt (by rw [← hg, h, zero_comp])
      obtain ⟨m, g', rfl⟩ := N.fact_x_μ hMo _ g hwx hg0 le_rfl
      obtain ⟨rfl, e⟩ := μpow m (g' ≫ ζ) (by rw [← hg, ← hχμ]; simp)
      rcases ht.2.2 _ g' ζ e.symm with h | h
      · exact hζt ⟨inv g', by rw [← e]; simp⟩
      · exact hζ.2.1 h
  have r2 : ¬∃ g, g ≫ ζ = t := by
    rintro ⟨g, hg⟩
    rcases ht.2.2 _ g ζ hg.symm with h | h
    · exact hζt ⟨inv g, by rw [← hg]; simp⟩
    · exact hζ.2.1 h
  exact hM.not_mi42b N.τ N.τ_n hτ0 N.χ N.χ N.μ N.μ N.α N.α t t ζ
    MI42B.not_isRepresentationFinite N.comm hαt
    (irr_not_ftm_comp N.μ (N.α ≫ N.α) hμn (not_isIso_comp_left' _ hαn) ζ hζ)
    (N.ftm_to_x _ N.hχ.1) (N.ftm_to_x _ hχχ)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_μe hL t ht hμt) (N.ftm_to_x _ N.hχ.1) (nfp hτ0 N.χ N.μ N.α (Or.inl hχn) N.τ_χ)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1) (N.ftm_from_y _ N.hα.1)
    (N.ftm_from_y _ ht.1)
    hχn hχn hμn hμn hαn hαn ht.2.1 ht.2.1 hζ.2.1 N.nχμ l1 y1 y2 N.nχμ y1 hta k₁ k₁' hta k₁ r1
    r2 y3 y4 y3 N.nαμ N.nαμ hζt

/-- Morphisms `g` out of `y` with `α ≫ g ≠ 0` are powers of `α` (when `α t = 0`). -/
lemma out_y_α {z : P} (t : y ⟶ z)
    (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e)
    (hαt : N.α ≫ t = 0) :
    ∀ n : ℕ, ∀ {w : P} (g : y ⟶ w), N.α ≫ g ≠ 0 → depth g ≤ n →
      ∃ (h : y = w) (j : ℕ), g = rpow N.α j ≫ eqToHom h := by
  intro n
  induction n with
  | zero =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨h, 0, by simp⟩
    · exfalso
      have hg0 : g ≠ 0 := fun h ↦ hg (by rw [h, comp_zero])
      obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg0 hi
      have := depth_lt_comp_left e r hg0 he.2.1
      omega
  | succ n ih =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨h, 0, by simp⟩
    have hg0 : g ≠ 0 := fun h ↦ hg (by rw [h, comp_zero])
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg0 hi
    rcases hOut e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · have hd' := depth_lt_comp_left N.α (u ≫ r) (by simpa using hg0) N.hα.2.1
      have hα' : N.α ≫ u ≫ r ≠ 0 := fun h ↦ hg (by simp only [Category.assoc]; rw [h, comp_zero])
      obtain ⟨h, j, hj⟩ := ih (u ≫ r) hα' (by simp only [Category.assoc] at hd hd'; omega)
      refine ⟨h, j + 1, ?_⟩
      rw [Category.assoc, hj, rpow_succ', Category.assoc]
    · exact absurd (by rw [Category.assoc, ← Category.assoc N.α, hαt, zero_comp]) hg

/-- **[mild] MIDB d), third part**: if `μ t ≠ 0` and `α t = 0`, `t` kills every arrow
out of `z` (figure 4.2, third diagram). -/
theorem midb_d3 (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {z : P} (t : y ⟶ z)
    (ht : IsIrreducible t) (hta : ¬∃ g, N.α ≫ g = t) (hμt : N.μ ≫ t ≠ 0) (hαt : N.α ≫ t = 0)
    {v : P} (ζ : z ⟶ v) (hζ : IsIrreducible ζ) : t ≫ ζ = 0 := by
  by_contra htζ
  have hL : LeftCancel P := hM.left
  have hR : RightCancel P := hM.right
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  have hχn := N.hχ.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  obtain ⟨hzx, hzy⟩ := N.z_ne t ht hαt
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hχχ : N.χ ≫ N.χ ≠ 0 := fun h ↦ hτ0 (by
    rw [show N.μ ≫ N.α ≫ N.α = N.χ ≫ N.χ ≫ N.μ from N.τ_χχ.symm, ← Category.assoc, h, zero_comp])
  have y1 : ¬∃ g, N.μ ≫ g = N.χ := fun ⟨g, hg⟩ ↦ N.hχ.1 (by rw [← hg, N.hyx g, comp_zero])
  have y2 : ¬∃ g, N.μ ≫ g = N.χ ≫ N.χ := fun ⟨g, hg⟩ ↦ hχχ (by rw [← hg, N.hyx g, comp_zero])
  have y3 : ¬∃ g, g ≫ N.μ = N.α := fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])
  have y4 : ¬∃ g, g ≫ N.μ = N.α ≫ N.α := fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp])
  have hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e →
      (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e := by
    intro c e he
    by_contra h
    push Not at h
    refine N.midb_a hM t e ht he hta (fun ⟨u, hu⟩ ↦ h.1 u hu) (fun ⟨u, hu⟩ ↦ h.2 u hu) ?_
    rintro ⟨g, hg⟩
    rcases ht.2.2 _ e g hg.symm with h' | h'
    · exact he.2.1 h'
    · exact h.2 (inv g) (by rw [← hg]; simp)
  have αpow : ∀ (m : ℕ) (g : y ⟶ z), rpow N.α m ≫ g = t → m = 0 := by
    intro m g hg
    rcases m with _ | m
    · rfl
    · exact absurd ⟨rpow N.α m ≫ g, by rw [← hg, rpow_succ', Category.assoc]⟩ hta
  have μpow : ∀ (m : ℕ) (g : y ⟶ z), N.μ ≫ rpow N.α m ≫ g = N.μ ≫ t → m = 0 := by
    intro m g hg
    exact αpow m g (hL _ _ _ hg (by rw [hg]; exact hμt))
  have hχμ : ∀ (m : ℕ) {v : P} (g : y ⟶ v), rpow N.χ m ≫ N.μ ≫ g = N.μ ≫ rpow N.α m ≫ g := by
    intro m v g; rw [← Category.assoc, N.rpow_χ_μ, Category.assoc]
  have l1 : ¬∃ g, N.χ ≫ g = N.μ ≫ t := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ hμt (by rw [← hg, h, comp_zero])
    obtain ⟨m, g', rfl⟩ := N.fact_x_μ hMo _ g hzx hg0 le_rfl
    have := μpow (m + 1) g' (by rw [← hg, ← hχμ, rpow_succ']; simp)
    omega
  have l2 : ¬∃ g, N.α ≫ g = t ≫ ζ := by
    rintro ⟨g, hg⟩
    obtain ⟨h, j, rfl⟩ := N.out_y_α t hOut hαt _ g (by rw [hg]; exact htζ) le_rfl
    subst h
    have hfull : t ≫ ζ = rpow N.α (j + 1) := by rw [← hg, rpow_succ']; simp
    rcases N.into_y hM ζ hζ with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact htζ (by rw [← Category.assoc, N.hyx (t ≫ u), zero_comp])
    · have e : (t ≫ u) ≫ N.α = rpow N.α j ≫ N.α := by
        rw [Category.assoc, hfull, rpow_succ]
      have e' := hR _ _ _ e (by rw [Category.assoc]; exact htζ)
      rcases j with _ | j
      · haveI : IsIso (t ≫ u) := by rw [e']; simp; infer_instance
        exact ht.2.1 (ray_isIso_factors t u).1
      · apply htζ
        rw [hfull, rpow_succ', ← e', ← Category.assoc, hαt, zero_comp]
  have r2 : ¬∃ g, t ≫ g = N.α ≫ N.α := k₁'
  exact hM.not_mi42c N.τ N.τ_n hτ0 N.χ N.χ N.μ N.μ N.α N.α t t ζ
    MI42C.not_isRepresentationFinite N.comm hαt
    (N.ftm_to_x _ N.hχ.1) (N.ftm_to_x _ hχχ)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_μe hL t ht hμt) (N.ftm_to_x _ N.hχ.1) (nfp hτ0 N.χ N.μ N.α (Or.inl hχn) N.τ_χ)
    (N.ftm_from_y _ htζ) (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ ht.1)
    (irr_not_ftm_comp N.μ (N.α ≫ N.α) hμn (not_isIso_comp_left' _ hαn) ζ hζ)
    hχn hχn hμn hμn hαn hαn ht.2.1 ht.2.1 hζ.2.1 N.nχμ l1 y1 y2 N.nχμ y1 hta l2 k₁ r2 hta k₁
    y3 y4 y3 N.nαμ N.nαμ

/-- **[mild] MIDB c), second part, `α t = 0`**: `α³ = 0` (figure 4.2, first diagram). -/
theorem midb_α3' (hM : MildHyp k P) {z : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) (hαt : N.α ≫ t = 0) : N.α ≫ N.α ≫ N.α = 0 := by
  by_contra h3
  have hR : RightCancel P := hM.right
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  have hχn := N.hχ.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hχχ : N.χ ≫ N.χ ≠ 0 := fun h ↦ hτ0 (by
    rw [show N.μ ≫ N.α ≫ N.α = N.χ ≫ N.χ ≫ N.μ from N.τ_χχ.symm, ← Category.assoc, h, zero_comp])
  have y1 : ¬∃ g, N.μ ≫ g = N.χ := fun ⟨g, hg⟩ ↦ N.hχ.1 (by rw [← hg, N.hyx g, comp_zero])
  have y2 : ¬∃ g, N.μ ≫ g = N.χ ≫ N.χ := fun ⟨g, hg⟩ ↦ hχχ (by rw [← hg, N.hyx g, comp_zero])
  have y3 : ¬∃ g, g ≫ N.μ = N.α := fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])
  have y4 : ¬∃ g, g ≫ N.μ = N.α ≫ N.α := fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp])
  have y5 : ¬∃ g, g ≫ N.μ = (N.α ≫ N.α) ≫ N.α := fun ⟨g, hg⟩ ↦ h3 (by
    rw [show N.α ≫ N.α ≫ N.α = (N.α ≫ N.α) ≫ N.α by simp, ← hg, N.hyx g, zero_comp])
  have k3 : ¬∃ g, t ≫ g = (N.α ≫ N.α) ≫ N.α := by
    rintro ⟨g, hg⟩
    have hg0 : g ≠ 0 := fun h ↦ h3 (by rw [show N.α ≫ N.α ≫ N.α = (N.α ≫ N.α) ≫ N.α by simp,
      ← hg, h, comp_zero])
    by_cases hgi : IsIso g
    · rcases ht.2.2 _ (N.α ≫ N.α) (N.α ≫ inv g) (by rw [← Category.assoc, ← hg]; simp) with
        h | h
      · exact hαn (ray_isIso_factors N.α N.α).1
      · exact hαn (ray_isIso_factors N.α (inv g)).1
    rcases N.fact_y hM g hg0 hgi with ⟨g', rfl⟩ | ⟨g', rfl⟩
    · exact h3 (by rw [show N.α ≫ N.α ≫ N.α = (N.α ≫ N.α) ≫ N.α by simp, ← hg,
        ← Category.assoc, N.hyx (t ≫ g'), zero_comp])
    · have e : (t ≫ g') ≫ N.α = (N.α ≫ N.α) ≫ N.α := by rw [Category.assoc, hg]
      exact k₁' ⟨g', hR _ _ _ e (by rw [e]; simpa using h3)⟩
  exact hM.not_mi42a N.τ N.τ_n hτ0 N.χ N.χ N.μ N.μ N.α N.α N.α t t
    MI42A.not_isRepresentationFinite N.comm hαt
    (N.ftm_to_x _ N.hχ.1) (N.ftm_to_x _ hχχ)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_to_x _ N.hχ.1) (nfp hτ0 N.χ N.μ N.α (Or.inl hχn) N.τ_χ)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ (by simpa using h3))
    (N.ftm_from_y _ ht.1) (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1)
    (N.ftm_from_y _ N.hα.1)
    hχn hχn hμn hμn hαn hαn hαn ht.2.1 ht.2.1 N.nχμ y1 y2 N.nχμ y1 hta k₁ k₁' k3 hta k₁ k₁'
    y4 y3 y5 y4 y3 N.nαμ N.nαμ

/-- **The remaining [mild] MIDB facts** (figure 4.2). -/
theorem midbRest (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) : N.MIDBRest := by
  intro z t ht hta
  exact ⟨fun hαt ↦ N.midb_α3' hM t ht hta hαt,
    fun hμt hαt c e he ↦ N.midb_d2 hM hMo t ht hta hμt hαt e he,
    fun hμt hαt c e he ↦ N.midb_d3 hM hMo t ht hta hμt hαt e he⟩

end DBN

variable (P) in
/-- **The exceptional dumb-bells**: closed, or with a tail at `y` or (dually) at `x`. -/
def DBExc : Prop :=
  ∃ (x y : P) (N : DBN x y), N.Closed ∨ (∃ (z : P) (t : y ⟶ z), N.TailY t) ∨
    (letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
     ∃ (z : Pᵒᵖ) (t : Opposite.op x ⟶ z), N.op.TailY t)

namespace DBData

/-- **[mild] Theorem 3, dumb-bell case, ray level**: a dumb-bell contour in a category with
no projective-injective vertex and no split point is exceptional. -/
theorem dbExc {x y : RayVert P} (D : DBData x y) (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ)
    (hOS : OneSidedCyclic P) (hE : EndCyclic P) (hNPI : NoProjInj P) (hNS : NoSplit P) :
    DBExc P := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨N⟩ := D.toN hM hOS hE
  exact ⟨_, _, N, N.classify hM hMo hNPI hNS (N.midbRest hM hMo) (N.op.midbRest hMo hMo.op)⟩

end DBData

namespace DBN

end DBN

end RayCat

end LargeIndecomposable
