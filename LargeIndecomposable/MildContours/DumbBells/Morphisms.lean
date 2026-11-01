module

public import LargeIndecomposable.MildContours.DumbBells.ExtraArrow

/-!
# Dumb-bells: the morphisms out of `x` and into `y`

Given the arrows out of `y` (`α` and possibly `t` with `μ t = 0`) and into `x`
(only `χ`), every nonzero morphism out of `x` is `χⁱ` or `μ αʲ`, and every
nonzero morphism into `y` is `αʲ` or `μ αʲ`.
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

/-- The arrows out of `x` are `χ` and `μ`. -/
lemma out_x (hMo : MildHyp k Pᵒᵖ) {c : P} (e : x ⟶ c) (he : IsIrreducible e) :
    (∃ u, N.μ ≫ u = e) ∨ ∃ u, N.χ ≫ u = e := by
  by_contra h
  push Not at h
  exact N.ldb_op hMo e he (fun ⟨u, hu⟩ ↦ h.1 u hu) (fun ⟨u, hu⟩ ↦ h.2 u hu)

/-- **Morphisms out of `y` not killed by `μ`** are powers of `α`. -/
lemma out_y_cls (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e →
      (∃ u, N.α ≫ u = e) ∨ N.μ ≫ e = 0) :
    ∀ n : ℕ, ∀ {w : P} (g : y ⟶ w), N.μ ≫ g ≠ 0 → depth g ≤ n →
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
    rcases hOut e he with ⟨u, rfl⟩ | hu
    · have hd' := depth_lt_comp_left N.α (u ≫ r) (by simpa using hg0) N.hα.2.1
      have hμ' : N.μ ≫ u ≫ r ≠ 0 := fun h ↦ hg (by
        rw [Category.assoc, ← Category.assoc N.μ, ← N.comm, Category.assoc, h, comp_zero])
      obtain ⟨h, j, hj⟩ := ih (u ≫ r) hμ' (by simp only [Category.assoc] at hd hd'; omega)
      refine ⟨h, j + 1, ?_⟩
      rw [Category.assoc, hj, rpow_succ', Category.assoc]
    · exact absurd (by rw [← Category.assoc, hu, zero_comp]) hg

/-- A nonzero non-invertible morphism ends with an arrow. -/
lemma exists_last {a b : P} (f : a ⟶ b) (hf0 : f ≠ 0) (hf : ¬IsIso f) :
    ∃ (c : P) (r : a ⟶ c) (e : c ⟶ b), IsIrreducible e ∧ f = r ≫ e := by
  obtain ⟨c, p, e, hp⟩ := MildContour.exists_last_arrow f hf0 hf
  exact ⟨c.out, pathVal p, e.1, e.2, hp⟩

/-- **Morphisms out of `x`** are `χⁱ` or `μ αʲ`. -/
lemma out_x_cls (hMo : MildHyp k Pᵒᵖ) (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e →
      (∃ u, N.α ≫ u = e) ∨ N.μ ≫ e = 0) :
    ∀ n : ℕ, ∀ {w : P} (f : x ⟶ w), f ≠ 0 → depth f ≤ n →
      (∃ (h : x = w) (i : ℕ), f = rpow N.χ i ≫ eqToHom h) ∨
        ∃ (h : y = w) (j : ℕ), f = N.μ ≫ rpow N.α j ≫ eqToHom h := by
  intro n
  induction n with
  | zero =>
    intro w f hf hd
    by_cases hi : IsIso f
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso f
      exact Or.inl ⟨h, 0, by simp⟩
    · exfalso
      obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      omega
  | succ n ih =>
    intro w f hf hd
    by_cases hi : IsIso f
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso f
      exact Or.inl ⟨h, 0, by simp⟩
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
    rcases N.out_x hMo e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · obtain ⟨h, j, hj⟩ := N.out_y_cls hOut _ (u ≫ r) (by simpa using hf) le_rfl
      exact Or.inr ⟨h, j, by rw [Category.assoc, hj]⟩
    · have hd' := depth_lt_comp_left N.χ (u ≫ r) (by simpa using hf) N.hχ.2.1
      rcases ih (u ≫ r) (fun h ↦ hf (by rw [Category.assoc, h, comp_zero]))
          (by simp only [Category.assoc] at hd hd'; omega) with ⟨h, i, hi⟩ | ⟨h, j, hj⟩
      · exact Or.inl ⟨h, i + 1, by rw [Category.assoc, hi, rpow_succ', Category.assoc]⟩
      · refine Or.inr ⟨h, j + 1, ?_⟩
        rw [Category.assoc, hj, ← Category.assoc, N.comm, rpow_succ']; simp

/-- **Morphisms into `x`** are powers of `χ`. -/
lemma into_x_cls (hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e) :
    ∀ n : ℕ, ∀ {w : P} (g : w ⟶ x), g ≠ 0 → depth g ≤ n →
      ∃ (h : w = x) (i : ℕ), g = eqToHom h ≫ rpow N.χ i := by
  intro n
  induction n with
  | zero =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨h, 0, by simp⟩
    · exfalso
      obtain ⟨c, r, e, he, rfl⟩ := exists_last g hg hi
      have := depth_lt_comp_right r e hg he.2.1
      omega
  | succ n ih =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact ⟨h, 0, by simp⟩
    obtain ⟨c, r, e, he, rfl⟩ := exists_last g hg hi
    obtain ⟨u, rfl⟩ := hIn e he
    have hd' := depth_lt_comp_right (r ≫ u) N.χ (by simpa using hg) N.hχ.2.1
    obtain ⟨h, i, hi⟩ := ih (r ≫ u) (fun h ↦ hg (by rw [← Category.assoc, h, zero_comp]))
      (by simp only [Category.assoc] at hd hd'; omega)
    exact ⟨h, i + 1, by rw [← Category.assoc, hi, rpow_succ, Category.assoc]⟩

/-- **Morphisms into `y`** are `αʲ` or `μ αʲ`. -/
lemma into_y_cls (hM : MildHyp k P)
    (hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e) :
    ∀ n : ℕ, ∀ {w : P} (ν : w ⟶ y), ν ≠ 0 → depth ν ≤ n →
      (∃ (h : w = y) (j : ℕ), ν = eqToHom h ≫ rpow N.α j) ∨
        ∃ (h : w = x) (j : ℕ), ν = eqToHom h ≫ N.μ ≫ rpow N.α j := by
  intro n
  induction n with
  | zero =>
    intro w ν hν hd
    by_cases hi : IsIso ν
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso ν
      exact Or.inl ⟨h, 0, by simp⟩
    · exfalso
      obtain ⟨c, r, e, he, rfl⟩ := exists_last ν hν hi
      have := depth_lt_comp_right r e hν he.2.1
      omega
  | succ n ih =>
    intro w ν hν hd
    by_cases hi : IsIso ν
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso ν
      exact Or.inl ⟨h, 0, by simp⟩
    obtain ⟨c, r, e, he, rfl⟩ := exists_last ν hν hi
    rcases N.into_y hM e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · obtain ⟨h, i, hi⟩ := N.into_x_cls hIn _ (r ≫ u)
        (fun h ↦ hν (by rw [← Category.assoc, h, zero_comp])) le_rfl
      exact Or.inr ⟨h, i, by rw [← Category.assoc, hi, Category.assoc, N.rpow_χ_μ]⟩
    · have hd' := depth_lt_comp_right (r ≫ u) N.α (by simpa using hν) N.hα.2.1
      rcases ih (r ≫ u) (fun h ↦ hν (by rw [← Category.assoc, h, zero_comp]))
          (by simp only [Category.assoc] at hd hd'; omega) with ⟨h, j, hj⟩ | ⟨h, j, hj⟩
      · exact Or.inl ⟨h, j + 1, by rw [← Category.assoc, hj, rpow_succ, Category.assoc]⟩
      · exact Or.inr ⟨h, j + 1, by rw [← Category.assoc, hj, rpow_succ]; simp⟩

lemma rpow_three {a : P} (e : a ⟶ a) (h : e ≫ e ≫ e = 0) : ∀ j, 3 ≤ j → rpow e j = 0 := by
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = 3 + m := ⟨j - 3, by omega⟩
  rw [rpow_add, show rpow e 3 = e ≫ e ≫ e by simp [rpow_succ], h, zero_comp]

lemma μα_ne (j : ℕ) (hj : j ≤ 2) : N.μ ≫ rpow N.α j ≠ 0 := by
  intro h
  apply N.hτ
  obtain ⟨m, hm⟩ : ∃ m, 2 = j + m := ⟨2 - j, by omega⟩
  rw [show N.μ ≫ N.α ≫ N.α = N.μ ≫ rpow N.α 2 by simp [rpow_succ], hm, rpow_add,
    ← Category.assoc, h, zero_comp]

/-- **An open dumb-bell with `μ t = 0` has a projective-injective `P_x`** ([mild] Theorem 3). -/
theorem projInj_of_μt (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ)
    (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ N.μ ≫ e = 0)
    (hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e)
    (hχ3 : N.χ ≫ N.χ ≫ N.χ = 0) (hα3 : N.α ≫ N.α ≫ N.α = 0) :
    ProjInjAt (N.μ ≫ N.α ≫ N.α) := by
  have rα := rpow_three N.α hα3
  have rχ := rpow_three N.χ hχ3
  have hμα2 : N.μ ≫ N.α ≫ N.α = N.μ ≫ rpow N.α 2 := by simp [rpow_succ]
  refine ⟨N.hτ, ?_, ?_, ?_, ?_⟩
  · intro w ζ hζ
    by_contra h
    have hμζ : N.μ ≫ ζ ≠ 0 := fun h' ↦ h (by
      rw [show N.μ ≫ N.α ≫ N.α = N.χ ≫ N.χ ≫ N.μ from N.τ_χχ.symm]; simp [h'])
    obtain ⟨hh, j, rfl⟩ := N.out_y_cls hOut _ ζ hμζ le_rfl
    subst hh
    have hj : j ≠ 0 := by rintro rfl; exact hζ (by simp; infer_instance)
    apply h
    rw [hμα2, ← Category.assoc, Category.assoc N.μ, ← rpow_add, rα _ (by omega)]; simp
  · intro u ζ hζ
    by_contra h
    have hζ0 : ζ ≠ 0 := fun h' ↦ h (by rw [h', zero_comp])
    obtain ⟨hh, i, rfl⟩ := N.into_x_cls hIn _ ζ hζ0 le_rfl
    subst hh
    have hi : i ≠ 0 := by rintro rfl; exact hζ (by simp; infer_instance)
    apply h
    rw [hμα2, eqToHom_refl, Category.id_comp, ← Category.assoc, N.rpow_χ_μ, Category.assoc,
      ← rpow_add, rα _ (by omega), comp_zero]
  · intro w μ' hμ' hd
    rcases N.out_x_cls hMo hOut _ μ' hμ' le_rfl with ⟨hh, i, rfl⟩ | ⟨hh, j, rfl⟩
    · subst hh
      exfalso
      by_cases hi : i ≤ 2
      · apply N.μα_ne i hi
        have := hd N.μ N.hμ.2.1
        rw [eqToHom_refl, Category.comp_id, N.rpow_χ_μ] at this
        exact this
      · exact hμ' (by rw [rχ i (by omega), zero_comp])
    · subst hh
      refine ⟨rfl, ?_⟩
      have hj : j ≤ 2 := by
        by_contra hj
        exact hμ' (by rw [rα j (by omega)]; simp)
      have hj2 : j = 2 := by
        by_contra hj2
        have := hd N.α N.hα.2.1
        rw [eqToHom_refl, Category.comp_id, Category.assoc, ← rpow_succ] at this
        exact N.μα_ne (j + 1) (by omega) this
      subst hj2
      simp [rpow_succ]
  · intro w ν hν hd
    rcases N.into_y_cls hM hIn _ ν hν le_rfl with ⟨hh, j, rfl⟩ | ⟨hh, j, rfl⟩
    · subst hh
      exfalso
      by_cases hj : j ≤ 2
      · apply N.μα_ne j hj
        have := hd N.μ N.hμ.2.1
        rwa [eqToHom_refl, Category.id_comp] at this
      · exact hν (by rw [rα j (by omega)]; simp)
    · subst hh
      refine ⟨rfl, ?_⟩
      have hj : j ≤ 2 := by
        by_contra hj
        exact hν (by rw [rα j (by omega)]; simp)
      have hj2 : j = 2 := by
        by_contra hj2
        have := hd N.χ N.hχ.2.1
        rw [eqToHom_refl, Category.id_comp, ← Category.assoc, N.comm, Category.assoc,
          ← rpow_succ'] at this
        exact N.μα_ne (j + 1) (by omega) this
      subst hj2
      simp [rpow_succ]

/-- **Morphisms out of `y`** when `α t = 0` and `t` kills every arrow out of `z`. -/
lemma out_y_all {z : P} (t : y ⟶ z)
    (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e)
    (hαt : N.α ≫ t = 0) (hz : ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0) :
    ∀ n : ℕ, ∀ {w : P} (g : y ⟶ w), g ≠ 0 → depth g ≤ n →
      (∃ (h : y = w) (j : ℕ), g = rpow N.α j ≫ eqToHom h) ∨ ∃ h : z = w, g = t ≫ eqToHom h := by
  intro n
  induction n with
  | zero =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact Or.inl ⟨h, 0, by simp⟩
    · exfalso
      obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg hi
      have := depth_lt_comp_left e r hg he.2.1
      omega
  | succ n ih =>
    intro w g hg hd
    by_cases hi : IsIso g
    · obtain ⟨h, rfl⟩ := RayQuiver.eq_id_of_isIso g
      exact Or.inl ⟨h, 0, by simp⟩
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' g hg hi
    rcases hOut e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · have hd' := depth_lt_comp_left N.α (u ≫ r) (by simpa using hg) N.hα.2.1
      rcases ih (u ≫ r) (fun h ↦ hg (by rw [Category.assoc, h, comp_zero]))
          (by simp only [Category.assoc] at hd hd'; omega) with ⟨h, j, hj⟩ | ⟨h, hj⟩
      · exact Or.inl ⟨h, j + 1, by rw [Category.assoc, hj, rpow_succ', Category.assoc]⟩
      · exact absurd (by rw [Category.assoc, hj, ← Category.assoc, hαt, zero_comp]) hg
    · by_cases hur : IsIso (u ≫ r)
      · obtain ⟨h, hh⟩ := RayQuiver.eq_id_of_isIso (u ≫ r)
        exact Or.inr ⟨h, by rw [Category.assoc, hh]⟩
      · exfalso
        have h0 : u ≫ r ≠ 0 := fun h ↦ hg (by rw [Category.assoc, h, comp_zero])
        obtain ⟨c', e', r', he', hr'⟩ := exists_first_arrow' (u ≫ r) h0 hur
        exact hg (by rw [Category.assoc, hr', ← Category.assoc, hz e' he', zero_comp])

/-- **Morphisms out of `x`** in the same situation. -/
lemma out_x_all (hMo : MildHyp k Pᵒᵖ) {z : P} (t : y ⟶ z)
    (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e)
    (hαt : N.α ≫ t = 0) (hz : ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0) :
    ∀ n : ℕ, ∀ {w : P} (f : x ⟶ w), f ≠ 0 → depth f ≤ n →
      w = x ∨ w = y ∨ w = z := by
  intro n
  induction n with
  | zero =>
    intro w f hf hd
    by_cases hi : IsIso f
    · exact Or.inl (eq_of_isIso hi).symm
    · exfalso
      obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
      have := depth_lt_comp_left e r hf he.2.1
      omega
  | succ n ih =>
    intro w f hf hd
    by_cases hi : IsIso f
    · exact Or.inl (eq_of_isIso hi).symm
    obtain ⟨c, e, r, he, rfl⟩ := exists_first_arrow' f hf hi
    rcases N.out_x hMo e he with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · rcases N.out_y_all t hOut hαt hz _ (u ≫ r)
        (fun h ↦ hf (by rw [Category.assoc, h, comp_zero])) le_rfl with
        ⟨h, -, -⟩ | ⟨h, -⟩
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h.symm)
    · have hd' := depth_lt_comp_left N.χ (u ≫ r) (by simpa using hf) N.hχ.2.1
      exact ih (u ≫ r) (fun h ↦ hf (by rw [Category.assoc, h, comp_zero]))
        (by simp only [Category.assoc] at hd hd'; omega)

/-- **Morphisms into `z`** come from `x`, `y` or `z` when only `t` ends in `z`. -/
lemma into_z_cls (hM : MildHyp k P)
    (hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e) {z : P} (t : y ⟶ z)
    (hInZ : ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e) {w : P} (ν : w ⟶ z)
    (hν : ν ≠ 0) : w = z ∨ w = x ∨ w = y := by
  by_cases hi : IsIso ν
  · exact Or.inl (eq_of_isIso hi)
  obtain ⟨c, r, e, he, rfl⟩ := exists_last ν hν hi
  obtain ⟨u, rfl⟩ := hInZ e he
  rcases N.into_y_cls hM hIn _ (r ≫ u) (fun h ↦ hν (by rw [← Category.assoc, h, zero_comp]))
    le_rfl with ⟨h, -, -⟩ | ⟨h, -, -⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

/-- **An open dumb-bell with `μ t ≠ 0` and an arrow out of `z` gives a split point `z`**. -/
theorem split_of_μt (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {z : P} (t : y ⟶ z)
    (ht : IsIrreducible t)
    (hOut : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e)
    (hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e)
    (hInZ : ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e)
    (hαt : N.α ≫ t = 0) (hz : ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0)
    (hμt : N.μ ≫ t ≠ 0) {v : P} (ζ : z ⟶ v) (hζ : IsIrreducible ζ) :
    SplitAt ({x, y} : Set P) z := by
  have hzx : z ≠ x := fun h ↦ by subst h; exact ht.1 (N.hyx t)
  have hzy : z ≠ y := fun h ↦ by
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
  have mem : ∀ {i : P}, i ∈ ({x, y} : Set P) ↔ i = x ∨ i = y := fun {i} ↦ by simp
  have outx := fun {w : P} (f : x ⟶ w) (hf : f ≠ 0) ↦ N.out_x_all hMo t hOut hαt hz _ f hf le_rfl
  have outy := fun {w : P} (f : y ⟶ w) (hf : f ≠ 0) ↦ N.out_y_all t hOut hαt hz _ f hf le_rfl
  have inx := fun {w : P} (f : w ⟶ x) (hf : f ≠ 0) ↦ N.into_x_cls hIn _ f hf le_rfl
  have iny := fun {w : P} (f : w ⟶ y) (hf : f ≠ 0) ↦ N.into_y_cls hM hIn _ f hf le_rfl
  have inz := fun {w : P} (f : w ⟶ z) (hf : f ≠ 0) ↦ N.into_z_cls hM hIn t hInZ f hf
  have src : ∀ {w j : P}, (j = x ∨ j = y) → ∀ f : w ⟶ j, f ≠ 0 → w = x ∨ w = y := by
    rintro w j (rfl | rfl) f hf
    · obtain ⟨h, -, -⟩ := inx f hf; exact Or.inl h
    · rcases iny f hf with ⟨h, -, -⟩ | ⟨h, -, -⟩
      · exact Or.inr h
      · exact Or.inl h
  refine ⟨by rw [mem]; push Not; exact ⟨hzx, hzy⟩, ?_, ?_, ?_, ?_, ?_, ⟨x, by simp, N.μ ≫ t, hμt⟩,
    ?_⟩
  · intro i hi j hj hjz f
    by_contra hf
    rw [mem] at hi hj
    push Not at hj
    rcases hi with rfl | rfl
    · rcases outx f hf with h | h | h
      · exact hj.1 h
      · exact hj.2 h
      · exact hjz h
    · rcases outy f hf with ⟨h, -, -⟩ | ⟨h, -⟩
      · exact hj.2 h.symm
      · exact hjz h.symm
  · intro i hi hiz j hj f
    by_contra hf
    rw [mem] at hi hj
    exact (src hj f hf).elim (fun h ↦ hi (Or.inl h)) (fun h ↦ hi (Or.inr h))
  · intro i hi hiz f
    by_contra hf
    rw [mem] at hi
    rcases inz f hf with h | h | h
    · exact hiz h
    · exact hi (Or.inl h)
    · exact hi (Or.inr h)
  · intro j hj f
    by_contra hf
    rw [mem] at hj
    rcases src hj f hf with h | h
    · exact hzx h
    · exact hzy h
  · intro f hf
    by_contra hf0
    by_cases hi : IsIso f
    · exact hf hi
    obtain ⟨c, r, e, he, rfl⟩ := exists_last f hf0 hi
    obtain ⟨u, rfl⟩ := hInZ e he
    rcases src (Or.inr rfl) (r ≫ u) (fun h ↦ hf0 (by rw [← Category.assoc, h, zero_comp])) with
      h | h
    · exact hzx h
    · exact hzy h
  · have hv0 : ζ ≠ 0 := hζ.1
    refine ⟨v, ?_, ?_, ζ, hv0⟩
    · rw [mem]
      rintro (rfl | rfl)
      · exact (src (Or.inl rfl) ζ hv0).elim hzx hzy
      · exact (src (Or.inr rfl) ζ hv0).elim hzx hzy
    · rintro rfl
      rcases inz ζ hv0 with h | h | h
      · obtain ⟨c, r, e, he, hre⟩ := exists_last ζ hv0 hζ.2.1
        obtain ⟨u, rfl⟩ := hInZ e he
        rcases src (Or.inr rfl) (r ≫ u) (fun h ↦ hv0 (by rw [hre, ← Category.assoc, h,
          zero_comp])) with h' | h'
        · exact hzx h'
        · exact hzy h'
      · exact hzx h
      · exact hzy h

/-- A dumb-bell with a tail `t : y ⟶ z` ending in a sink `z`. -/
structure TailY {z : P} (t : y ⟶ z) : Prop where
  ht : IsIrreducible t
  μt : N.μ ≫ t ≠ 0
  αt : N.α ≫ t = 0
  out_y : ∀ {c : P} (e : y ⟶ c), IsIrreducible e → (∃ u, N.α ≫ u = e) ∨ ∃ u, t ≫ u = e
  into_x : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e
  into_z : ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e
  sink : ∀ {c : P} (e : z ⟶ c), ¬IsIrreducible e
  χ3 : N.χ ≫ N.χ ≫ N.χ = 0

/-- **An open dumb-bell** (an extra arrow `t` out of `y`) is a dumb-bell with a tail, or
gives a projective-injective vertex or a split point. The three remaining [mild] MIDB
facts are hypotheses. -/
theorem open_y (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hNPI : NoProjInj P) (hNS : NoSplit P)
    {z : P} (t : y ⟶ z) (ht : IsIrreducible t) (hta : ¬∃ g, N.α ≫ g = t)
    (hA : N.α ≫ t = 0 → N.α ≫ N.α ≫ N.α = 0)
    (hB : N.μ ≫ t ≠ 0 → N.α ≫ t = 0 → ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e)
    (hC : N.μ ≫ t ≠ 0 → N.α ≫ t = 0 → ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0) :
    N.TailY t := by
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
  have hIn : ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e := by
    intro c e he
    by_contra h
    exact N.midb_b hM hMo t ht hta e he h
  have hχ3 := N.midb_χ3 hM t ht hta
  by_cases hμt : N.μ ≫ t = 0
  · exfalso
    have hα3 : N.α ≫ N.α ≫ N.α = 0 := by
      by_cases hαt : N.α ≫ t = 0
      · exact hA hαt
      · exact N.midb_α3_of hM t ht hta hαt
    refine hNPI _ (N.projInj_of_μt hM hMo (fun e he ↦ ?_) hIn hχ3 hα3)
    rcases hOut e he with h | ⟨u, rfl⟩
    · exact Or.inl h
    · exact Or.inr (by rw [← Category.assoc, hμt, zero_comp])
  have hαt := N.midb_d1 hM t ht hta hμt
  have hInZ : ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e :=
    fun e he ↦ hB hμt hαt e he
  have hz : ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0 := fun e he ↦ hC hμt hαt e he
  refine ⟨ht, hμt, hαt, hOut, hIn, hInZ, ?_, hχ3⟩
  intro c e he
  exact hNS _ _ (N.split_of_μt hM hMo t ht hOut hIn hInZ hαt hz hμt e he)

/-- The remaining [mild] MIDB facts, from cleaving diagrams (figure 4.2). -/
def MIDBRest : Prop :=
  ∀ {z : P} (t : y ⟶ z), IsIrreducible t → (¬∃ g, N.α ≫ g = t) →
    (N.α ≫ t = 0 → N.α ≫ N.α ≫ N.α = 0) ∧
    (N.μ ≫ t ≠ 0 → N.α ≫ t = 0 → ∀ {c : P} (e : c ⟶ z), IsIrreducible e → ∃ u, u ≫ t = e) ∧
    (N.μ ≫ t ≠ 0 → N.α ≫ t = 0 → ∀ {c : P} (e : z ⟶ c), IsIrreducible e → t ≫ e = 0)

/-- No arrow at `x` or `y` besides `χ`, `μ`, `α`. -/
def Closed : Prop :=
  (∀ {c : P} (e : y ⟶ c), IsIrreducible e → ∃ u, N.α ≫ u = e) ∧
    ∀ {c : P} (e : c ⟶ x), IsIrreducible e → ∃ u, u ≫ N.χ = e

/-- **[mild] Theorem 3, dumb-bell case, ray level**: under the global hypotheses a
dumb-bell is closed, or has a tail at `y`, or (dually) a tail at `x`. -/
theorem classify (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) (hNPI : NoProjInj P) (hNS : NoSplit P)
    (hR : N.MIDBRest)
    (hRo : letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ); letI : Fintype Pᵒᵖ := Fintype.ofFinite _
      letI : DecidableEq Pᵒᵖ := Classical.decEq _; N.op.MIDBRest) :
    N.Closed ∨ (∃ (z : P) (t : y ⟶ z), N.TailY t) ∨
      (letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
       ∃ (z : Pᵒᵖ) (t : Opposite.op x ⟶ z), N.op.TailY t) := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  by_cases h1 : ∃ (z : P) (t : y ⟶ z), IsIrreducible t ∧ ¬∃ g, N.α ≫ g = t
  · obtain ⟨z, t, ht, hta⟩ := h1
    obtain ⟨hA, hB, hC⟩ := hR t ht hta
    exact Or.inr (Or.inl ⟨z, t, N.open_y hM hMo hNPI hNS t ht hta hA hB hC⟩)
  by_cases h2 : ∃ (w : P) (ζ : w ⟶ x), IsIrreducible ζ ∧ ¬∃ g, g ≫ N.χ = ζ
  · obtain ⟨w, ζ, hζ, hζc⟩ := h2
    have hζ' : IsIrreducible ζ.op := (isIrreducible_op _).2 hζ
    have hζc' : ¬∃ g, N.op.α ≫ g = ζ.op := neg_op_left hζc
    obtain ⟨hA, hB, hC⟩ := hRo ζ.op hζ' hζc'
    exact Or.inr (Or.inr ⟨_, ζ.op,
      N.op.open_y hMo hMo.op hNPI.op hNS.op ζ.op hζ' hζc' hA hB hC⟩)
  push Not at h1 h2
  exact Or.inl ⟨fun e he ↦ h1 _ e he, fun e he ↦ h2 _ e he⟩

end DBN

end RayCat

end LargeIndecomposable
