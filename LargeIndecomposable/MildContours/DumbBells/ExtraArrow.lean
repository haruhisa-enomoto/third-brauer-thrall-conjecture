module

public import LargeIndecomposable.MildContours.DumbBells.NormalForm
public import LargeIndecomposable.Cleaving.Shapes.ShapeMI41A
public import LargeIndecomposable.Cleaving.Shapes.ShapeMI41D
public import LargeIndecomposable.Cleaving.Families.FamMI41B
public import LargeIndecomposable.Cleaving.Families.FamMI41C

/-!
# Dumb-bells with an extra arrow ([mild] MIDB, a)–c))

An extra arrow `t : y ⟶ z` (not `α`) at the end of a dumb-bell in normal form:
* `midb_a`: it is the only extra arrow out of `y` (figure 4.1, first diagram);
* `midb_b`: there is no extra arrow into `x` (figure 4.1, second diagram);
* `midb_χ3`: `χ³ = 0` (figure 4.1, third diagram);
* `midb_α3_of`: `α³ = 0` if `α t ≠ 0` (figure 4.1, fourth diagram);
* `midb_d1`: `μ t ≠ 0` forces `α t = 0` (a `D̃₄` star).
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

/-- Nonzero morphisms out of `y` do not factor through `τ`. -/
lemma ftm_from_y {w : P} (f : y ⟶ w) (hf : f ≠ 0) : ¬FactorsThroughMorphism N.τ f := by
  rintro ⟨u, v, rfl⟩
  exact hf (by rw [N.hyx u, zero_comp])

/-- Nonzero morphisms into `x` do not factor through `τ`. -/
lemma ftm_to_x {w : P} (f : w ⟶ x) (hf : f ≠ 0) : ¬FactorsThroughMorphism N.τ f := by
  rintro ⟨u, v, rfl⟩
  exact hf (by rw [N.hyx v]; simp)

lemma rpow_χ_μ (n : ℕ) : rpow N.χ n ≫ N.μ = N.μ ≫ rpow N.α n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rpow_succ', Category.assoc, ih, ← Category.assoc, N.comm, Category.assoc,
      ← rpow_succ']

/-- `μ ≫ e` does not factor through `τ` for an arrow `e` out of `y`. -/
lemma ftm_μe (hL : LeftCancel P) {w : P} (e : y ⟶ w) (he : IsIrreducible e) (h0 : N.μ ≫ e ≠ 0) :
    ¬FactorsThroughMorphism N.τ (N.μ ≫ e) := by
  rintro ⟨u, v, huv⟩
  have key : ∀ n : ℕ, u = rpow N.χ n → False := by
    intro n hn
    have e' : N.μ ≫ e = N.μ ≫ (rpow N.α n ≫ N.α ≫ N.α ≫ v) := by
      rw [huv, hn]; simp only [DBN.τ, Category.assoc]
      rw [← Category.assoc (rpow N.χ n), N.rpow_χ_μ]; simp
    have he' := hL _ _ _ e' h0
    rcases he.2.2 _ (rpow N.α n ≫ N.α) (N.α ≫ v) (by rw [he']; simp) with h | h
    · exact N.hα.2.1 (ray_isIso_factors (rpow N.α n) N.α).2
    · exact N.hα.2.1 (ray_isIso_factors N.α v).1
  by_cases hu : IsIso u
  · obtain ⟨hh, hu1⟩ := RayQuiver.eq_id_of_isIso u
    exact key 0 (by simpa using hu1)
  · obtain ⟨n, -, hn⟩ := N.hρx u hu
    exact key n hn

/-- The arrows into `y` are `μ` and `α`. -/
lemma into_y (hM : MildHyp k P) {c : P} (e : c ⟶ y) (he : IsIrreducible e) :
    (∃ u, u ≫ N.μ = e) ∨ ∃ u, u ≫ N.α = e := by
  by_contra h
  push Not at h
  exact N.ldb hM e he (fun ⟨u, hu⟩ ↦ h.1 u hu) (fun ⟨u, hu⟩ ↦ h.2 u hu)

/-- Nonzero non-invertible morphisms into `y` end with `μ` or `α`. -/
lemma fact_y (hM : MildHyp k P) {c : P} (g : c ⟶ y) (hg0 : g ≠ 0) (hg : ¬IsIso g) :
    (∃ g', g = g' ≫ N.μ) ∨ ∃ g', g = g' ≫ N.α := by
  obtain ⟨d, p, e, hp⟩ := MildContour.exists_last_arrow g hg0 hg
  rcases N.into_y hM e.1 e.2 with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact Or.inl ⟨pathVal p ≫ u, by rw [hp, ← hu, Category.assoc]⟩
  · exact Or.inr ⟨pathVal p ≫ u, by rw [hp, ← hu, Category.assoc]⟩

/-- An extra arrow out of `y` does not divide `α` or `α²`. -/
lemma key_t (hM : MildHyp k P) {z : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) : (¬∃ g, t ≫ g = N.α) ∧ ¬∃ g, t ≫ g = N.α ≫ N.α := by
  have hR : RightCancel P := hM.right
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    rcases N.hα.2.2 _ t g hg.symm with h | h
    · exact ht.2.1 h
    · exact hta ⟨inv g, by rw [← hg]; simp⟩
  · rintro ⟨g, hg⟩
    have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ N.hτ (by rw [h, comp_zero])
    have hg0 : g ≠ 0 := fun h ↦ hαα (by rw [← hg, h, comp_zero])
    have hgn : ¬IsIso g := fun h ↦ by
      rcases ht.2.2 _ N.α (N.α ≫ inv g) (by rw [← Category.assoc, ← hg]; simp) with h' | h'
      · exact N.hα.2.1 h'
      · exact N.hα.2.1 (ray_isIso_factors N.α (inv g)).1
    rcases N.fact_y hM g hg0 hgn with ⟨g', rfl⟩ | ⟨g', rfl⟩
    · exact hαα (by rw [← hg, ← Category.assoc, N.hyx (t ≫ g'), zero_comp])
    · have e : (t ≫ g') ≫ N.α = N.α ≫ N.α := by rw [Category.assoc, hg]
      have e' := hR _ _ _ e (by rw [e]; exact hαα)
      rcases N.hα.2.2 _ t g' e'.symm with h | h
      · exact ht.2.1 h
      · exact hta ⟨inv g', by rw [← e']; simp⟩

/-- An extra arrow into `x` is not divided by `χ` or `χ²` (dual of `key_t`). -/
lemma key_ζ (hMo : MildHyp k Pᵒᵖ) {t : P} (ζ : t ⟶ x) (hζ : IsIrreducible ζ)
    (hζc : ¬∃ g, g ≫ N.χ = ζ) : (¬∃ g, g ≫ ζ = N.χ) ∧ ¬∃ g, g ≫ ζ = N.χ ≫ N.χ := by
  letI := isRayCategory_of_finiteRayCategory (C := Pᵒᵖ)
  letI : Fintype Pᵒᵖ := Fintype.ofFinite _
  letI : DecidableEq Pᵒᵖ := Classical.decEq _
  obtain ⟨h1, h2⟩ := N.op.key_t hMo ζ.op ((isIrreducible_op _).2 hζ) (neg_op_left hζc)
  refine ⟨fun ⟨g, hg⟩ ↦ h1 ⟨g.op, ?_⟩, fun ⟨g, hg⟩ ↦ h2 ⟨g.op, ?_⟩⟩
  · change ζ.op ≫ g.op = N.χ.op; rw [← op_comp, hg]
  · change ζ.op ≫ g.op = N.χ.op ≫ N.χ.op; rw [← op_comp, ← op_comp, hg]

/-- **[mild] MIDB a)**: at most one extra arrow out of `y`. -/
theorem midb_a (hM : MildHyp k P) {z z' : P} (t₁ : y ⟶ z) (t₂ : y ⟶ z')
    (h₁ : IsIrreducible t₁) (h₂ : IsIrreducible t₂) (ha₁ : ¬∃ g, N.α ≫ g = t₁)
    (ha₂ : ¬∃ g, N.α ≫ g = t₂) (h12 : ¬∃ g, t₁ ≫ g = t₂) (h21 : ¬∃ g, t₂ ≫ g = t₁) : False := by
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t₁ h₁ ha₁
  obtain ⟨k₂, k₂'⟩ := N.key_t hM t₂ h₂ ha₂
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  exact hM.not_mi41a N.τ N.τ_n hτ0 N.α N.α N.μ t₁ t₂
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ h₁.1) (N.ftm_from_y _ h₂.1)
    (N.ftm_from_y _ N.hα.1)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    hαn hαn hμn h₁.2.1 h₂.2.1 ha₁ ha₂ k₁ k₁' h12 k₂ k₂' h21 N.nαμ
    (fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp]))

/-- **[mild] MIDB b)**: with an extra arrow out of `y`, no extra arrow ends in `x`. -/
theorem midb_b (hM : MildHyp k P) (hMo : MildHyp k Pᵒᵖ) {z w : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) (ζ : w ⟶ x) (hζ : IsIrreducible ζ) (hζc : ¬∃ g, g ≫ N.χ = ζ) :
    False := by
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  have hχn := N.hχ.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  obtain ⟨z₁, z₂⟩ := N.key_ζ hMo ζ hζ hζc
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hχχ : N.χ ≫ N.χ ≠ 0 := fun h ↦ hτ0 (by
    rw [show N.μ ≫ N.α ≫ N.α = N.χ ≫ N.χ ≫ N.μ from N.τ_χχ.symm, ← Category.assoc, h, zero_comp])
  have y1 : ¬∃ g, N.μ ≫ g = N.χ := fun ⟨g, hg⟩ ↦ N.hχ.1 (by rw [← hg, N.hyx g, comp_zero])
  have y2 : ¬∃ g, N.μ ≫ g = N.χ ≫ N.χ := fun ⟨g, hg⟩ ↦ hχχ (by rw [← hg, N.hyx g, comp_zero])
  have y3 : ¬∃ g, g ≫ N.μ = N.α := fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])
  have y4 : ¬∃ g, g ≫ N.μ = N.α ≫ N.α := fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp])
  exact hM.not_mi41b N.τ N.τ_n hτ0 N.χ N.χ ζ N.μ N.μ N.α N.α t
    MI41B.not_isRepresentationFinite N.comm (N.ftm_to_x _ hζ.1) (N.ftm_to_x _ N.hχ.1)
    (N.ftm_to_x _ hχχ)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_to_x _ N.hχ.1) (nfp hτ0 N.χ N.μ N.α (Or.inl hχn) N.τ_χ)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1) (N.ftm_from_y _ N.hα.1)
    hχn hχn hζ.2.1 hμn hμn hαn hαn ht.2.1 N.nχμ y1 y2 N.nχμ y1 hta k₁ k₁' z₂ z₁ y3 hζc y4 y3
    N.nαμ N.nαμ

/-- **[mild] MIDB c), first part**: with an extra arrow out of `y`, `χ³ = 0`. -/
theorem midb_χ3 (hM : MildHyp k P) {z : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) : N.χ ≫ N.χ ≫ N.χ = 0 := by
  by_contra h3
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  have hχn := N.hχ.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  have hχχ : N.χ ≫ N.χ ≠ 0 := fun h ↦ h3 (by rw [← Category.assoc, h, zero_comp])
  have y1 : ¬∃ g, N.μ ≫ g = N.χ := fun ⟨g, hg⟩ ↦ N.hχ.1 (by rw [← hg, N.hyx g, comp_zero])
  have y2 : ¬∃ g, N.μ ≫ g = N.χ ≫ N.χ := fun ⟨g, hg⟩ ↦ hχχ (by rw [← hg, N.hyx g, comp_zero])
  have y2' : ¬∃ g, N.μ ≫ g = (N.χ ≫ N.χ) ≫ N.χ := fun ⟨g, hg⟩ ↦ h3 (by
    rw [← Category.assoc, ← hg, N.hyx g, comp_zero])
  have y3 : ¬∃ g, g ≫ N.μ = N.α := fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])
  have y4 : ¬∃ g, g ≫ N.μ = N.α ≫ N.α := fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp])
  exact hM.not_mi41c N.τ N.τ_n hτ0 N.χ N.χ N.χ N.μ N.μ N.α N.α t
    MI41C.not_isRepresentationFinite N.comm (N.ftm_to_x _ N.hχ.1) (N.ftm_to_x _ hχχ)
    (N.ftm_to_x _ (by simpa using h3))
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_to_x _ N.hχ.1) (N.ftm_to_x _ hχχ) (nfp hτ0 N.χ N.μ N.α (Or.inl hχn) N.τ_χ)
    (N.ftm_to_x _ N.hχ.1)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1) (N.ftm_from_y _ N.hα.1)
    hχn hχn hχn hμn hμn hαn hαn ht.2.1 N.nχμ y1 y2 y2' N.nχμ y1 y2 hta k₁ k₁' y3 y4 y3
    N.nαμ N.nαμ

/-- **[mild] MIDB c), second part, `α t ≠ 0`**: `α³ = 0` (figure 4.1, fourth diagram). -/
theorem midb_α3_of (hM : MildHyp k P) {z : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) (hαt : N.α ≫ t ≠ 0) : N.α ≫ N.α ≫ N.α = 0 := by
  by_contra h3
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  obtain ⟨k₁, k₁'⟩ := N.key_t hM t ht hta
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  exact hM.not_mi41d N.τ N.τ_n hτ0 N.α N.α N.α N.μ t
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ (by simpa using h3))
    (N.ftm_from_y _ hαt) (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ ht.1)
    (N.ftm_from_y _ N.hα.1)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    hαn hαn hαn hμn ht.2.1 hta k₁ k₁' N.nαμ
    (fun ⟨g, hg⟩ ↦ hαα (by rw [← hg, N.hyx g, zero_comp]))
    (fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp]))

/-- **[mild] MIDB d), first part**: `μ t ≠ 0` forces `α t = 0` (a `D̃₄` star). -/
theorem midb_d1 (hM : MildHyp k P) {z : P} (t : y ⟶ z) (ht : IsIrreducible t)
    (hta : ¬∃ g, N.α ≫ g = t) (hμt : N.μ ≫ t ≠ 0) : N.α ≫ t = 0 := by
  by_contra hαt
  have hτ0 := N.hτ
  have hμn := N.hμ.2.1
  have hαn := N.hα.2.1
  obtain ⟨k₁, -⟩ := N.key_t hM t ht hta
  have hαα : N.α ≫ N.α ≠ 0 := fun h ↦ hτ0 (by rw [h, comp_zero])
  exact hM.not_md4b N.τ N.τ_n hτ0 N.μ N.α N.α t (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ ht.1)
    (nfp hτ0 (𝟙 _) N.μ (N.α ≫ N.α) (Or.inr (not_isIso_comp_left' _ hαn)) (by simp))
    (nfp hτ0 (𝟙 _) (N.μ ≫ N.α) N.α (Or.inr hαn) (by simp))
    (N.ftm_μe hM.left t ht hμt)
    (N.ftm_from_y _ N.hα.1) (N.ftm_from_y _ hαα) (N.ftm_from_y _ hαt)
    hμn hαn hαn ht.2.1 hta k₁ (fun ⟨g, hg⟩ ↦ N.hα.1 (by rw [← hg, N.hyx g, zero_comp])) N.nαμ

end DBN

end RayCat

end LargeIndecomposable
