module

public import LargeIndecomposable.Crowns.Lemma7.Short
public import LargeIndecomposable.Cleaving.Shapes.ShapeF73
public import LargeIndecomposable.Cleaving.Shapes.ShapeF74
public import LargeIndecomposable.Cleaving.Shapes.ShapeF75

/-!
# BO13a Lemma 7: the core

* `RayCat.depth_add_le`, `RayCat.one_le_depth`, `RayCat.isIrreducible_of_depth`,
  `RayCat.depth_lt_of_le`: depth estimates.
* `MulBasis.no_crown_irr`: a crown of irreducible morphisms contradicts the
  existence of a long morphism.
* `MulBasis.l7_nice`: the contour of `σ` carrying `ρ` is `α e₁ e₂` with
  `ρ = α ≫ ρ'` and `ρ ∤ α e₁`.
* `MulBasis.l7_depth`: `depth σ ≤ 4`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- Depth is superadditive. -/
lemma depth_add_le {x y z : P} (f : x ⟶ y) (g : y ⟶ z) (h : f ≫ g ≠ 0) :
    depth f + depth g ≤ depth (f ≫ g) := by
  have hf : f ≠ 0 := fun h0 ↦ h (by rw [h0, zero_comp])
  have hg : g ≠ 0 := fun h0 ↦ h (by rw [h0, comp_zero])
  obtain ⟨p, hpl, hp⟩ := exists_path_depth hf
  obtain ⟨q, hql, hq⟩ := exists_path_depth hg
  have := length_le_depth' (p.comp q) (f := f ≫ g) (by rw [pathVal_comp, hp, hq]) h
  rw [Quiver.Path.length_comp] at this
  omega

lemma one_le_depth {x y : P} {f : x ⟶ y} (hf : f ≠ 0) (hi : ¬IsIso f) : 1 ≤ depth f := by
  obtain ⟨p, hpl, hp⟩ := exists_path_depth hf
  cases p with
  | nil => exact absurd (hp ▸ IsIso.id _) hi
  | cons p e => simp only [Quiver.Path.length_cons] at hpl; omega

/-- A nonzero non-invertible morphism of depth at most one is irreducible. -/
lemma isIrreducible_of_depth {x y : P} {f : x ⟶ y} (hf : f ≠ 0) (hi : ¬IsIso f)
    (hd : depth f ≤ 1) : IsIrreducible f := by
  refine ⟨hf, hi, fun Z g h hgh ↦ ?_⟩
  by_contra hc
  push Not at hc
  have h0 : g ≫ h ≠ 0 := by rw [← hgh]; exact hf
  have h1 := depth_add_le g h h0
  have h2 := one_le_depth (fun h0' ↦ h0 (by rw [h0', zero_comp])) hc.1
  have h3 := one_le_depth (fun h0' ↦ h0 (by rw [h0', comp_zero])) hc.2
  rw [← hgh] at h1
  omega

/-- A proper multiple `σ` of `ρ` with `ρ` not a prefix of `σ` has larger depth. -/
lemma depth_lt_of_le {x y y' : P} {σ : x ⟶ y} {ρ : x ⟶ y'} (hσ0 : σ ≠ 0)
    (hle : FactorsThroughMorphism ρ σ) (hv : ¬∃ c, ρ ≫ c = σ) : depth ρ < depth σ := by
  obtain ⟨c, d, hcd⟩ := hle
  by_cases hc : IsIso c
  · have hc1 : c = 𝟙 x := by
      obtain ⟨h, he⟩ := eq_eqToHom_of_isIso c
      rw [he]; rfl
    exact absurd ⟨d, by rw [hcd, hc1, Category.id_comp]⟩ hv
  · have h0 : c ≫ ρ ≫ d ≠ 0 := by rw [← hcd]; exact hσ0
    have h1 := depth_lt_comp_left c (ρ ≫ d) h0 hc
    have h2 := depth_le_comp_right ρ d (fun h' ↦ h0 (by rw [h', comp_zero]))
    rw [← hcd] at h1
    omega


omit [IsRayCategory P] in
lemma irr_comp_iso {x y z : P} {f : x ⟶ y} (hf : IsIrreducible f) (c : y ⟶ z) [IsIso c] :
    IsIrreducible (f ≫ c) := by
  refine ⟨fun h ↦ hf.1 (by
      rw [← Category.comp_id f, ← IsIso.hom_inv_id c, ← Category.assoc, h, zero_comp]),
    fun h ↦ hf.2.1 (by
      have e : f = (f ≫ c) ≫ inv c := by simp
      rw [e]; infer_instance),
    fun Z g h hgh ↦ ?_⟩
  rcases hf.2.2 _ g (h ≫ inv c) (by rw [← Category.assoc, ← hgh]; simp) with h1 | h1
  · exact Or.inl h1
  · right
    have e : h = (h ≫ inv c) ≫ c := by simp
    rw [e]; infer_instance

variable [IsFiniteRayCategory P]

omit [IsFiniteRayCategory P] in
lemma irr_eq_of_tsef {x y : P} {f g : x ⟶ y} (hf : IsIrreducible f) (hg : IsIrreducible g)
    (h : TwoSidedEndomorphismFactors f g) : f = g := by
  obtain ⟨a, b, hab⟩ := h
  have hab' : g = (show x ⟶ x from a) ≫ f ≫ (show y ⟶ y from b) := by
    rw [hab, Category.assoc]
  generalize (show x ⟶ x from a) = a' at hab'
  generalize (show y ⟶ y from b) = b' at hab'
  rcases hg.2.2 _ a' (f ≫ b') hab' with ha | hfb
  · obtain ⟨hx, ha'⟩ := eq_eqToHom_of_isIso a'
    have hab'' : g = f ≫ b' := by rw [hab', ha']; simp
    rcases hg.2.2 _ f b' hab'' with hf' | hb
    · exact absurd hf' hf.2.1
    · obtain ⟨hy, hb'⟩ := eq_eqToHom_of_isIso b'
      rw [hab'', hb']; simp
  · exact absurd ⟨b' ≫ inv (f ≫ b'), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
      (not_split_mono hf.2.1)

/-- **Parallel irreducible morphisms are equal.** -/
lemma irr_eq {x y : P} {f g : x ⟶ y} (hf : IsIrreducible f) (hg : IsIrreducible g) : f = g := by
  rcases IsFiniteRayCategory.factorization_comparable f g with h | h
  · exact irr_eq_of_tsef hf hg h
  · exact (irr_eq_of_tsef hg hf h).symm

omit [IsRayCategory P] [IsFiniteRayCategory P] in
lemma Crown.mk4_irr {a₀ a₁ b₀ b₁ : P} {f₀ : a₀ ⟶ b₀} {f₁ : a₁ ⟶ b₀} {f₂ : a₁ ⟶ b₁}
    {f₃ : a₀ ⟶ b₁} (h₀ : IsIrreducible f₀) (h₁ : IsIrreducible f₁) (h₂ : IsIrreducible f₂)
    (h₃ : IsIrreducible f₃) (t : ℕ) : IsIrreducible (Crown.mk4f f₀ f₁ f₂ f₃ t).2.2 := by
  rw [Crown.mk4f_mod]
  have : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases t % 4 <;> assumption

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- A crown of irreducible morphisms contradicts the existence of a long morphism. -/
theorem no_crown_irr
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (K : Crown P) (hirr : ∀ t, IsIrreducible (K.f t).2.2) {a b : P} (τ : a ⟶ b)
    (hτ : IsLong τ) : False := by
  obtain ⟨t, h | h⟩ := B.long_meets hmin K τ hτ
  · exact not_factorsThrough_irr hτ.2.1 hτ.1 hτ.2.2.1 (hirr (2 * t))
      (ftm_of_rayMor_eq (K.toZChain_ρ t) h)
  · exact not_factorsThrough_irr hτ.2.1 hτ.1 hτ.2.2.1 (hirr (2 * t + 1))
      (ftm_of_rayMor_eq (K.toZChain_σ t) h)

include B in
/-- **BO13a Lemma 7**: the contour of `σ` carrying `ρ` is `α e₁ e₂`, and `ρ` does not
factor through `α e₁`. -/
theorem l7_nice
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {x y₀ y₁ x₂ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ0 : ρ ≠ 0)
    (hρl : ¬IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (hle : FactorsThroughMorphism ρ σ) {μ : x₂ ⟶ y₁} (hμ : IsLong μ)
    (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ)
    (hne : (⟨x, y₀, σ⟩ : RayMor P) ≠ ⟨x₂, y₁, μ⟩)
    {c d : RayVert P} (α : RayVert.mk x ⟶ c) (β : RayVert.mk x ⟶ d)
    (v' : Quiver.Path c (RayVert.mk y₀)) (w' : Quiver.Path d (RayVert.mk y₀))
    (hv : pathVal (α.toPath.comp v') = σ) (hw : pathVal (β.toPath.comp w') = σ)
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w')) (hα : ∃ g, α.1 ≫ g = ρ) :
    w'.length ≤ 3 ∧ ∃ (b : RayVert P) (e₁ : c ⟶ b) (e₂ : b ⟶ RayVert.mk y₀),
      v' = (Quiver.Path.nil.cons e₁).cons e₂ ∧ ¬∃ g, (α.1 ≫ e₁.1) ≫ g = ρ := by
  obtain ⟨h2, h3⟩ := B.l7_short hmin hL hR hQ hcont hσ hρ0 hρl hv1 hv2 hle hμ hm1 hm2 hne α β v'
    w' hv hw hni hα
  refine ⟨h3, ?_⟩
  cases v' with
  | nil => simp at h2
  | cons v₁ e₂ =>
    cases v₁ with
    | nil => simp at h2
    | cons v₀ e₁ =>
      cases v₀ with
      | cons _ _ => simp at h2
      | nil =>
        refine ⟨_, e₁, e₂, rfl, ?_⟩
        rintro ⟨g, hg⟩
        obtain ⟨c', d', hcd⟩ := hle
        have hσ' : (α.1 ≫ e₁.1) ≫ e₂.1 = σ := by
          rw [← hv, pathVal_comp, pathVal_toPath]
          change _ = α.1 ≫ ((𝟙 _ ≫ e₁.1) ≫ e₂.1)
          simp
        obtain ⟨_, d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR hv2 (α.1 ≫ e₁.1) e₂.1 g hσ' hg c' d'
          hcd.symm hσ.1
        rcases e₂.2.2.2 _ d₁ d₂ hd.symm with h | h
        · exact hd₁ h
        · exact hd₂ h

include B in
/-- **BO13a Lemma 7**, `rad⁵ P = 0`: every path with value `σ` has length at most four. -/
theorem l7_depth
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {x y₀ y₁ x₂ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ0 : ρ ≠ 0)
    (hρl : ¬IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ) (hv2 : ¬∃ c, ρ ≫ c = σ)
    (hle : FactorsThroughMorphism ρ σ) {μ : x₂ ⟶ y₁} (hμ : IsLong μ)
    (hm1 : ¬∃ c, c ≫ μ = ρ) (hm2 : ¬∃ c, c ≫ ρ = μ)
    (hne : (⟨x, y₀, σ⟩ : RayMor P) ≠ ⟨x₂, y₁, μ⟩)
    (h5a : ∀ {c d : RayVert P} (α : RayVert.mk x ⟶ c) (β : RayVert.mk x ⟶ d)
      (v' : Quiver.Path c (RayVert.mk y₀)) (w' : Quiver.Path d (RayVert.mk y₀)),
      pathVal (α.toPath.comp v') = σ → pathVal (β.toPath.comp w') = σ →
      ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') →
      (∃ g, α.1 ≫ g = ρ) ∨ (∃ g, β.1 ≫ g = ρ)) :
    depth σ ≤ 4 := by
  have short2 : ∀ {c d : RayVert P} (α : RayVert.mk x ⟶ c) (β : RayVert.mk x ⟶ d)
      (v' : Quiver.Path c (RayVert.mk y₀)) (w' : Quiver.Path d (RayVert.mk y₀)),
      pathVal (α.toPath.comp v') = σ → pathVal (β.toPath.comp w') = σ →
      ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') →
      (α.toPath.comp v').length ≤ 4 ∧ (β.toPath.comp w').length ≤ 4 := by
    intro c d α β v' w' hv hw hni
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
    rcases h5a α β v' w' hv hw hni with h | h
    · obtain ⟨h2, h3⟩ := B.l7_short hmin hL hR hQ hcont hσ hρ0 hρl hv1 hv2 hle hμ hm1 hm2 hne α
        β v' w' hv hw hni h
      omega
    · obtain ⟨h2, h3⟩ := B.l7_short hmin hL hR hQ hcont hσ hρ0 hρl hv1 hv2 hle hμ hm1 hm2 hne β
        α w' v' hw hv (fun h' ↦ hni h'.symm) h
      omega
  obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hσ (hcont _ hσ)
  obtain ⟨u, hul, hu⟩ := exists_path_depth hσ.1
  obtain ⟨_, αu, u', rfl⟩ := exists_first_arrow u (by rw [hu]; exact hσ.2.1)
  rw [← hul]
  by_cases hi : Interlaced (αu.toPath.comp u') (α.toPath.comp v')
  · have hi' : ¬Interlaced (αu.toPath.comp u') (β.toPath.comp w') := fun h' ↦
      hni (Relation.EqvGen.trans _ _ _ hi.symm h')
    exact (short2 αu β u' w' hu hw hi').1
  · exact (short2 αu α u' v' hu hv hi).1

omit [IsRayCategory P] [Fintype P] [DecidableEq P] [IsFiniteRayCategory P] in
/-- A nonempty prefix of a path begins with the first arrow of the path. -/
lemma first_of_prefix {b : P} {z m c : RayVert P} (e : RayVert.mk b ⟶ c) (v : Quiver.Path c z)
    (u₁ : Quiver.Path (RayVert.mk b) m) (u₂ : Quiver.Path m z) (h : u₁.comp u₂ = e.toPath.comp v)
    (hu : 0 < u₁.length) : ∃ X, e.1 ≫ X = pathVal u₁ := by
  obtain ⟨α', hα'⟩ := exists_isFirst u₁ hu
  have h1 := hα'.comp u₂
  rw [h] at h1
  have h2 : IsFirst (e.toPath.comp v) (arrB e) := ⟨e, v, rfl, rfl⟩
  obtain rfl := h1.unique h2
  exact hα'.bLe

include B in
/-- **BO13a Lemma 7, permeable case** (figures 7.3, 7.4): the contour of `σ₂` is
permeable (`ρ₁` factors through the last arrow of `β₂ w₂`). -/
theorem l7_perm
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ y₀ y₁ : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ y₀}
    (hσ₁ : IsLong σ₁) (hσ₂ : IsLong σ₂) (hρ₁0 : ρ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0)
    (hρ₁l : ¬IsLong ρ₁) (hρ₂l : ¬IsLong ρ₂)
    (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁) (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂)
    (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hne : (⟨x, y₀, σ₁⟩ : RayMor P) ≠ ⟨x₂, y₁, σ₂⟩)
    {a b c : RayVert P} (α : RayVert.mk x ⟶ a) (e₁ : a ⟶ b) (e₂ : b ⟶ RayVert.mk y₀)
    (β : RayVert.mk x ⟶ c) (w : Quiver.Path c (RayVert.mk y₀))
    (hv : pathVal (α.toPath.comp ((Quiver.Path.nil.cons e₁).cons e₂)) = σ₁)
    (hw : pathVal (β.toPath.comp w) = σ₁)
    (hni : ¬Interlaced (α.toPath.comp ((Quiver.Path.nil.cons e₁).cons e₂)) (β.toPath.comp w))
    (ρ₁' : a.out ⟶ y₁) (hρ₁' : α.1 ≫ ρ₁' = ρ₁) (hmx1 : ¬∃ g, (α.1 ≫ e₁.1) ≫ g = ρ₁)
    (hβρ₁ : ¬∃ g, β.1 ≫ g = ρ₁)
    {a₂ b₂ c₂ : RayVert P} (α₂ : RayVert.mk x₂ ⟶ a₂) (f₁ : a₂ ⟶ b₂) (f₂ : b₂ ⟶ RayVert.mk y₁)
    (β₂ : RayVert.mk x₂ ⟶ c₂) (w₂ : Quiver.Path c₂ (RayVert.mk y₁))
    (hv₂ : pathVal (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) = σ₂)
    (hw₂ : pathVal (β₂.toPath.comp w₂) = σ₂)
    (hni₂ : ¬Interlaced (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) (β₂.toPath.comp w₂))
    (ρ₂' : a₂.out ⟶ y₀) (hρ₂' : α₂.1 ≫ ρ₂' = ρ₂) (hmx2 : ¬∃ g, (α₂.1 ≫ f₁.1) ≫ g = ρ₂)
    (hβρ₂ : ¬∃ g, β₂.1 ≫ g = ρ₂)
    {d₂ : RayVert P} (q : Quiver.Path (RayVert.mk x₂) d₂) (ω : d₂ ⟶ RayVert.mk y₁)
    (hq : β₂.toPath.comp w₂ = q.cons ω) (hω : ∃ g, g ≫ ω.1 = ρ₁)
    (hD44 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F73.thin) k)) : False := by
  have hσ₁0 := hσ₁.1
  have hσ₂0 := hσ₂.1
  have hσ₁v : α.1 ≫ e₁.1 ≫ e₂.1 = σ₁ := by
    rw [← hv, pathVal_comp, pathVal_toPath]
    change _ = α.1 ≫ ((𝟙 _ ≫ e₁.1) ≫ e₂.1)
    simp
  have hσ₁w : β.1 ≫ pathVal w = σ₁ := by rw [← hw, pathVal_comp, pathVal_toPath]
  have hσ₂v : α₂.1 ≫ f₁.1 ≫ f₂.1 = σ₂ := by
    rw [← hv₂, pathVal_comp, pathVal_toPath]
    change _ = α₂.1 ≫ ((𝟙 _ ≫ f₁.1) ≫ f₂.1)
    simp
  have hir₁' : ¬IsIso ρ₁' := fun h ↦ hv2 ⟨inv ρ₁' ≫ e₁.1 ≫ e₂.1, by
    rw [← hρ₁', Category.assoc, IsIso.hom_inv_id_assoc, hσ₁v]⟩
  have hir₂' : ¬IsIso ρ₂' := fun h ↦ hw2 ⟨inv ρ₂' ≫ f₁.1 ≫ f₂.1, by
    rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂v]⟩
  have hw0 : 0 < w.length := by
    by_contra h0
    have hl : w.length = 0 := by omega
    cases w with
    | cons _ _ => simp at hl
    | nil =>
      apply hσ₁.2.2.1
      rw [← hσ₁w]
      exact (Category.comp_id β.1).symm ▸ β.2
  -- `σ₂` does not divide segments of `σ₁`, `ρ₁`, `ρ₂`; `σ₁` none of `σ₂`, `ρ₁`, `ρ₂`
  have seg : ∀ {a' b' X' Y' : P} {τ : a' ⟶ b'} {f : X' ⟶ Y'}, ¬FactorsThroughMorphism τ f →
      ∀ {X Y : P} (L : X' ⟶ X) (s : X ⟶ Y) (R : Y ⟶ Y'), L ≫ s ≫ R = f →
        ¬FactorsThroughMorphism τ s := by
    intro a' b' X' Y' τ f hf X Y L s R hs h
    exact hf (by
      rw [← hs]; exact FactorsThroughMorphism.comp_left (FactorsThroughMorphism.comp_right h R) L)
  have n21 : ¬FactorsThroughMorphism σ₂ σ₁ := not_ftm_of_ne hσ₂ hσ₁0 hne
  have n12 : ¬FactorsThroughMorphism σ₁ σ₂ := not_ftm_of_ne hσ₁ hσ₂0 (fun h ↦ hne h.symm)
  have n2ρ₁ : ¬FactorsThroughMorphism σ₂ ρ₁ := not_factorsThrough_of_not_isLong hσ₂ hρ₁0 hρ₁l
  have n2ρ₂ : ¬FactorsThroughMorphism σ₂ ρ₂ := not_factorsThrough_of_not_isLong hσ₂ hρ₂0 hρ₂l
  have n1ρ₁ : ¬FactorsThroughMorphism σ₁ ρ₁ := not_factorsThrough_of_not_isLong hσ₁ hρ₁0 hρ₁l
  have n1ρ₂ : ¬FactorsThroughMorphism σ₁ ρ₂ := not_factorsThrough_of_not_isLong hσ₁ hρ₂0 hρ₂l
  -- crossings in the contour of `σ₁`
  have hval₁ : pathVal (α.toPath.comp ((Quiver.Path.nil.cons e₁).cons e₂)) =
      pathVal (β.toPath.comp w) := by rw [hv, hw]
  have h0₁ : pathVal (α.toPath.comp ((Quiver.Path.nil.cons e₁).cons e₂)) ≠ 0 := by
    rw [hv]; exact hσ₁0
  have hαβ : ¬∃ g, α.1 ≫ g = β.1 := by
    have := prefix_cross hL hR _ _ hval₁ h0₁ hni α.toPath _ β.toPath w rfl rfl (by simp) hw0
    simpa only [pathVal_toPath] using this
  have hβα : ¬∃ g, β.1 ≫ g = α.1 := by
    have := prefix_cross hL hR _ _ hval₁.symm (by rw [← hval₁]; exact h0₁) (fun h ↦ hni h.symm)
      β.toPath w α.toPath ((Quiver.Path.nil.cons e₁).cons e₂) rfl rfl (by simp) (by simp)
    simpa only [pathVal_toPath] using this
  -- the longest suffix of `β₂ w₂` through which `ρ₁` factors
  obtain ⟨_, _, p₁, e, p₂, hsplit, hp₂, ⟨γ, hγ⟩, hmxs⟩ := exists_max_suffix
    (x := RayVert.mk x₂) (y := RayVert.mk y₁) ρ₁ q ω.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hω; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩)
    (by
      rintro ⟨g, hg⟩
      refine hp1 ⟨g, ?_⟩
      rw [← hg, ← hw₂, hq]
      rfl)
  have hpath : (p₁.cons e).comp p₂ = β₂.toPath.comp w₂ := by rw [hsplit, hq]; rfl
  obtain ⟨_, p₂', e'', rfl⟩ := exists_last_arrow p₂ (not_isIso_pathVal p₂ hp₂)
  have hpath' : ((p₁.cons e).comp p₂').cons e'' = β₂.toPath.comp w₂ := hpath
  have hρ₁e : ∃ g, g ≫ e''.1 = ρ₁ := ⟨γ ≫ pathVal p₂', by rw [Category.assoc]; exact hγ⟩
  have hval₂ : pathVal (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) =
      pathVal (((p₁.cons e).comp p₂').cons e'') := by rw [hpath', hv₂, hw₂]
  have h0₂ : pathVal (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) ≠ 0 := by
    rw [hv₂]; exact hσ₂0
  have hni₂' : ¬Interlaced (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂))
      (((p₁.cons e).comp p₂').cons e'') := by rw [hpath']; exact hni₂
  -- Lemma 4 b), dual: `ρ₁` does not factor through `f₂`
  have hρ₁f₂ : ¬∃ g, g ≫ f₂.1 = ρ₁ := fun hf ↦ B.not_factors_both_last hmin hL hR f₂ e''
    (α₂.toPath.comp (Quiver.Path.nil.cons f₁)) ((p₁.cons e).comp p₂') hval₂ h0₂ hni₂' ρ₁ hρ₁0
    (fun ⟨c', hc⟩ ↦ hp1 ⟨c', by rw [← hc]; exact congrArg (c' ≫ ·) hv₂.symm⟩)
    (fun ⟨c', hc⟩ ↦ hp2 ⟨c', by rw [hc]; exact hv₂⟩) hf hρ₁e
  have hrf₁ : ¬∃ g, ρ₂' ≫ g = f₁.1 := by
    rintro ⟨g, hg⟩
    rcases f₁.2.2.2 _ ρ₂' g hg.symm with h | h
    · exact hir₂' h
    · exact hmx2 ⟨inv g, by
        rw [Category.assoc, ← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hρ₂']⟩
  have hf₁r : ¬∃ g, f₁.1 ≫ g = ρ₂' := fun ⟨g, hg⟩ ↦ hmx2 ⟨g, by
    rw [Category.assoc, hg, hρ₂']⟩
  by_cases h6a : ∃ g, g ≫ e''.1 = ρ₁'
  · -- figure 7.3 (category 44) in `P/σ₂`
    obtain ⟨h, hh⟩ := h6a
    have hiα₂f₁ : ¬IsIso (α₂.1 ≫ f₁.1) := fun hi ↦ not_split_mono α₂.2.2.1
      ⟨f₁.1 ≫ inv (α₂.1 ≫ f₁.1), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
    have crs := contour_cross hL hR α₂.toPath ((Quiver.Path.nil.cons f₁).cons f₂)
      ((p₁.cons e).comp p₂') e''.toPath hval₂ h0₂ hni₂' (by simp) (by simp)
    have hcrv := contour_cross hL hR α.toPath ((Quiver.Path.nil.cons e₁).cons e₂) β.toPath w
      hval₁ h0₁ hni (by simp) hw0
    have hcrv' := contour_cross hL hR (α.toPath.comp (Quiver.Path.nil.cons e₁))
      (Quiver.Path.nil.cons e₂) β.toPath w hval₁ h0₁ hni (by simp) hw0
    have hcrw := contour_cross hL hR β.toPath w (α.toPath.comp (Quiver.Path.nil.cons e₁))
      (Quiver.Path.nil.cons e₂) hval₁.symm (by rw [← hval₁]; exact h0₁)
      (fun h' ↦ hni h'.symm) (by simp) (by simp)
    refine B.not_f73 hmin hL hR σ₂ hσ₂.2.1 hσ₂0 β.1 (pathVal w) α.1 e₁.1 e₂.1 ρ₁' f₂.1 f₁.1 ρ₂'
      hD44 (hσ₁v.trans hσ₁w.symm)
      (seg n21 α.1 e₁.1 e₂.1 hσ₁v) (seg n21 α.1 (e₁.1 ≫ e₂.1) (𝟙 _) (by simpa using hσ₁v))
      (seg n2ρ₁ α.1 ρ₁' (𝟙 _) (by simpa using hρ₁'))
      (not_ftm_mid hσ₂0 α₂.2.2.1 hσ₂v) (seg n2ρ₂ α₂.1 ρ₂' (𝟙 _) (by simpa using hρ₂'))
      (not_ftm_suffix hσ₂0 α₂.2.2.1 hσ₂v)
      (seg n21 (α.1 ≫ e₁.1) e₂.1 (𝟙 _) (by simpa using hσ₁v))
      (not_ftm_suffix hσ₂0 hiα₂f₁ (by rw [Category.assoc]; exact hσ₂v))
      (seg n21 β.1 (pathVal w) (𝟙 _) (by simpa using hσ₁w))
      (seg n21 (𝟙 _) α.1 (e₁.1 ≫ e₂.1) (by simpa using hσ₁v))
      (seg n21 (𝟙 _) (α.1 ≫ e₁.1) e₂.1 (by simpa using hσ₁v))
      (seg n21 (𝟙 _) β.1 (pathVal w) (by simpa using hσ₁w))
      (seg n21 (𝟙 _) (β.1 ≫ pathVal w) (𝟙 _) (by simpa using hσ₁w))
      (seg n2ρ₁ (𝟙 _) (α.1 ≫ ρ₁') (𝟙 _) (by simpa using hρ₁'))
      β.2.2.1 (not_isIso_pathVal w hw0) α.2.2.1 e₁.2.2.1 e₂.2.2.1 hir₁' f₂.2.2.1 f₁.2.2.1 hir₂'
      (fun ⟨g, hg⟩ ↦ hmx1 ⟨g, by rw [Category.assoc, hg, hρ₁']⟩)
      (fun ⟨g, hg⟩ ↦ hv2 ⟨g, by rw [← hρ₁', Category.assoc, hg, hσ₁v]⟩) ?_ hf₁r
      (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂v]⟩) hrf₁ hαβ hβα ?_
      (fun ⟨g, hg⟩ ↦ hβρ₁ ⟨g, by rw [hg, hρ₁']⟩) ?_ ?_ ?_
      (fun ⟨g, hg⟩ ↦ hρ₁f₂ ⟨g, by rw [hg, hρ₁']⟩)
      (fun ⟨g, hg⟩ ↦ hρ₁f₂ ⟨α.1 ≫ g, by rw [Category.assoc, hg, hρ₁']⟩) ?_ ?_
    · rintro ⟨g, hg⟩
      rcases e₁.2.2.2 _ ρ₁' g hg.symm with h' | h'
      · exact hir₁' h'
      · exact hmx1 ⟨inv g, by
          rw [Category.assoc, ← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hρ₁']⟩
    · rintro ⟨g, hg⟩
      refine hcrw.2 ⟨g, ?_⟩
      rw [pathVal_toPath, hg, pathVal_comp, pathVal_toPath]
      change _ = α.1 ≫ (𝟙 _ ≫ e₁.1)
      rw [Category.id_comp]
    · rintro ⟨g, hg⟩
      rcases f₂.2.2.2 _ g ρ₁' hg.symm with h' | h'
      · exact hρ₁f₂ ⟨α.1 ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, hρ₁']⟩
      · exact hir₁' h'
    · rintro ⟨g, hg⟩
      refine crs.1 ⟨g ≫ h, ?_⟩
      rw [pathVal_toPath, Category.assoc, hh, hg]
      change _ = (𝟙 _ ≫ f₁.1) ≫ f₂.1
      rw [Category.id_comp]
    · rintro ⟨g, hg⟩
      refine hcrw.1 ⟨g, ?_⟩
      change g ≫ (𝟙 _ ≫ e₂.1) = _
      rw [Category.id_comp, hg]
    · rintro ⟨g, hg⟩
      refine hcrv.1 ⟨g, ?_⟩
      rw [hg]
      change _ = (𝟙 _ ≫ e₁.1) ≫ e₂.1
      rw [Category.id_comp]
    · rintro ⟨g, hg⟩
      refine hcrv'.1 ⟨g, ?_⟩
      rw [hg]
      change _ = 𝟙 _ ≫ e₂.1
      rw [Category.id_comp]
  · -- figure 7.4 (`D̃₇`) in `P/σ₁`
    have hσ₂W : pathVal (p₁.cons e) ≫ pathVal (p₂'.cons e'') = σ₂ := by
      rw [← pathVal_comp, hpath, hw₂]
    have hiγ : ¬IsIso γ := fun h ↦ hp2 ⟨pathVal (p₁.cons e) ≫ inv γ, by
      rw [← hγ, Category.assoc, IsIso.inv_hom_id_assoc, hσ₂W]⟩
    have hval₂' : pathVal (β₂.toPath.comp w₂) =
        pathVal (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) := by rw [hv₂, hw₂]
    have h0₂' : pathVal (β₂.toPath.comp w₂) ≠ 0 := by rw [hw₂]; exact hσ₂0
    have hni₂s : ¬Interlaced (β₂.toPath.comp w₂)
        (α₂.toPath.comp ((Quiver.Path.nil.cons f₁).cons f₂)) := fun h' ↦ hni₂ h'.symm
    obtain ⟨X, hX⟩ := first_of_prefix β₂ w₂ (p₁.cons e) (p₂'.cons e'') hpath (by simp)
    refine B.not_f74 hmin hL hR σ₁ hσ₁.2.1 hσ₁0 β.1 α.1 γ (pathVal (p₁.cons e)) α₂.1 f₁.1 ρ₂'
      (not_ftm_prefix hσ₁0 (not_isIso_pathVal w hw0) hσ₁w)
      (not_ftm_prefix hσ₁0 (fun hi ↦ not_split_mono e₁.2.2.1
        ⟨e₂.1 ≫ inv (e₁.1 ≫ e₂.1), by rw [← Category.assoc, IsIso.hom_inv_id]⟩) hσ₁v)
      (seg n1ρ₁ (𝟙 _) γ (pathVal (p₂'.cons e'')) (by simpa using hγ))
      (seg n12 (𝟙 _) (pathVal (p₁.cons e)) (pathVal (p₂'.cons e'')) (by simpa using hσ₂W))
      (seg n12 (𝟙 _) α₂.1 (f₁.1 ≫ f₂.1) (by simpa using hσ₂v))
      (seg n12 (𝟙 _) (α₂.1 ≫ f₁.1) f₂.1 (by simpa using hσ₂v))
      (seg n1ρ₂ (𝟙 _) (α₂.1 ≫ ρ₂') (𝟙 _) (by simpa using hρ₂'))
      (seg n12 α₂.1 f₁.1 f₂.1 hσ₂v) (seg n1ρ₂ α₂.1 ρ₂' (𝟙 _) (by simpa using hρ₂'))
      β.2.2.1 α.2.2.1 hiγ (not_isIso_pathVal _ (by simp)) α₂.2.2.1 f₁.2.2.1 hir₂' hβα
      (fun ⟨g, hg⟩ ↦ hβρ₁ ⟨g ≫ pathVal (p₂'.cons e''), by rw [← Category.assoc, hg, hγ]⟩)
      hαβ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf₁r hrf₁
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hγ, ← Category.assoc, hg, hσ₂W]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hγ, ← hg, Category.assoc, hσ₂W]⟩)
    · -- `α ≫ g = γ` makes `ρ₁'` factor through `e''`
      rintro ⟨g, hg⟩
      have heq : α.1 ≫ ((g ≫ pathVal p₂') ≫ e''.1) = α.1 ≫ ρ₁' := by
        rw [hρ₁', ← hγ, ← hg]
        simp only [Category.assoc]
        rfl
      exact h6a ⟨g ≫ pathVal p₂', hL α.1 _ _ heq (by rw [heq, hρ₁']; exact hρ₁0)⟩
    · rintro ⟨g, hg⟩
      rcases β.2.2.2 _ γ g hg.symm with h | h
      · exact hiγ h
      · exact hβρ₁ ⟨inv g ≫ pathVal (p₂'.cons e''), by
          rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hγ]⟩
    · rintro ⟨g, hg⟩
      rcases α.2.2.2 _ γ g hg.symm with h | h
      · exact hiγ h
      · have heq : α.1 ≫ ((inv g ≫ pathVal p₂') ≫ e''.1) = α.1 ≫ ρ₁' := by
          rw [hρ₁', ← hγ, ← hg]
          simp only [Category.assoc, IsIso.hom_inv_id_assoc]
          rfl
        exact h6a ⟨inv g ≫ pathVal p₂', hL α.1 _ _ heq (by rw [heq, hρ₁']; exact hρ₁0)⟩
    · have := prefix_cross hL hR _ _ hval₂' h0₂' hni₂s (p₁.cons e) (p₂'.cons e'') α₂.toPath
        ((Quiver.Path.nil.cons f₁).cons f₂) hpath rfl (by simp) (by simp)
      simpa only [pathVal_toPath] using this
    · have := prefix_cross hL hR _ _ hval₂' h0₂' hni₂s (p₁.cons e) (p₂'.cons e'')
        (α₂.toPath.comp (Quiver.Path.nil.cons f₁)) (Quiver.Path.nil.cons f₂) hpath rfl (by simp)
        (by simp)
      rintro ⟨g, hg⟩
      refine this ⟨g, ?_⟩
      rw [hg, pathVal_comp, pathVal_toPath]
      change _ = α₂.1 ≫ (𝟙 _ ≫ f₁.1)
      rw [Category.id_comp]
    · rintro ⟨g, hg⟩
      exact hβρ₂ ⟨X ≫ g, by rw [← Category.assoc, hX, hg, hρ₂']⟩
    · have := prefix_cross hL hR _ _ hval₂'.symm (by rw [← hval₂']; exact h0₂')
        (fun h' ↦ hni₂s h'.symm) α₂.toPath ((Quiver.Path.nil.cons f₁).cons f₂) (p₁.cons e)
        (p₂'.cons e'') rfl hpath (by simp) (by simp)
      simpa only [pathVal_toPath] using this

include B in
/-- **BO13a Lemma 7, reflecting case, the `D̃₅`** in `P/σ₁`: if `ρ₁ = φ ≫ f₂` does not
factor through `f₁ ≫ f₂`. -/
theorem l7_f75
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ y₀ y₁ : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ y₀}
    (hσ₁ : IsLong σ₁) (hρ₁0 : ρ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0) (hρ₁l : ¬IsLong ρ₁) (hρ₂l : ¬IsLong ρ₂)
    (hσ₂0 : σ₂ ≠ 0) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (hne : (⟨x₂, y₁, σ₂⟩ : RayMor P) ≠ ⟨x, y₀, σ₁⟩)
    {a₂ b₂ : RayVert P} (α₂ : RayVert.mk x₂ ⟶ a₂) (f₁ : a₂ ⟶ b₂) (f₂ : b₂ ⟶ RayVert.mk y₁)
    (hσ₂v : α₂.1 ≫ f₁.1 ≫ f₂.1 = σ₂) (ρ₂' : a₂.out ⟶ y₀) (hρ₂' : α₂.1 ≫ ρ₂' = ρ₂)
    (hmx2 : ¬∃ g, (α₂.1 ≫ f₁.1) ≫ g = ρ₂) (φ : x ⟶ b₂.out) (hφ : φ ≫ f₂.1 = ρ₁)
    (hnot : ¬∃ g, g ≫ f₁.1 ≫ f₂.1 = ρ₁) : False := by
  have hσ₁0 := hσ₁.1
  have seg : ∀ {a' b' X' Y' : P} {τ : a' ⟶ b'} {f : X' ⟶ Y'}, ¬FactorsThroughMorphism τ f →
      ∀ {X Y : P} (L : X' ⟶ X) (s : X ⟶ Y) (R : Y ⟶ Y'), L ≫ s ≫ R = f →
        ¬FactorsThroughMorphism τ s := by
    intro a' b' X' Y' τ f hf X Y L s R hs h
    exact hf (by
      rw [← hs]; exact FactorsThroughMorphism.comp_left (FactorsThroughMorphism.comp_right h R) L)
  have n12 : ¬FactorsThroughMorphism σ₁ σ₂ := not_ftm_of_ne hσ₁ hσ₂0 hne
  have n1ρ₁ : ¬FactorsThroughMorphism σ₁ ρ₁ := not_factorsThrough_of_not_isLong hσ₁ hρ₁0 hρ₁l
  have n1ρ₂ : ¬FactorsThroughMorphism σ₁ ρ₂ := not_factorsThrough_of_not_isLong hσ₁ hρ₂0 hρ₂l
  have hir₂' : ¬IsIso ρ₂' := fun h ↦ hw2 ⟨inv ρ₂' ≫ f₁.1 ≫ f₂.1, by
    rw [← hρ₂', Category.assoc, IsIso.hom_inv_id_assoc, hσ₂v]⟩
  have hiφ : ¬IsIso φ := fun h ↦ hp2 ⟨α₂.1 ≫ f₁.1 ≫ inv φ, by
    rw [← hφ]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]; exact hσ₂v⟩
  refine B.not_f75 hmin hL hR σ₁ hσ₁.2.1 hσ₁0 α₂.1 f₁.1 ρ₂' f₂.1 φ
    (seg n12 α₂.1 f₁.1 f₂.1 hσ₂v) (seg n12 α₂.1 (f₁.1 ≫ f₂.1) (𝟙 _) (by simpa using hσ₂v))
    (seg n1ρ₂ α₂.1 ρ₂' (𝟙 _) (by simpa using hρ₂'))
    (seg n12 (𝟙 _) α₂.1 (f₁.1 ≫ f₂.1) (by simpa using hσ₂v))
    (seg n12 (𝟙 _) (α₂.1 ≫ f₁.1) f₂.1 (by simpa using hσ₂v))
    (seg n12 (𝟙 _) ((α₂.1 ≫ f₁.1) ≫ f₂.1) (𝟙 _) (by simpa using hσ₂v))
    (seg n1ρ₂ (𝟙 _) (α₂.1 ≫ ρ₂') (𝟙 _) (by simpa using hρ₂'))
    (seg n12 (α₂.1 ≫ f₁.1) f₂.1 (𝟙 _) (by simpa using hσ₂v))
    (seg n1ρ₁ (𝟙 _) φ f₂.1 (by simpa using hφ))
    (seg n1ρ₁ (𝟙 _) (φ ≫ f₂.1) (𝟙 _) (by simpa using hφ))
    α₂.2.2.1 f₁.2.2.1 hir₂' f₂.2.2.1 hiφ
    (fun ⟨g, hg⟩ ↦ hmx2 ⟨g, by rw [Category.assoc, hg, hρ₂']⟩) ?_
    (fun ⟨g, hg⟩ ↦ hw2 ⟨g, by rw [← hρ₂', Category.assoc, hg, hσ₂v]⟩)
    (fun ⟨g, hg⟩ ↦ hnot ⟨g, by rw [← Category.assoc, hg, hφ]⟩) ?_
    (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hφ, ← Category.assoc, hg, Category.assoc, hσ₂v]⟩)
  · rintro ⟨g, hg⟩
    rcases f₁.2.2.2 _ ρ₂' g hg.symm with h | h
    · exact hir₂' h
    · exact hmx2 ⟨inv g, by
        rw [Category.assoc, ← hg, Category.assoc, IsIso.hom_inv_id, Category.comp_id, hρ₂']⟩
  · rintro ⟨g, hg⟩
    rcases f₁.2.2.2 _ g φ hg.symm with h | h
    · exact hnot ⟨inv g, by rw [← hφ, ← hg]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]⟩
    · exact hiφ h

include B in
/-- **BO13a Lemma 7, reflecting case**: both contours reflecting. -/
theorem l7_refl
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P)
    {x x₂ y₀ y₁ : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ y₀}
    (hσ₁ : IsLong σ₁) (hσ₂ : IsLong σ₂) (hρ₁0 : ρ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0)
    (hρ₁l : ¬IsLong ρ₁) (hρ₂l : ¬IsLong ρ₂)
    (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁) (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂)
    (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂) (hq1 : ¬∃ c, c ≫ σ₁ = ρ₂) (hq2 : ¬∃ c, c ≫ ρ₂ = σ₁)
    (hle1 : FactorsThroughMorphism ρ₁ σ₁) (hle2 : FactorsThroughMorphism ρ₂ σ₂)
    (hne : (⟨x, y₀, σ₁⟩ : RayMor P) ≠ ⟨x₂, y₁, σ₂⟩)
    {a b : RayVert P} (α : RayVert.mk x ⟶ a) (e₁ : a ⟶ b) (e₂ : b ⟶ RayVert.mk y₀)
    (hσ₁v : α.1 ≫ e₁.1 ≫ e₂.1 = σ₁) (ρ₁' : a.out ⟶ y₁) (hρ₁' : α.1 ≫ ρ₁' = ρ₁)
    (hmx1 : ¬∃ g, (α.1 ≫ e₁.1) ≫ g = ρ₁)
    {a₂ b₂ : RayVert P} (α₂ : RayVert.mk x₂ ⟶ a₂) (f₁ : a₂ ⟶ b₂) (f₂ : b₂ ⟶ RayVert.mk y₁)
    (hσ₂v : α₂.1 ≫ f₁.1 ≫ f₂.1 = σ₂) (ρ₂' : a₂.out ⟶ y₀) (hρ₂' : α₂.1 ≫ ρ₂' = ρ₂)
    (hmx2 : ¬∃ g, (α₂.1 ≫ f₁.1) ≫ g = ρ₂)
    (hd₁ : depth σ₁ ≤ 4) (hd₂ : depth σ₂ ≤ 4)
    (hr₁ : ∃ g, g ≫ e₂.1 = ρ₂) (hr₂ : ∃ g, g ≫ f₂.1 = ρ₁) : False := by
  have hσ₁0 := hσ₁.1
  have hσ₂0 := hσ₂.1
  have seg : ∀ {a' b' X' Y' : P} {τ : a' ⟶ b'} {f : X' ⟶ Y'}, ¬FactorsThroughMorphism τ f →
      ∀ {X Y : P} (L : X' ⟶ X) (s : X ⟶ Y) (R : Y ⟶ Y'), L ≫ s ≫ R = f →
        ¬FactorsThroughMorphism τ s := by
    intro a' b' X' Y' τ f hf X Y L s R hs h
    exact hf (by
      rw [← hs]; exact FactorsThroughMorphism.comp_left (FactorsThroughMorphism.comp_right h R) L)
  have n12 : ¬FactorsThroughMorphism σ₁ σ₂ := not_ftm_of_ne hσ₁ hσ₂0 (fun h ↦ hne h.symm)
  have n1ρ₁ : ¬FactorsThroughMorphism σ₁ ρ₁ := not_factorsThrough_of_not_isLong hσ₁ hρ₁0 hρ₁l
  have n1ρ₂ : ¬FactorsThroughMorphism σ₁ ρ₂ := not_factorsThrough_of_not_isLong hσ₁ hρ₂0 hρ₂l
  -- `ρ₁` factors through `f₁ ≫ f₂`, `ρ₂` through `e₁ ≫ e₂` (else a `D̃₅`)
  by_cases hA : ∃ g, g ≫ f₁.1 ≫ f₂.1 = ρ₁
  swap
  · obtain ⟨φ, hφ⟩ := hr₂
    exact B.l7_f75 hmin hL hR hσ₁ hρ₁0 hρ₂0 hρ₁l hρ₂l hσ₂0 hp2 hw2 (fun h ↦ hne h.symm) α₂ f₁ f₂
      hσ₂v ρ₂' hρ₂' hmx2 φ hφ hA
  by_cases hB : ∃ g, g ≫ e₁.1 ≫ e₂.1 = ρ₂
  swap
  · obtain ⟨φ, hφ⟩ := hr₁
    exact B.l7_f75 hmin hL hR hσ₂ hρ₂0 hρ₁0 hρ₂l hρ₁l hσ₁0 hq2 hv2 hne α e₁ e₂ hσ₁v ρ₁' hρ₁'
      hmx1 φ hφ hB
  obtain ⟨t₁, hr1⟩ := hA
  obtain ⟨t₂, hr2⟩ := hB
  -- `t₁`, `t₂` are arrows (`rad⁵ P = 0`)
  have hit₁ : ¬IsIso t₁ := fun h ↦ hp2 ⟨α₂.1 ≫ inv t₁, by
    rw [← hr1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]; exact hσ₂v⟩
  have hit₂ : ¬IsIso t₂ := fun h ↦ hq2 ⟨α.1 ≫ inv t₂, by
    rw [← hr2]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]; exact hσ₁v⟩
  have hirr₁ : IsIrreducible t₁ := by
    refine isIrreducible_of_depth (fun h ↦ hρ₁0 (by rw [← hr1, h, zero_comp])) hit₁ ?_
    have d1 := depth_lt_of_le hσ₁0 hle1 hv2
    have d2 := depth_add_le t₁ (f₁.1 ≫ f₂.1) (by rw [hr1]; exact hρ₁0)
    have d3 := depth_add_le f₁.1 f₂.1 (fun h ↦ hρ₁0 (by rw [← hr1, h, comp_zero]))
    have d4 := one_le_depth f₁.2.1 f₁.2.2.1
    have d5 := one_le_depth f₂.2.1 f₂.2.2.1
    rw [hr1] at d2
    omega
  have hirr₂ : IsIrreducible t₂ := by
    refine isIrreducible_of_depth (fun h ↦ hρ₂0 (by rw [← hr2, h, zero_comp])) hit₂ ?_
    have d1 := depth_lt_of_le hσ₂0 hle2 hw2
    have d2 := depth_add_le t₂ (e₁.1 ≫ e₂.1) (by rw [hr2]; exact hρ₂0)
    have d3 := depth_add_le e₁.1 e₂.1 (fun h ↦ hρ₂0 (by rw [← hr2, h, comp_zero]))
    have d4 := one_le_depth e₁.2.1 e₁.2.2.1
    have d5 := one_le_depth e₂.2.1 e₂.2.2.1
    rw [hr2] at d2
    omega
  -- an isomorphism `a₂ ≅ a` gives the `D̃₄` star at `a₂` in `P/σ₁`
  have star : ∀ c : a₂.out ⟶ a.out, IsIso c → t₁ ≫ c = α.1 → α₂.1 ≫ c = t₂ → False := by
    intro c hc h1 h2
    refine B.not_s4s hmin hL hR σ₁ hσ₁.2.1 hσ₁0 t₁ α₂.1 f₁.1 (c ≫ e₁.1)
      (seg n12 α₂.1 f₁.1 f₂.1 hσ₂v)
      (not_ftm_mid hσ₁0 hit₁ (q := e₂.1) (by rw [← hσ₁v, ← h1]; simp only [Category.assoc]))
      (seg n1ρ₁ (𝟙 _) t₁ (f₁.1 ≫ f₂.1) (by simpa using hr1))
      (seg n1ρ₁ (𝟙 _) (t₁ ≫ f₁.1) f₂.1 (by simpa using hr1))
      (not_ftm_prefix hσ₁0 e₂.2.2.1 (by rw [← hσ₁v, ← h1]; simp only [Category.assoc]))
      (seg n12 (𝟙 _) α₂.1 (f₁.1 ≫ f₂.1) (by simpa using hσ₂v))
      (seg n12 (𝟙 _) (α₂.1 ≫ f₁.1) f₂.1 (by simpa using hσ₂v))
      (seg n1ρ₂ (𝟙 _) (α₂.1 ≫ c ≫ e₁.1) e₂.1 (by
        simp only [Category.id_comp, Category.assoc]; rw [← Category.assoc α₂.1, h2]; exact hr2))
      hit₁ α₂.2.2.1 f₁.2.2.1 (fun h ↦ e₁.2.2.1 (by
        have e : e₁.1 = inv c ≫ (c ≫ e₁.1) := by simp
        rw [e]; infer_instance)) ?_ ?_
      (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hσ₂v, ← hg, ← hr1]; simp only [Category.assoc]⟩)
      (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr1, ← hg, Category.assoc, hσ₂v]⟩)
    · rintro ⟨g, hg⟩
      refine hmx2 ⟨g ≫ e₂.1, ?_⟩
      calc (α₂.1 ≫ f₁.1) ≫ g ≫ e₂.1 = α₂.1 ≫ (f₁.1 ≫ g) ≫ e₂.1 := by simp
        _ = α₂.1 ≫ (c ≫ e₁.1) ≫ e₂.1 := by rw [hg]
        _ = (α₂.1 ≫ c) ≫ e₁.1 ≫ e₂.1 := by simp
        _ = ρ₂ := by rw [h2, hr2]
    · rintro ⟨g, hg⟩
      refine hmx1 ⟨g ≫ f₂.1, ?_⟩
      calc (α.1 ≫ e₁.1) ≫ g ≫ f₂.1 = (t₁ ≫ c) ≫ e₁.1 ≫ g ≫ f₂.1 := by rw [h1]; simp
        _ = t₁ ≫ ((c ≫ e₁.1) ≫ g) ≫ f₂.1 := by simp
        _ = ρ₁ := by rw [hg, hr1]
  -- otherwise `(t₁, α₂, t₂, α)` is a crown of arrows
  have v1 : ¬∃ c, α₂.1 ≫ c = t₂ := by
    rintro ⟨c, hc⟩
    rcases hirr₂.2.2 _ α₂.1 c hc.symm with h | h
    · exact α₂.2.2.1 h
    · exact star c h (irr_eq (irr_comp_iso hirr₁ c) α.2) hc
  have v2 : ¬∃ c, t₂ ≫ c = α₂.1 := by
    rintro ⟨c, hc⟩
    rcases α₂.2.2.2 _ t₂ c hc.symm with h | h
    · exact hit₂ h
    · exact star (inv c) inferInstance (irr_eq (irr_comp_iso hirr₁ (inv c)) α.2) (by
        rw [← hc]; simp)
  have v3 : ¬∃ c, α.1 ≫ c = t₁ := by
    rintro ⟨c, hc⟩
    rcases hirr₁.2.2 _ α.1 c hc.symm with h | h
    · exact α.2.2.1 h
    · exact star (inv c) inferInstance (by rw [← hc]; simp)
        (irr_eq (irr_comp_iso α₂.2 (inv c)) hirr₂)
  have v4 : ¬∃ c, t₁ ≫ c = α.1 := by
    rintro ⟨c, hc⟩
    rcases α.2.2.2 _ t₁ c hc.symm with h | h
    · exact hit₁ h
    · exact star c h hc (irr_eq (irr_comp_iso α₂.2 c) hirr₂)
  let K := Crown.mk4 t₁ α₂.1 t₂ α.1
    (fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr1, ← hg, Category.assoc, hσ₂v]⟩)
    (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hσ₂v, ← hg, ← hr1]; simp only [Category.assoc]⟩) v1 v2
    (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [← hr2, ← hg, Category.assoc, hσ₁v]⟩)
    (fun ⟨g, hg⟩ ↦ hq2 ⟨g, by rw [← hσ₁v, ← hg, ← hr2]; simp only [Category.assoc]⟩) v3 v4
    hirr₁.1 α₂.2.1 hirr₂.1 α.2.1
  exact B.no_crown_irr hmin K (Crown.mk4_irr hirr₁ α₂.2 hirr₂ α.2) σ₁ hσ₁

include B in
/-- **BO13a Lemma 7, core**: a crown `(σ₁, ρ₁, σ₂, ρ₂)` of length four with `σ₁ ≠ σ₂`
long, `ρ₁`, `ρ₂` not long, `ρ₁ ≤ σ₁`, `ρ₂ ≤ σ₂` and only `σ₁`, `σ₂` long is impossible. -/
theorem l7_core
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    {x x₂ y₀ y₁ : P} {σ₁ : x ⟶ y₀} {ρ₁ : x ⟶ y₁} {σ₂ : x₂ ⟶ y₁} {ρ₂ : x₂ ⟶ y₀}
    (hσ₁ : IsLong σ₁) (hσ₂ : IsLong σ₂) (hρ₁0 : ρ₁ ≠ 0) (hρ₂0 : ρ₂ ≠ 0)
    (hρ₁l : ¬IsLong ρ₁) (hρ₂l : ¬IsLong ρ₂)
    (hv1 : ¬∃ c, σ₁ ≫ c = ρ₁) (hv2 : ¬∃ c, ρ₁ ≫ c = σ₁)
    (hp1 : ¬∃ c, c ≫ σ₂ = ρ₁) (hp2 : ¬∃ c, c ≫ ρ₁ = σ₂)
    (hw1 : ¬∃ c, σ₂ ≫ c = ρ₂) (hw2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (hq1 : ¬∃ c, c ≫ σ₁ = ρ₂) (hq2 : ¬∃ c, c ≫ ρ₂ = σ₁)
    (hle1 : FactorsThroughMorphism ρ₁ σ₁) (hle2 : FactorsThroughMorphism ρ₂ σ₂)
    (hne : (⟨x, y₀, σ₁⟩ : RayMor P) ≠ ⟨x₂, y₁, σ₂⟩)
    (hD44 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F73.thin) k)) : False := by
  -- the crown `(ρ₁, σ₂, ρ₂, σ₁)` for Lemma 5 a)
  let K := Crown.mk4 ρ₁ σ₂ ρ₂ σ₁ hp1 hp2 hw1 hw2 hq1 hq2 hv1 hv2 hρ₁0 hσ₂.1 hρ₂0 hσ₁.1
  have eσ1 : (⟨_, _, K.toZChain.σ 1⟩ : RayMor P) = ⟨x, y₀, σ₁⟩ := by rw [Crown.toZChain_σ]; rfl
  have eσ0 : (⟨_, _, K.toZChain.σ 0⟩ : RayMor P) = ⟨x₂, y₁, σ₂⟩ := by rw [Crown.toZChain_σ]; rfl
  have eσ2 : (⟨_, _, K.toZChain.σ 2⟩ : RayMor P) = ⟨x₂, y₁, σ₂⟩ := by rw [Crown.toZChain_σ]; rfl
  have eρ0 : (⟨_, _, K.toZChain.ρ 0⟩ : RayMor P) = ⟨x, y₁, ρ₁⟩ := rfl
  have eρ1 : (⟨_, _, K.toZChain.ρ 1⟩ : RayMor P) = ⟨x₂, y₀, ρ₂⟩ := rfl
  have eρ2 : (⟨_, _, K.toZChain.ρ 2⟩ : RayMor P) = ⟨x, y₁, ρ₁⟩ := rfl
  have first₁ : ∀ {c d : RayVert P} (α : RayVert.mk x ⟶ c) (β : RayVert.mk x ⟶ d)
      (v' : Quiver.Path c (RayVert.mk y₀)) (w' : Quiver.Path d (RayVert.mk y₀)),
      pathVal (α.toPath.comp v') = σ₁ → pathVal (β.toPath.comp w') = σ₁ →
      ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') →
      (∃ g, α.1 ≫ g = ρ₁) ∨ (∃ g, β.1 ≫ g = ρ₁) := by
    intro c d α β v' w' hv hw hni
    by_contra h
    exact B.lemma5a_mk hmin hL hR hQ hcont K.toZChain 1 eσ1 eρ2 hσ₁
      ⟨0, isLong_of_rayMor_eq eσ2.symm hσ₂⟩ α β v' w' hv hw hni (fun h' ↦ h (Or.inl h'))
      (fun h' ↦ h (Or.inr h'))
  have first₂ : ∀ {c d : RayVert P} (α : RayVert.mk x₂ ⟶ c) (β : RayVert.mk x₂ ⟶ d)
      (v' : Quiver.Path c (RayVert.mk y₁)) (w' : Quiver.Path d (RayVert.mk y₁)),
      pathVal (α.toPath.comp v') = σ₂ → pathVal (β.toPath.comp w') = σ₂ →
      ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') →
      (∃ g, α.1 ≫ g = ρ₂) ∨ (∃ g, β.1 ≫ g = ρ₂) := by
    intro c d α β v' w' hv hw hni
    by_contra h
    exact B.lemma5a_mk hmin hL hR hQ hcont K.toZChain 0 eσ0 eρ1 hσ₂
      ⟨0, isLong_of_rayMor_eq eσ1.symm hσ₁⟩ α β v' w' hv hw hni (fun h' ↦ h (Or.inl h'))
      (fun h' ↦ h (Or.inr h'))
  have last₁ : ∀ {c d : RayVert P} (α : c ⟶ RayVert.mk y₀) (β : d ⟶ RayVert.mk y₀)
      (v' : Quiver.Path (RayVert.mk x) c) (w' : Quiver.Path (RayVert.mk x) d),
      pathVal (v'.cons α) = σ₁ → pathVal (w'.cons β) = σ₁ → ¬Interlaced (v'.cons α) (w'.cons β) →
      (∃ g, g ≫ α.1 = ρ₂) ∨ (∃ g, g ≫ β.1 = ρ₂) := by
    intro c d α β v' w' hv hw hni
    by_contra h
    exact B.lemma5a_last_mk hmin hL hR hQ hcont K 1 eσ1 eρ1 hσ₁ α β v' w' hv hw hni
      (fun h' ↦ h (Or.inl h')) (fun h' ↦ h (Or.inr h'))
  have last₂ : ∀ {c d : RayVert P} (α : c ⟶ RayVert.mk y₁) (β : d ⟶ RayVert.mk y₁)
      (v' : Quiver.Path (RayVert.mk x₂) c) (w' : Quiver.Path (RayVert.mk x₂) d),
      pathVal (v'.cons α) = σ₂ → pathVal (w'.cons β) = σ₂ → ¬Interlaced (v'.cons α) (w'.cons β) →
      (∃ g, g ≫ α.1 = ρ₁) ∨ (∃ g, g ≫ β.1 = ρ₁) := by
    intro c d α β v' w' hv hw hni
    by_contra h
    exact B.lemma5a_last_mk hmin hL hR hQ hcont K 0 eσ0 eρ0 hσ₂ α β v' w' hv hw hni
      (fun h' ↦ h (Or.inl h')) (fun h' ↦ h (Or.inr h'))
  -- a contour of `σ₁` carrying `ρ₁`, normalized
  obtain ⟨c, d, α, β, v', w', hv, hw, hni, hα⟩ : ∃ (c d : RayVert P) (α : RayVert.mk x ⟶ c)
      (β : RayVert.mk x ⟶ d) (v' : Quiver.Path c (RayVert.mk y₀))
      (w' : Quiver.Path d (RayVert.mk y₀)), pathVal (α.toPath.comp v') = σ₁ ∧
        pathVal (β.toPath.comp w') = σ₁ ∧ ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') ∧
          ∃ g, α.1 ≫ g = ρ₁ := by
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hσ₁ (hcont _ hσ₁)
    rcases first₁ α β v' w' hv hw hni with h | h
    · exact ⟨_, _, α, β, v', w', hv, hw, hni, h⟩
    · exact ⟨_, _, β, α, w', v', hw, hv, fun h' ↦ hni h'.symm, h⟩
  have hβρ₁ : ¬∃ g, β.1 ≫ g = ρ₁ := fun hβ ↦ B.not_factors_both hmin hL hR α β v' w'
    (by rw [hv, hw]) (by rw [hv]; exact hσ₁.1) hni ⟨_, ρ₁⟩ hρ₁0
    (by rintro ⟨c', hc⟩; rw [hv] at hc; exact hv1 ⟨c', hc⟩)
    (by rintro ⟨c', hc⟩; change ρ₁ ≫ c' = _ at hc; rw [hv] at hc; exact hv2 ⟨c', hc⟩) hα hβ
  obtain ⟨-, b, e₁, e₂, rfl, hmx1⟩ := B.l7_nice hmin hL hR hQ hcont hσ₁ hρ₁0 hρ₁l hv1 hv2 hle1
    hσ₂ hp1 hp2 hne α β v' w' hv hw hni hα
  obtain ⟨ρ₁', hρ₁'⟩ := hα
  -- a contour of `σ₂` carrying `ρ₂`, normalized
  obtain ⟨c₂, d₂, α₂, β₂, v₂, w₂, hv₂, hw₂, hni₂, hα₂⟩ : ∃ (c d : RayVert P)
      (α : RayVert.mk x₂ ⟶ c) (β : RayVert.mk x₂ ⟶ d) (v' : Quiver.Path c (RayVert.mk y₁))
      (w' : Quiver.Path d (RayVert.mk y₁)), pathVal (α.toPath.comp v') = σ₂ ∧
        pathVal (β.toPath.comp w') = σ₂ ∧ ¬Interlaced (α.toPath.comp v') (β.toPath.comp w') ∧
          ∃ g, α.1 ≫ g = ρ₂ := by
    obtain ⟨c, d, α, β, v', w', hv, hw, hni⟩ := exists_contour_first hσ₂ (hcont _ hσ₂)
    rcases first₂ α β v' w' hv hw hni with h | h
    · exact ⟨_, _, α, β, v', w', hv, hw, hni, h⟩
    · exact ⟨_, _, β, α, w', v', hw, hv, fun h' ↦ hni h'.symm, h⟩
  have hβρ₂ : ¬∃ g, β₂.1 ≫ g = ρ₂ := fun hβ ↦ B.not_factors_both hmin hL hR α₂ β₂ v₂ w₂
    (by rw [hv₂, hw₂]) (by rw [hv₂]; exact hσ₂.1) hni₂ ⟨_, ρ₂⟩ hρ₂0
    (by rintro ⟨c', hc⟩; rw [hv₂] at hc; exact hw1 ⟨c', hc⟩)
    (by rintro ⟨c', hc⟩; change ρ₂ ≫ c' = _ at hc; rw [hv₂] at hc; exact hw2 ⟨c', hc⟩) hα₂ hβ
  obtain ⟨-, b₂, f₁, f₂, rfl, hmx2⟩ := B.l7_nice hmin hL hR hQ hcont hσ₂ hρ₂0 hρ₂l hw1 hw2 hle2
    hσ₁ hq1 hq2 (fun h ↦ hne h.symm) α₂ β₂ v₂ w₂ hv₂ hw₂ hni₂ hα₂
  obtain ⟨ρ₂', hρ₂'⟩ := hα₂
  have hσ₁v : α.1 ≫ e₁.1 ≫ e₂.1 = σ₁ := by
    rw [← hv, pathVal_comp, pathVal_toPath]
    change _ = α.1 ≫ ((𝟙 _ ≫ e₁.1) ≫ e₂.1)
    simp
  have hσ₂v : α₂.1 ≫ f₁.1 ≫ f₂.1 = σ₂ := by
    rw [← hv₂, pathVal_comp, pathVal_toPath]
    change _ = α₂.1 ≫ ((𝟙 _ ≫ f₁.1) ≫ f₂.1)
    simp
  -- permeable or reflecting
  obtain ⟨_, q₂, ω₂, hq₂⟩ := exists_last_arrow (β₂.toPath.comp w₂) (by rw [hw₂]; exact hσ₂.2.1)
  obtain ⟨_, q₁, ω₁, hq₁⟩ := exists_last_arrow (β.toPath.comp w') (by rw [hw]; exact hσ₁.2.1)
  rcases last₂ f₂ ω₂ (α₂.toPath.comp (Quiver.Path.nil.cons f₁)) q₂ hv₂ (by rw [← hq₂]; exact hw₂)
      (by rw [← hq₂]; exact hni₂) with hr₂ | hω₂
  · rcases last₁ e₂ ω₁ (α.toPath.comp (Quiver.Path.nil.cons e₁)) q₁ hv (by rw [← hq₁]; exact hw)
        (by rw [← hq₁]; exact hni) with hr₁ | hω₁
    · exact B.l7_refl hmin hL hR hσ₁ hσ₂ hρ₁0 hρ₂0 hρ₁l hρ₂l hv2 hp1 hp2 hw2 hq1 hq2 hle1 hle2
        hne α e₁ e₂ hσ₁v ρ₁' hρ₁' hmx1 α₂ f₁ f₂ hσ₂v ρ₂' hρ₂' hmx2
        (B.l7_depth hmin hL hR hQ hcont hσ₁ hρ₁0 hρ₁l hv1 hv2 hle1 hσ₂ hp1 hp2 hne first₁)
        (B.l7_depth hmin hL hR hQ hcont hσ₂ hρ₂0 hρ₂l hw1 hw2 hle2 hσ₁ hq1 hq2
          (fun h ↦ hne h.symm) first₂) hr₁ hr₂
    · exact B.l7_perm hmin hL hR hσ₂ hσ₁ hρ₂0 hρ₁0 hρ₂l hρ₁l hw2 hq1 hq2 hv2
        (fun h ↦ hne h.symm) α₂ f₁ f₂ β₂ w₂ hv₂ hw₂ hni₂ ρ₂' hρ₂' hmx2 hβρ₂ α e₁ e₂ β w' hv hw
        hni ρ₁' hρ₁' hmx1 hβρ₁ q₁ ω₁ hq₁ hω₁ hD44
  · exact B.l7_perm hmin hL hR hσ₁ hσ₂ hρ₁0 hρ₂0 hρ₁l hρ₂l hv2 hp1 hp2 hw2 hne α e₁ e₂ β w' hv
      hw hni ρ₁' hρ₁' hmx1 hβρ₁ α₂ f₁ f₂ β₂ w₂ hv₂ hw₂ hni₂ ρ₂' hρ₂' hmx2 hβρ₂ q₂ ω₂ hq₂ hω₂ hD44

end MulBasis

end RayQuiver

end LargeIndecomposable
