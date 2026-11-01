module

public import LargeIndecomposable.Crowns.Lemma6.CaseIIAMain
public import LargeIndecomposable.Crowns.Lemma6.CaseIU
public import LargeIndecomposable.Cleaving.Shapes.ShapeF616
public import LargeIndecomposable.Cleaving.Shapes.ShapeF617
public import LargeIndecomposable.Cleaving.Shapes.ShapeF618

/-!
# BO13a Lemma 6, case II.C: diagrams

`σ, ρ` long neighbours, `ρₙ`, `σ₂` not long, `ρₙ` factors through the last
arrow of `u₂` and `σ₂` through the last arrow of `u₂'`.

* `MulBasis.l6_s614`: figure 6.14 (`D̃₅` `w₁, ψ, w₁', ρₙ', σ₂'`, `P/σ`);
* `MulBasis.l6_f615`: figure 6.15 (`D̃₄` star `ρₙ', ψ₂ ; u₂, u₂'`, `P/σ`) when
  `ρₙ ≤ σ`; `ψ₂` is chosen as the longest suffix of `ψ` through which `ρₙ'`
  does not factor, and Lemma 4 c) excludes `ψ₂ = ψ`;
* `MulBasis.l6_f617`: figure 6.17 (category 20 with `σ₂' ≫ a = 0`, `P/σ`);
* `MulBasis.l6_IIC_β`: the case where `ρₙ` does not factor through `u₂`
  (figures 6.16 (`Ẽ₆`), 6.17, 6.18 and two `D̃₄` stars);
* `MulBasis.l6_IIC_αend`: the end of the case `ρₙ = ρₙ' ≫ u₂` after the crown
  of length four.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

/-- **A maximal suffix through which `f` factors**, possibly empty. -/
lemma exists_max_suffix₀ {x y : RayVert P} {z : P} (f : z ⟶ y.out) :
    ∀ {w : RayVert P} (p : Quiver.Path x w) (q : Quiver.Path w y),
      (∃ g, g ≫ pathVal q = f) → (¬∃ g, g ≫ pathVal (p.comp q) = f) →
      ∃ (w'' w' : RayVert P) (p₁ : Quiver.Path x w'') (e : w'' ⟶ w') (p₂ : Quiver.Path w' y),
        (p₁.cons e).comp p₂ = p.comp q ∧ (∃ g, g ≫ pathVal p₂ = f) ∧
          ¬∃ g, g ≫ e.1 ≫ pathVal p₂ = f := by
  intro w p
  induction p with
  | nil =>
    intro q hq hpq
    exact absurd (by simpa using hq) hpq
  | cons p' e ih =>
    intro q hq hpq
    by_cases h : ∃ g, g ≫ e.1 ≫ pathVal q = f
    · have e1 : (p'.cons e).comp q = p'.comp (e.toPath.comp q) := by
        rw [← Quiver.Path.comp_assoc]; rfl
      obtain ⟨w'', w', p₁, e', p₂, h1, h3, h4⟩ := ih (e.toPath.comp q)
        (by obtain ⟨g, hg⟩ := h; exact ⟨g, by rw [pathVal_comp, pathVal_toPath]; exact hg⟩)
        (by rw [← e1]; exact hpq)
      exact ⟨w'', w', p₁, e', p₂, by rw [h1, e1], h3, h4⟩
    · exact ⟨_, _, p', e, q, rfl, hq, h⟩

variable [IsRayCategory P] [IsFiniteRayCategory P]

omit [IsRayCategory P] in
/-- The four ways two nonzero parallel morphisms compare. -/
lemma cmp4 (hQ : OneSidedCyclic P) {X Y : P} (f g : X ⟶ Y) (hf : f ≠ 0) (hg : g ≠ 0) :
    (∃ b : End Y, g = f ≫ b) ∨ (∃ a : End X, g = a ≫ f) ∨ (∃ b : End Y, f = g ≫ b) ∨
      (∃ a : End X, f = a ≫ g) := by
  rcases IsFiniteRayCategory.factorization_comparable f g with hT | hT
  · rcases hQ X Y with h | h
    · exact Or.inl (h f g hg hT)
    · exact Or.inr (Or.inl (h f g hg hT))
  · rcases hQ X Y with h | h
    · exact Or.inr (Or.inr (Or.inl (h g f hf hT)))
    · exact Or.inr (Or.inr (Or.inr (h g f hf hT)))

omit [IsFiniteRayCategory P] in
/-- **Maximality of `ψ`**: no proper extension `ψ ≫ d` divides both `σ` and `ρ`. -/
lemma L6Data.not_common_ext (hL : LeftCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀} {ρ : x ⟶ y₁}
    (hσ0 : σ ≠ 0) (D : L6Data σ ρ) {c : P} (d : D.m.out ⟶ c) (hid : ¬IsIso d) (a : c ⟶ y₀)
    (a' : c ⟶ y₁) (ha : d ≫ a = D.U) (ha' : d ≫ a' = D.U') : False := by
  have hle := D.hmax ⟨_, D.ψ ≫ d⟩ ⟨pathVal D.χ ≫ d, by
      change D.α.1 ≫ pathVal D.χ ≫ d = D.ψ ≫ d
      simp only [L6Data.ψ]
      rw [pathVal_comp D.α.toPath D.χ, pathVal_toPath, Category.assoc]⟩
    ⟨a, by change (D.ψ ≫ d) ≫ a = σ; rw [Category.assoc, ha, D.ψU]⟩
    ⟨a', by change (D.ψ ≫ d) ≫ a' = ρ; rw [Category.assoc, ha', D.ψU']⟩
  obtain ⟨k', hk'⟩ := hle
  change (D.ψ ≫ d) ≫ k' = D.ψ at hk'
  have hdk : d ≫ k' = 𝟙 _ := hL D.ψ _ _ (by rw [Category.comp_id, ← Category.assoc, hk'])
    (by rw [← Category.assoc, hk']; exact fun h ↦ hσ0 (by rw [← D.ψU, h, zero_comp]))
  exact not_split_mono hid ⟨k', hdk⟩

/-- `σ` does not divide `σ₂' ≫ a` for `σ₂ = σ₂' ≫ u₂'` and a proper prefix `a` of
`u₂` (else `σ₂` and `ρ` would be parallel). -/
lemma l6_gap (hQ : OneSidedCyclic P) (hL : LeftCancel P) {x y₀ y₁ : P} {σ : x ⟶ y₀}
    {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (D : L6Data σ ρ) {x'' : P} (σ₂ : x'' ⟶ y₁)
    (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂) (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂)
    (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂) {c : P} (A : D.m.out ⟶ c) (Bm : c ⟶ y₀)
    (hAB : A ≫ Bm = D.U) (hiB : ¬IsIso Bm) (htA : t ≫ A ≠ 0) :
    ¬FactorsThroughMorphism σ (t ≫ A) := by
  intro h
  obtain ⟨hx, hy, he⟩ := hσ.2.2.2 (t ≫ A) htA h
  subst hx hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
  have hψ0 : D.ψ ≠ 0 := fun h0 ↦ hσ.1 (by rw [← D.ψU, h0, zero_comp])
  have ht0 : t ≠ 0 := fun h0 ↦ hσ₂0 (by rw [← ht, h0, zero_comp])
  refine not_parallel hQ σ₂ ρ hσ₂0 hρ.1 ?_ ?_ hm1 hm2
  · rintro ⟨c', hc'⟩
    rcases cmp4 hQ t D.ψ ht0 hψ0 with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨b, hb⟩ | ⟨a, ha⟩
    · have e1 := D.ψU
      rw [← hAB, hb] at e1
      have h1 : t ≫ A = t ≫ ((show D.m.out ⟶ D.m.out from b) ≫ A ≫ Bm) :=
        (he.trans e1.symm).trans (by simp)
      have h2 := hL t _ _ h1 htA
      have hA0 : A ≠ 0 := fun h0 ↦ htA (by rw [h0, comp_zero])
      obtain ⟨-, hB1⟩ := IsRayCategory.eq_id_of_two_sided A hA0 _ _ h2
      exact hiB (by rw [hB1]; infer_instance)
    · exact hm1 ⟨a, by rw [← ht, ← Category.assoc, ← ha]; exact D.ψU'⟩
    · have h1 : D.ψ ≫ D.U' = D.ψ ≫ ((show D.m.out ⟶ D.m.out from b) ≫ D.U' ≫ c') :=
        calc D.ψ ≫ D.U' = ρ := D.ψU'
          _ = σ₂ ≫ c' := hc'.symm
          _ = _ := by rw [← ht, hb]; simp
      have h2 := hL D.ψ _ _ h1 (by rw [D.ψU']; exact hρ.1)
      have hU'0 : D.U' ≠ 0 := fun h0 ↦ hρ.1 (by rw [← D.ψU', h0, comp_zero])
      obtain ⟨hb1, -⟩ := IsRayCategory.eq_id_of_two_sided D.U' hU'0 _ c' h2
      refine hm1 ⟨𝟙 _, ?_⟩
      rw [Category.id_comp, ← ht, hb, show (show D.m.out ⟶ D.m.out from b) = 𝟙 _ from hb1,
        Category.comp_id]
      exact D.ψU'
    · exact hm2 ⟨a, by rw [← ht, ha, Category.assoc]; exact (congrArg (a ≫ ·) D.ψU').symm⟩
  · rintro ⟨c', hc'⟩
    exact hσ₂l (hρ.of_factorsThrough hσ₂0 ⟨𝟙 _, c', by rw [← hc']; simp⟩)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a figure 6.14**: `D̃₅` `w₁, ψ, w₁', ρₙ', σ₂'` in `P/σ` (`σ₂` not long). -/
theorem l6_s614
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x'' : P} (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0)
    (hσ₂l : ¬IsLong σ₂) (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂) {x' : P}
    (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn)
    (hp2 : ¬∃ c, c ≫ ρn = σ) (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (t : x'' ⟶ D.m.out)
    (ht : t ≫ D.U' = σ₂) (hrt : ¬∃ g, g ≫ r = t) (htr : ¬∃ g, g ≫ t = r) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  refine B.not_s65 hmin hL hR σ hσ.2.1 hσ0 D.β.1 D.ψ D.β'.1 r t
    (not_ftm_prefix hσ0 (D.W_not_isIso hσ.2.2.1) D.βW) (not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.βW']; exact FactorsThroughMorphism.comp_right h _))
    (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    D.β.2.2.1 D.ψ_not_isIso D.β'.2.2.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrt ?_ htr
  · exact fun h ↦ hp2 ⟨D.ψ ≫ inv r, by rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  · exact fun h ↦ hm1 ⟨D.ψ ≫ inv t, by rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.W', by rw [← Category.assoc, hg, D.βW']⟩
  · rintro ⟨g, hg⟩
    rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩
  · rintro ⟨g, hg⟩
    rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.W, by rw [← Category.assoc, hg, D.βW]⟩
  · exact fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hp1 ⟨g, by rw [← hr, ← hg, Category.assoc, D.ψU]⟩
  · exact fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩
  · exact fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← D.ψU, ← hg, Category.assoc, hr]⟩
  · exact fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← D.ψU', ← hg, Category.assoc, ht]⟩

include B in
/-- **BO13a figure 6.15**: for `ρₙ = ρₙ' ≫ u₂` with `ρₙ' ≫ u₂' ≠ 0` and `ρₙ ≤ σ`,
the `D̃₄` star `ρₙ', ψ₂ ; u₂, u₂'` in `P/σ`. -/
theorem l6_f615
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (hrU' : r ≫ D.U' ≠ 0)
    (hle : FactorsThroughMorphism ρn σ) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  obtain ⟨_, _, p₁, e, p₂, hsplit, ⟨g, hg⟩, hmx⟩ := exists_max_suffix₀ (x := RayVert.mk x)
    (y := D.m) r (D.α.toPath.comp D.χ) Quiver.Path.nil ⟨r, Category.comp_id r⟩ (by
      rintro ⟨g, hg⟩
      have h1 : g ≫ D.ψ = r := by simpa using hg
      exact hp1 ⟨g, by rw [← hr, ← h1, Category.assoc, D.ψU]⟩)
  have hsplit' : pathVal p₁ ≫ e.1 ≫ pathVal p₂ = D.ψ := by
    have := congrArg pathVal hsplit
    rw [pathVal_comp, Quiver.Path.comp_nil] at this
    rw [← Category.assoc]; exact this
  obtain ⟨E, hE⟩ : ∃ E, E = e.1 ≫ pathVal p₂ := ⟨_, rfl⟩
  rw [← hE] at hsplit' hmx
  by_cases hp₁ : p₁.length = 0
  · cases p₁ with
    | cons _ _ => simp at hp₁
    | nil =>
      obtain ⟨c, d, hcd⟩ := hle
      have hEψ : E = D.ψ := by rw [← hsplit']; exact (Category.id_comp _).symm
      have h1 : e.1 ≫ pathVal p₂ ≫ D.U = σ := by
        rw [← Category.assoc, ← hE, hEψ]; exact D.ψU
      obtain ⟨_, d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL hp2 (pathVal p₂ ≫ D.U) e.1 g h1
        (by rw [← Category.assoc, hg, hr]) d c hcd.symm hσ0
      rcases e.2.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
  · have hiPre : ¬IsIso (pathVal p₁) := not_isIso_pathVal p₁ (by omega)
    have hiE : ¬IsIso E := by
      have := not_isIso_pathVal (e.toPath.comp p₂) (by simp)
      rwa [pathVal_comp, pathVal_toPath, ← hE] at this
    refine B.not_s4s hmin hL hR σ hσ.2.1 hσ0 r E D.U D.U'
      (not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU)
      (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
        rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
      (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
        rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
      (by rw [hr]; exact fun h ↦ hρnl (hσ.of_factorsThrough hρn0 h))
      (l6_ρ_not_to_y₀ hQ hρ hσ hv2 hv1 _ hrU')
      (fun h ↦ not_ftm_prefix hσ0 D.U_not_isIso D.ψU (by
        rw [← hsplit']; exact FactorsThroughMorphism.comp_left h _))
      (not_ftm_suffix hσ0 hiPre (by rw [← Category.assoc, hsplit', D.ψU]))
      (l6_ρ_not_to_y₀ hQ hρ hσ hv2 hv1 _ (fun h0 ↦ hρ0 (D.ψU'.symm.trans (by
        rw [← hsplit', Category.assoc, h0, comp_zero]))))
      hir hiE D.U_not_isIso D.U'_not_isIso (D.U_U' hv1) (D.U'_U hv2) ?_ hmx
    rintro ⟨g', hg'⟩
    have : (pathVal p₁ ≫ g') ≫ ρn = D.ψ ≫ D.U := by
      rw [← hsplit', ← hg', ← hr]; simp only [Category.assoc]
    exact hp2 ⟨pathVal p₁ ≫ g', this.trans D.ψU⟩

include B in
/-- **Case II.C (α), end**: `ρₙ = ρₙ' ≫ u₂`, `ρₙ' ≫ u₂' ≠ 0` and every long
morphism divides `σ` or `ρ` (a crown of length four). -/
theorem l6_IIC_αend
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hiρn : ¬IsIso ρn) (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (r : x' ⟶ D.m.out) (hr : r ≫ D.U = ρn) (hrU' : r ≫ D.U' ≠ 0)
    (h2 : ∀ {a b : P} (τ : a ⟶ b), IsLong τ → FactorsThroughMorphism τ σ ∨
      FactorsThroughMorphism τ ρ) : False := by
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ inv r, by
    rw [← hr, Category.assoc, IsIso.inv_hom_id_assoc, D.ψU]⟩
  have hρnr : ¬IsIrreducible ρn := fun h ↦ by
    rcases h.2.2 _ r D.U hr.symm with h' | h'
    · exact hir h'
    · exact D.U_not_isIso h'
  exact B.l6_f615 hmin hL hR hQ hσ hρ hv1 hv2 D ρn hρn0 hρnl hp1 hp2 r hr hrU'
    (l6_le_σ hσ hv1 ρn hρn0 hiρn hρnr h2 hρ)

include B in
/-- **BO13a figure 6.17** (category 20 with `σ₂' ≫ a = 0`) in `P/σ`, for a morphism
`φ` out of the domain of `σ₂` (in BO13a `φ = ρ₂`). -/
theorem l6_f617
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ) {x' x'' : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0)
    (hρnl : ¬IsLong ρn) (hp2 : ¬∃ c, c ≫ ρn = σ) (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0)
    (hσ₂l : ¬IsLong σ₂) (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂)
    (hσ₂W' : ¬∃ g, g ≫ D.W' = σ₂) {c : P} (a : D.m.out ⟶ c) (bb : c ⟶ y₀)
    (hab : a ≫ bb = D.U) (hia : ¬IsIso a) (hβa : ¬∃ g, D.β.1 ≫ g = D.ψ ≫ a)
    (r : x' ⟶ c) (hr : r ≫ bb = ρn) (hra : ¬∃ g, g ≫ a = r) (t : x'' ⟶ D.m.out)
    (ht : t ≫ D.U' = σ₂) (hta : t ≫ a = 0) (hib : ¬IsIso bb) {z : P} (φ : x'' ⟶ z)
    (h0φ : ¬FactorsThroughMorphism σ φ) (hiφ : ¬IsIso φ) (hφ1 : ¬∃ g, t ≫ g = φ)
    (hφ2 : ¬∃ g, φ ≫ g = σ₂)
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F617.thin) k)) : False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  have hρβ := B.l6_ρβ hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hσβ' := B.l6_σβ' hmin hL hR hσ0 hρ0 hv1 hv2 D
  have hψab : D.ψ ≫ a ≫ bb = σ := by rw [hab]; exact D.ψU
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ a ≫ inv r, by
    rw [← hr, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc]; exact hψab⟩
  have hit : ¬IsIso t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
    rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc]; exact D.ψU'⟩
  refine B.not_f617 hmin hL hR σ hσ.2.1 hσ0 D.β'.1 D.ψ D.U' D.W' D.β.1 a r t φ hD
    (by rw [D.ψU', D.βW']) hta
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.βW']; exact FactorsThroughMorphism.comp_left h _))
    (not_ftm_mid hσ0 D.ψ_not_isIso hψab)
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _))
    (not_ftm_prefix hσ0 (D.W_not_isIso hσ.2.2.1) D.βW)
    (fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
      rw [← D.βW']; exact FactorsThroughMorphism.comp_right h _))
    (not_ftm_prefix hσ0 hib (by rw [Category.assoc]; exact hψab))
    (not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
    (by rw [D.βW']; exact not_ftm_long_dom hσ hρ0 hv1)
    (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
      rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
    (fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
      rw [← ht]; exact FactorsThroughMorphism.comp_right h _)))
    (by rw [ht]; exact fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 h)) h0φ
    D.β'.2.2.1 D.ψ_not_isIso D.U'_not_isIso (D.W'_not_isIso hρ.2.2.1) D.β.2.2.1 hia hir hit hiφ
    (fun ⟨g, hg⟩ ↦ D.not_common_ext hL hσ0 a hia bb g hab hg)
    (fun ⟨g, hg⟩ ↦ hv2 ⟨g ≫ bb, by
      rw [← D.ψU', Category.assoc, ← Category.assoc D.U', hg]; exact hψab⟩)
    (fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.W', by rw [← Category.assoc, hg]; exact D.βW'⟩)
    (fun ⟨g, hg⟩ ↦ hρβ ⟨g ≫ D.U', by rw [← Category.assoc, hg]; exact D.ψU'⟩)
    (fun ⟨g, hg⟩ ↦ hρβ ⟨g, by rw [hg]; exact D.βW'⟩) hβa
    (fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.U, by rw [← Category.assoc, hg]; exact D.ψU⟩)
    (fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ D.W, by rw [← Category.assoc, hg]; exact D.βW⟩)
    (fun ⟨g, hg⟩ ↦ hσβ' ⟨g ≫ bb, by rw [← Category.assoc, hg, Category.assoc]; exact hψab⟩)
    ?_ ?_ hφ1
    (fun ⟨g, hg⟩ ↦ hφ2 ⟨g ≫ D.U', by rw [← Category.assoc, hg, ht]⟩)
    (fun ⟨g, hg⟩ ↦ hφ2 ⟨g, by rw [hg, ht]⟩)
    (D.W'_U' hL hR hρ0 hρ.2.2.1).1
    (fun ⟨g, hg⟩ ↦ hσ₂W' ⟨g, by rw [hg, ht]⟩) hra (D.W'_U' hL hR hρ0 hρ.2.2.1).2
    (fun ⟨g, hg⟩ ↦ hm2 ⟨g, by rw [← ht, ← hg, Category.assoc, D.ψU']⟩)
    (fun ⟨g, hg⟩ ↦ hp2 ⟨g, by rw [← hr, ← Category.assoc, hg, Category.assoc]; exact hψab⟩)
    (fun ⟨g, hg⟩ ↦ hp2 ⟨D.ψ ≫ g, by
      rw [← hr, Category.assoc, ← Category.assoc g, hg]; exact hψab⟩)
    (fun ⟨g, hg⟩ ↦ hm1 ⟨g, by rw [← ht, ← Category.assoc, hg]; exact D.ψU'⟩)
  · rintro ⟨g, hg⟩
    rcases D.β'.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hσβ' ⟨inv g ≫ D.U, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU]⟩
  · rintro ⟨g, hg⟩
    rcases D.β.2.2.2 _ D.ψ g hg.symm with h | h
    · exact D.ψ_not_isIso h
    · exact hρβ ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, D.ψU']⟩

include B in
/-- **BO13a Lemma 6, case II.C (β)**: `σ₂ = σ₂' ≫ u₂'` and `ρₙ` factors through the
last arrow of `u₂` but not through `u₂`. With `u₂ = a ≫ b` and `ρₙ = ρₙ' ≫ b`
for the longest such suffix `b`: the star `ψ, σ₂' ; a, u₂'` if `σ₂' ≫ a ≠ 0`;
otherwise figure 6.16 (`Ẽ₆`) if `σₙ` does not factor through `ρₙ'`, figure 6.17
if `ρ₂` does not factor through `σ₂'` (with an arrow `φ` for `ρ₂` if `ρ₂ ≅ σ`),
figure 6.18 (`D̃₅`) or the star `ψ, σ₂' ; ρ₂', u₂'` (all in `P/σ`). -/
theorem l6_IIC_β
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ) {x y₀ y₁ : P}
    {σ : x ⟶ y₀} {ρ : x ⟶ y₁} (hσ : IsLong σ) (hρ : IsLong ρ) (hv1 : ¬∃ c, σ ≫ c = ρ)
    (hv2 : ¬∃ c, ρ ≫ c = σ) (D : L6Data σ ρ)
    {x' x'' zn z₂ : P} (ρn : x' ⟶ y₀) (hρn0 : ρn ≠ 0) (hρnl : ¬IsLong ρn)
    (hp1 : ¬∃ c, c ≫ σ = ρn) (hp2 : ¬∃ c, c ≫ ρn = σ)
    (σn : x' ⟶ zn) (hσn0 : σn ≠ 0) (hiσn : ¬IsIso σn) (hq1 : ¬∃ c, σn ≫ c = ρn)
    (hq2 : ¬∃ c, ρn ≫ c = σn)
    (σ₂ : x'' ⟶ y₁) (hσ₂0 : σ₂ ≠ 0) (hσ₂l : ¬IsLong σ₂)
    (hm1 : ¬∃ c, c ≫ σ₂ = ρ) (hm2 : ¬∃ c, c ≫ ρ = σ₂)
    (ρ₂ : x'' ⟶ z₂) (hρ₂0 : ρ₂ ≠ 0) (hiρ₂ : ¬IsIso ρ₂) (hs1 : ¬∃ c, σ₂ ≫ c = ρ₂)
    (hs2 : ¬∃ c, ρ₂ ≫ c = σ₂)
    (t : x'' ⟶ D.m.out) (ht : t ≫ D.U' = σ₂) (hσ₂W' : ¬∃ g, g ≫ D.W' = σ₂)
    (hρnW : ¬∃ g, g ≫ D.W = ρn) {c₀ : RayVert P} (u₀ : Quiver.Path D.m c₀)
    (e₀ : c₀ ⟶ RayVert.mk y₀) (hu : D.u₂ = u₀.cons e₀) (hρne : ∃ g, g ≫ e₀.1 = ρn)
    (hnU : ¬∃ g, g ≫ D.U = ρn)
    (hD617 : ¬Statement.IsRepresentationFinite (Linearization (ThinCat F617.thin) k)) :
    False := by
  have hσ0 := hσ.1
  have hρ0 := hρ.1
  obtain ⟨c₁, c₂, a₀, ea, b₀, hsplit, hb₀, ⟨r, hr⟩, hmx⟩ := exists_max_suffix (x := D.m)
    (y := RayVert.mk y₀) ρn u₀ e₀.toPath (by simp)
    (by obtain ⟨g, hg⟩ := hρne; exact ⟨g, by rw [pathVal_toPath]; exact hg⟩)
    (by
      rintro ⟨g, hg⟩
      exact hnU ⟨g, by change g ≫ pathVal D.u₂ = ρn; rw [hu]; exact hg⟩)
  obtain ⟨Am, hAm⟩ : ∃ Am, Am = pathVal (a₀.cons ea) := ⟨_, rfl⟩
  have hAB : Am ≫ pathVal b₀ = D.U := by
    change _ = pathVal D.u₂
    rw [hAm, ← pathVal_comp, hsplit, hu]
    rfl
  have hiA : ¬IsIso Am := by rw [hAm]; exact not_isIso_pathVal _ (by simp)
  have hiB : ¬IsIso (pathVal b₀) := not_isIso_pathVal _ hb₀
  have hψAB : D.ψ ≫ Am ≫ pathVal b₀ = σ := by rw [hAB]; exact D.ψU
  have hiψA : ¬IsIso (D.ψ ≫ Am) := fun h ↦ not_split_mono D.ψ_not_isIso
    ⟨Am ≫ inv (D.ψ ≫ Am), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have hrA : ¬∃ g, g ≫ Am = r := by
    rintro ⟨g, hg⟩
    refine hmx ⟨g ≫ pathVal a₀, ?_⟩
    rw [← hr, ← hg, hAm]
    change _ = (g ≫ (pathVal a₀ ≫ ea.1)) ≫ _
    simp only [Category.assoc]
  have hir : ¬IsIso r := fun h ↦ hp2 ⟨D.ψ ≫ Am ≫ inv r, by
    rw [← hr, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc]; exact hψAB⟩
  have hAr : ¬∃ g, g ≫ r = Am := fun ⟨g, hg⟩ ↦ hp2 ⟨D.ψ ≫ g, by
    rw [← hr, Category.assoc, ← Category.assoc g, hg]; exact hψAB⟩
  have hAU' : ¬∃ g, Am ≫ g = D.U' := fun ⟨g, hg⟩ ↦
    D.not_common_ext hL hσ0 Am hiA _ g hAB hg
  have hU'A : ¬∃ g, D.U' ≫ g = Am := fun ⟨g, hg⟩ ↦ hv2 ⟨g ≫ pathVal b₀, by
    rw [← D.ψU', Category.assoc, ← Category.assoc D.U', hg]; exact hψAB⟩
  -- the contour `(ψ u₂, β w)` does not cross at the split of `u₂`
  have hpath : ((D.α.toPath.comp D.χ).comp (a₀.cons ea)).comp b₀ =
      (D.α.toPath.comp D.χ).comp D.u₂ := by
    rw [Quiver.Path.comp_assoc, hsplit, hu]; rfl
  have hval1 : pathVal (D.β.toPath.comp D.w) =
      pathVal (((D.α.toPath.comp D.χ).comp (a₀.cons ea)).comp b₀) := by
    rw [hpath, D.hσw, D.hσu]
  have h01 : pathVal (D.β.toPath.comp D.w) ≠ 0 := by rw [D.hσw]; exact hσ0
  have hni1 : ¬Interlaced (D.β.toPath.comp D.w)
      (((D.α.toPath.comp D.χ).comp (a₀.cons ea)).comp b₀) := by
    rw [hpath]; exact fun h ↦ D.hniσ h.symm
  have cr1 := contour_cross hL hR _ _ _ _ hval1 h01 hni1 (by simp) hb₀
  have cr2 := contour_cross hL hR _ _ _ _ hval1.symm (by rw [← hval1]; exact h01)
    (fun h ↦ hni1 h.symm) (by simp) (pos_length_of_not_isIso D.w (D.W_not_isIso hσ.2.2.1))
  have hβA : ¬∃ g, D.β.1 ≫ g = D.ψ ≫ Am := by
    rintro ⟨g, hg⟩
    refine cr1.2 ⟨g, ?_⟩
    rw [pathVal_toPath, pathVal_comp, ← hAm]
    exact hg
  have h0U' : ¬FactorsThroughMorphism σ D.U' := fun h ↦ not_ftm_long_dom hσ hρ0 hv1 (by
    rw [← D.ψU']; exact FactorsThroughMorphism.comp_left h _)
  by_cases hs : ∃ s, r ≫ s = σn
  swap
  · -- figure 6.16
    refine B.not_f616 hmin hL hR σ hσ.2.1 hσ0 r σn Am D.U' (pathVal b₀) D.W
      (not_ftm_suffix hσ0 hiψA (by rw [Category.assoc]; exact hψAB))
      (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
        rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
      (by rw [hr]; exact fun h ↦ hρnl (hσ.of_factorsThrough hρn0 h))
      (l6_not_ftm_nbr hQ hσ hρn0 hσn0 hp1 hp2 hq1 hq2)
      (not_ftm_mid hσ0 D.ψ_not_isIso hψAB)
      (by rw [hAB]; exact not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU) h0U'
      (not_ftm_suffix hσ0 D.β.2.2.1 D.βW)
      hir hiσn hiA D.U'_not_isIso hiB (D.W_not_isIso hσ.2.2.1) hs
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g ≫ pathVal b₀, by rw [← Category.assoc, hg, hr]⟩)
      (fun ⟨g, hg⟩ ↦ hq1 ⟨g, by rw [hg, hr]⟩) hAU' hU'A
      (fun ⟨g, hg⟩ ↦ D.U'_U hv2 ⟨g, by rw [hg, hAB]⟩) hAr hrA cr1.1 cr2.1
      (fun ⟨g, hg⟩ ↦ hρnW ⟨g, by rw [hg, hr]⟩)
      (fun ⟨g, hg⟩ ↦ (D.W_U hL hR hσ0 hσ.2.2.1).1 ⟨g, by rw [hg, hAB]⟩)
  have hit : ¬IsIso t := fun h ↦ hm1 ⟨D.ψ ≫ inv t, by
    rw [Category.assoc, ← ht, IsIso.inv_hom_id_assoc]; exact D.ψU'⟩
  have h0t : ¬FactorsThroughMorphism σ t := fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 (by
    rw [← ht]; exact FactorsThroughMorphism.comp_right h _))
  have h0σ₂ : ¬FactorsThroughMorphism σ σ₂ := fun h ↦ hσ₂l (hσ.of_factorsThrough hσ₂0 h)
  have htψ : ¬∃ g, g ≫ t = D.ψ := fun ⟨g, hg⟩ ↦ hm1 ⟨g, by
    rw [← ht, ← Category.assoc, hg]; exact D.ψU'⟩
  have hψt : ¬∃ g, g ≫ D.ψ = t := fun ⟨g, hg⟩ ↦ hm2 ⟨g, by
    rw [← ht, ← hg, Category.assoc, D.ψU']⟩
  by_cases htA : t ≫ Am = 0
  swap
  · -- the star `ψ, σ₂' ; a, u₂'`
    exact B.not_s4s hmin hL hR σ hσ.2.1 hσ0 t D.ψ Am D.U' (not_ftm_mid hσ0 D.ψ_not_isIso hψAB)
      h0U' h0t (l6_gap hQ hL hσ hρ D σ₂ hσ₂0 hσ₂l hm1 hm2 t ht Am (pathVal b₀) hAB hiB htA)
      (by rw [ht]; exact h0σ₂) (not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
      (not_ftm_prefix hσ0 hiB (by rw [Category.assoc]; exact hψAB))
      (by rw [D.ψU']; exact not_ftm_long_dom hσ hρ0 hv1) hit D.ψ_not_isIso hiA
      D.U'_not_isIso hAU' hU'A htψ hψt
  by_cases hσρ₂ : FactorsThroughMorphism σ ρ₂
  · -- `ρ₂ ≅ σ`: an arrow `φ` of a contour of `σ` replaces `ρ₂`
    obtain ⟨hx, hy, he⟩ := hσ.2.2.2 ρ₂ hρ₂0 hσρ₂
    subst hx hy
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he
    rw [he] at hs1 hs2
    obtain ⟨T, φ, hφ, hφ2⟩ := B.exists_first_not hmin hL hR hσ (hcont _ hσ) σ₂ hσ₂0 hs2 hs1
    refine B.l6_f617 hmin hL hR hσ hρ hv1 hv2 D ρn hρn0 hρnl hp2 σ₂ hσ₂0 hσ₂l hm1 hm2 hσ₂W'
      Am (pathVal b₀) hAB hiA hβA r hr hrA t ht htA hiB φ
      (not_factorsThrough_irr hσ.2.1 hσ0 hσ.2.2.1 hφ) hφ.2.1 ?_ hφ2 hD617
    rintro ⟨g, hg⟩
    rcases hφ.2.2 _ t g hg.symm with h | h
    · exact hit h
    · exact hφ2 ⟨inv g ≫ D.U', by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩
  by_cases hq : ∃ q, t ≫ q = ρ₂
  swap
  · exact B.l6_f617 hmin hL hR hσ hρ hv1 hv2 D ρn hρn0 hρnl hp2 σ₂ hσ₂0 hσ₂l hm1 hm2 hσ₂W'
      Am (pathVal b₀) hAB hiA hβA r hr hrA t ht htA hiB ρ₂ hσρ₂ hiρ₂ hq hs2 hD617
  obtain ⟨q, hq⟩ := hq
  have hiq : ¬IsIso q := fun h ↦ hs2 ⟨inv q ≫ D.U', by
    rw [← hq, Category.assoc, IsIso.hom_inv_id_assoc, ht]⟩
  have h0q : ¬FactorsThroughMorphism σ q := fun h ↦ hσρ₂ (by
    rw [← hq]; exact FactorsThroughMorphism.comp_left h _)
  have hqU' : ¬∃ g, q ≫ g = D.U' := fun ⟨g, hg⟩ ↦ hs2 ⟨g, by
    rw [← hq, Category.assoc, hg, ht]⟩
  have hU'q : ¬∃ g, D.U' ≫ g = q := fun ⟨g, hg⟩ ↦ hs1 ⟨g, by
    rw [← ht, Category.assoc, hg, hq]⟩
  by_cases hqU : ∃ ξ, q ≫ ξ = D.U
  · -- the star `ψ, σ₂' ; ρ₂', u₂'`
    obtain ⟨ξ, hξ⟩ := hqU
    have hiξ : ¬IsIso ξ := fun h ↦ hρ₂0 (by
      have e1 : q = D.U ≫ inv ξ := by rw [← hξ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [← hq, e1, ← hAB]
      simp only [← Category.assoc, htA, zero_comp])
    exact B.not_s4s hmin hL hR σ hσ.2.1 hσ0 t D.ψ q D.U' h0q h0U' h0t (by rw [hq]; exact hσρ₂)
      (by rw [ht]; exact h0σ₂) (not_ftm_prefix hσ0 D.U_not_isIso D.ψU)
      (not_ftm_prefix hσ0 hiξ (by rw [Category.assoc, hξ]; exact D.ψU))
      (by rw [D.ψU']; exact not_ftm_long_dom hσ hρ0 hv1) hit D.ψ_not_isIso hiq
      D.U'_not_isIso hqU' hU'q htψ hψt
  · -- figure 6.18
    exact B.not_f618 hmin hL hR σ hσ.2.1 hσ0 r (pathVal b₀) Am q D.U'
      (not_ftm_suffix hσ0 hiψA (by rw [Category.assoc]; exact hψAB))
      (fun h ↦ hρnl (hσ.of_factorsThrough hρn0 (by
        rw [← hr]; exact FactorsThroughMorphism.comp_right h _)))
      (by rw [hr]; exact fun h ↦ hρnl (hσ.of_factorsThrough hρn0 h))
      (not_ftm_mid hσ0 D.ψ_not_isIso hψAB)
      (by rw [hAB]; exact not_ftm_suffix hσ0 D.ψ_not_isIso D.ψU) h0q h0U'
      hir hiB hiA hiq D.U'_not_isIso
      (fun ⟨g, hg⟩ ↦ hρ₂0 (by rw [← hq, ← hg, ← Category.assoc, htA, zero_comp])) hAU'
      (fun ⟨g, hg⟩ ↦ hqU ⟨g ≫ pathVal b₀, by rw [← Category.assoc, hg, hAB]⟩)
      (fun ⟨g, hg⟩ ↦ hqU ⟨g, by rw [hg, hAB]⟩) hqU' hU'A
      (fun ⟨g, hg⟩ ↦ D.U'_U hv2 ⟨g, by rw [hg, hAB]⟩) hU'q hAr hrA

end MulBasis

end RayQuiver

end LargeIndecomposable
