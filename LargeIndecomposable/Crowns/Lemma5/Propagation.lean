module

public import LargeIndecomposable.Cleaving.Zigzags.ZigzagArm2
public import LargeIndecomposable.Crowns.Lemma5.Statement

/-!
# BO13a Lemma 5 a): the factorization propagation

Let `μ` be long and let the chain morphisms `ρ (p+j), σ (p+j)` (`j < N`) be
non-long. Suppose two distinct arrows out of `x p` do not divide `ρ p`. A
"state" at depth `d` is an object `M` with `R : x (p+d+1) → M`,
`S : M → z (p+d)`, `T : M → E`, `σ (p+d) = R ≫ S`, satisfying non-factoring
conditions. Every state is contradictory
(`RayQuiver.MulBasis.lemma5a_propagation`): either `ρ (p+d)` does not factor
through `S` (BO13a figures 5.2, 5.3), or `ρ (p+d) = R' ≫ S` and then
`σ (p+d-1)` does not factor through `R'` (figure 5.4), or we descend to a
state at depth `d − 1`, or we reach `x p` (the `D̃₅` case).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P]

lemma FactorsThroughMorphism.comp_right {a b x y z : P} {μ : a ⟶ b} {f : x ⟶ y}
    (h : FactorsThroughMorphism μ f) (g : y ⟶ z) : FactorsThroughMorphism μ (f ≫ g) := by
  obtain ⟨c, d, rfl⟩ := h
  exact ⟨c, d ≫ g, by simp⟩

lemma FactorsThroughMorphism.comp_left {a b x y z : P} {μ : a ⟶ b} {g : y ⟶ z}
    (h : FactorsThroughMorphism μ g) (f : x ⟶ y) : FactorsThroughMorphism μ (f ≫ g) := by
  obtain ⟨c, d, rfl⟩ := h
  exact ⟨f ≫ c, d, by simp⟩

/-- A factor of a nonzero non-long morphism is not divisible by a long one. -/
lemma not_ftm_left {a b x y z : P} {μ : a ⟶ b} (hμ : IsLong μ) {f : x ⟶ y} {g : y ⟶ z}
    (h0 : f ≫ g ≠ 0) (hl : ¬IsLong (f ≫ g)) : ¬FactorsThroughMorphism μ f := fun h ↦
  hl (hμ.of_factorsThrough h0 (FactorsThroughMorphism.comp_right h g))

lemma not_ftm_right {a b x y z : P} {μ : a ⟶ b} (hμ : IsLong μ) {f : x ⟶ y} {g : y ⟶ z}
    (h0 : f ≫ g ≠ 0) (hl : ¬IsLong (f ≫ g)) : ¬FactorsThroughMorphism μ g := fun h ↦
  hl (hμ.of_factorsThrough h0 (FactorsThroughMorphism.comp_left h f))

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), the propagation.** Every state is contradictory. -/
theorem lemma5a_propagation
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (Z : ZChain P) (p N : ℕ)
    (hnρ : ∀ j < N, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j < N, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p) :
    ∀ d, d < N → ∀ {M E : P} (R : Z.x (p + d + 1) ⟶ M) (S : M ⟶ Z.z (p + d)) (T : M ⟶ E),
      R ≫ S = Z.σ (p + d) → ¬IsIso R → ¬IsIso S → ¬IsIso T →
      ¬FactorsThroughMorphism μ R → ¬FactorsThroughMorphism μ S →
      ¬FactorsThroughMorphism μ T → ¬FactorsThroughMorphism μ (R ≫ T) →
      (¬∃ g, S ≫ g = T) → (¬∃ g, T ≫ g = S) → False := by
  have hτ := hμ.2.1
  have hτ0 := hμ.1
  have hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2 := fun i i' hii' hg ↦ by
    have := eq_of_bLe_irr (hFi i) (hFi i') hg
    fin_cases i <;> fin_cases i' <;> simp_all
  have hFμ : ∀ i, ¬FactorsThroughMorphism μ (F i).2 :=
    fun i ↦ not_factorsThrough_irr hτ hτ0 hμ.2.2.1 (hFi i)
  have hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2 :=
    fun i ↦ not_comp_eq_irr (hFi i) (Z.ρ_not_isIso p) (hFρ i)
  have hρμ : ∀ j < N, ¬FactorsThroughMorphism μ (Z.ρ (p + j)) :=
    fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.ρ_ne _) (hnρ j hj)
  have hσμ : ∀ j < N, ¬FactorsThroughMorphism μ (Z.σ (p + j)) :=
    fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.σ_ne _) (hnσ j hj)
  -- the arm at a sink (figures 5.2, 5.3): available at every depth
  have arm : ∀ d, d < N → ∀ {M E : P} (R : Z.x (p + d + 1) ⟶ M) (S : M ⟶ Z.z (p + d))
      (T : M ⟶ E), R ≫ S = Z.σ (p + d) → ¬IsIso R → ¬IsIso S → ¬IsIso T →
      ¬FactorsThroughMorphism μ R → ¬FactorsThroughMorphism μ S →
      ¬FactorsThroughMorphism μ T → ¬FactorsThroughMorphism μ (R ≫ T) →
      (¬∃ g, S ≫ g = T) → (¬∃ g, T ≫ g = S) → (¬∃ g, g ≫ S = Z.ρ (p + d)) → False := by
    intro d hd M E R S T hRS hiR hiS hiT hμR hμS hμT hμRT hST hTS hstop
    refine B.not_zigzag_arm hmin hL hR μ hτ hτ0 Z p d F S R T hRS
      (fun j hj ↦ hρμ j (by omega)) (fun j hj ↦ hσμ j (by omega)) (hσμ d hd) hFμ hμS hμR hμT
      hμRT (fun i ↦ (hFi i).2.1) hiS hiR hiT hFF hFρ hρF hST hTS ?_ hstop
    rintro ⟨g, hg⟩
    exact Z.peak₂ (p + d) ⟨R ≫ g, by rw [Category.assoc, hg, hRS]⟩
  intro d
  induction d with
  | zero =>
    intro hd M E R S T hRS hiR hiS hiT hμR hμS hμT hμRT hST hTS
    by_cases hstop : ∃ g, g ≫ S = Z.ρ (p + 0)
    · obtain ⟨R', hR'⟩ := hstop
      have hR'μ : ¬FactorsThroughMorphism μ R' :=
        not_ftm_left hμ (by rw [hR']; exact Z.ρ_ne _) (by rw [hR']; exact hnρ 0 hd)
      have hiR' : ¬IsIso R' := fun h ↦ Z.peak₂ (p + 0) ⟨R ≫ inv R', by
        rw [← hR', Category.assoc, IsIso.inv_hom_id_assoc, hRS]⟩
      have hfρ : ∀ i, ¬∃ g, (F i).2 ≫ g = R' := fun i ⟨g, hg⟩ ↦
        hFρ i ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
      have hfρs : ∀ i, ¬∃ g, (F i).2 ≫ g = R' ≫ S := fun i ↦ by rw [hR']; exact hFρ i
      have hrf : ∀ i, ¬∃ g, R' ≫ g = (F i).2 := fun i ⟨g, hg⟩ ↦ by
        rcases (hFi i).2.2 _ R' g hg.symm with h | h
        · exact hiR' h
        · exact hFρ i ⟨inv g ≫ S, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hR']; rfl⟩
      refine B.not_d5 hmin hL hR μ hτ hτ0 (F 0).2 (F 1).2 R' R S (hFμ 0) (hFμ 1) hR'μ hμR hμS
        (by rw [hR']; exact hρμ 0 hd) (by rw [hRS]; exact hσμ 0 hd) (hFi 0).2.1 (hFi 1).2.1 hiR'
        hiR hiS (hFF 0 1 (by decide)) (hFF 1 0 (by decide)) (hfρ 0) (hfρs 0) (hfρ 1) (hfρs 1)
        (hrf 0) (hrf 1) ?_ ?_
      · rintro ⟨g, hg⟩
        exact Z.peak₂ (p + 0) ⟨g, by rw [← hR', ← Category.assoc, hg, hRS]⟩
      · rintro ⟨g, hg⟩
        exact Z.peak₁ (p + 0) ⟨g, by rw [← hRS, ← Category.assoc, hg, hR']⟩
    · exact arm 0 hd R S T hRS hiR hiS hiT hμR hμS hμT hμRT hST hTS hstop
  | succ d ih =>
    intro hd M E R S T hRS hiR hiS hiT hμR hμS hμT hμRT hST hTS
    by_cases hstop : ∃ g, g ≫ S = Z.ρ (p + (d + 1))
    · obtain ⟨R', hR'⟩ := hstop
      have hR'μ : ¬FactorsThroughMorphism μ R' :=
        not_ftm_left hμ (by rw [hR']; exact Z.ρ_ne _) (by rw [hR']; exact hnρ (d + 1) hd)
      have hiR' : ¬IsIso R' := fun h ↦ Z.peak₂ (p + (d + 1)) ⟨R ≫ inv R', by
        rw [← hR', Category.assoc, IsIso.inv_hom_id_assoc, hRS]⟩
      by_cases hstop2 : ∃ g, R' ≫ g = Z.σ (p + d)
      · obtain ⟨S'', hS''⟩ := hstop2
        refine ih (by omega) R' S'' S hS'' hiR' ?_ hiS
          (not_ftm_left hμ (by rw [hS'']; exact Z.σ_ne _) (by rw [hS'']; exact hnσ d (by omega)))
          (not_ftm_right hμ (by rw [hS'']; exact Z.σ_ne _) (by rw [hS'']; exact hnσ d (by omega)))
          hμS (by rw [hR']; exact hρμ (d + 1) hd) ?_ ?_
        · intro h
          exact Z.valley₁ (p + d) ⟨inv S'' ≫ S, by
            rw [← hS'', Category.assoc, IsIso.hom_inv_id_assoc, hR']; rfl⟩
        · rintro ⟨g, hg⟩
          exact Z.valley₁ (p + d) ⟨g, by rw [← hS'', Category.assoc, hg, hR']; rfl⟩
        · rintro ⟨g, hg⟩
          exact Z.valley₂ (p + d) ⟨g, by
            show Z.ρ (p + (d + 1)) ≫ g = _
            rw [← hR', Category.assoc, hg, hS'']⟩
      · refine B.not_zigzag_arm2 hmin hL hR μ hτ hτ0 Z p d F R' R S
          (fun j hj ↦ hρμ j (by omega)) (fun j hj ↦ hσμ j (by omega)) hFμ hR'μ hμR hμS
          (by rw [hR']; exact hρμ (d + 1) hd) (by rw [hRS]; exact hσμ (d + 1) hd)
          (fun i ↦ (hFi i).2.1) hiR' hiR hiS hFF hFρ hρF ?_ hstop2 ?_ ?_ ?_
        · rintro ⟨g, hg⟩
          exact Z.valley₁ (p + d) ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
        · rw [hR']
          exact Z.valley₁ (p + d)
        · rintro ⟨g, hg⟩
          exact Z.peak₂ (p + (d + 1)) ⟨g, by rw [← hR', ← Category.assoc, hg, hRS]⟩
        · rintro ⟨g, hg⟩
          exact Z.peak₁ (p + (d + 1)) ⟨g, by rw [← hRS, ← Category.assoc, hg, hR']⟩
    · exact arm (d + 1) hd R S T hRS hiR hiS hiT hμR hμS hμT hμRT hST hTS hstop

end MulBasis

end RayQuiver

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- An irreducible morphism followed by an isomorphism is irreducible. -/
lemma IsIrreducible.comp_isIso {x y z : P} {α : x ⟶ y} (hα : IsIrreducible α) (T : y ⟶ z)
    [IsIso T] : IsIrreducible (α ≫ T) := by
  refine ⟨fun h ↦ hα.1 (by simpa using congrArg (· ≫ inv T) h), fun h ↦ hα.2.1 ?_, ?_⟩
  · have : IsIso ((α ≫ T) ≫ inv T) := inferInstance
    simpa using this
  · intro w g h he
    rcases hα.2.2 w g (h ≫ inv T) (by rw [← Category.assoc, ← he]; simp) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by simpa using (inferInstance : IsIso ((h ≫ inv T) ≫ T)))

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), case `τ = ρᵢ`.** Let `μ` be long, the chain morphisms
`ρ (p+j), σ (p+j)` (`j ≤ L`) non-long, and `τ = ρ (p+L+1)` not divisible by
`μ` and not irreducible. Let `F` be two distinct arrows out of `x p` not dividing
`ρ p`, and `G` two distinct arrows out of `x (p+L+1)` each dividing `τ`. Then we
get a contradiction. -/
theorem lemma5a_caseA
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (Z : ZChain P) (p L : ℕ)
    (hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j ≤ L, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    (G : Fin 2 → BMor (Z.x (p + L + 1))) (hGi : ∀ i, IsIrreducible (G i).2) (hG01 : G 0 ≠ G 1)
    (hGτ : ∀ i, ∃ t, (G i).2 ≫ t = Z.ρ (p + L + 1))
    (hτμ : ¬FactorsThroughMorphism μ (Z.ρ (p + L + 1)))
    (hτr : ¬IsIrreducible (Z.ρ (p + L + 1))) : False := by
  by_cases hσG : ∃ i, ∃ g, (G i).2 ≫ g = Z.σ (p + L)
  · obtain ⟨i, S, hS⟩ := hσG
    obtain ⟨T, hT⟩ := hGτ i
    have hσ0 := Z.σ_ne (p + L)
    refine B.lemma5a_propagation hmin hL hR hμ Z p (L + 1) (fun j hj ↦ hnρ j (by omega))
      (fun j hj ↦ hnσ j (by omega)) F hFi hF01 hFρ L (by omega) (G i).2 S T hS (hGi i).2.1 ?_ ?_
      (not_factorsThrough_irr hμ.2.1 hμ.1 hμ.2.2.1 (hGi i))
      (not_ftm_right hμ (by rw [hS]; exact hσ0) (by rw [hS]; exact hnσ L le_rfl))
      (fun h ↦ hτμ (by rw [← hT]; exact FactorsThroughMorphism.comp_left h _))
      (by rw [hT]; exact hτμ) ?_ ?_
    · intro h
      exact Z.valley₁ (p + L) ⟨inv S ≫ T, by rw [← hS, Category.assoc, IsIso.hom_inv_id_assoc, hT]⟩
    · intro h
      exact hτr (by rw [← hT]; exact IsIrreducible.comp_isIso (hGi i) T)
    · rintro ⟨g, hg⟩
      exact Z.valley₁ (p + L) ⟨g, by rw [← hS, Category.assoc, hg, hT]⟩
    · rintro ⟨g, hg⟩
      exact Z.valley₂ (p + L) ⟨g, by rw [← hT, Category.assoc, hg, hS]⟩
  · push_neg at hσG
    exact B.not_zigzag_arrow_forks hmin hL hR μ hμ.2.1 hμ.1 hμ.2.2.1 Z p L F G hFi hGi hF01 hG01
      (fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.ρ_ne _) (hnρ j hj))
      (fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.σ_ne _) (hnσ j hj)) hFρ
      (fun i ⟨g, hg⟩ ↦ hσG i g hg)

end MulBasis

end RayQuiver

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), entering the propagation at a source.** A state at the
source `x (p+d)`: `R' : x (p+d) → M`, `R : x (p+d+1) → M`, `S : M → z (p+d)`
with `ρ (p+d) = R' ≫ S`, `σ (p+d) = R ≫ S`, is contradictory, provided the
chain morphisms before position `p+d` are non-long and `ρ (p+d)` too. -/
theorem lemma5a_stateB
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (Z : ZChain P) (p d : ℕ)
    (hnρ : ∀ j ≤ d, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j < d, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    {M : P} (R' : Z.x (p + d) ⟶ M) (R : Z.x (p + d + 1) ⟶ M) (S : M ⟶ Z.z (p + d))
    (hR' : R' ≫ S = Z.ρ (p + d)) (hRS : R ≫ S = Z.σ (p + d))
    (hiR : ¬IsIso R) (hiS : ¬IsIso S) (hμR : ¬FactorsThroughMorphism μ R)
    (hμS : ¬FactorsThroughMorphism μ S) (hμRS : ¬FactorsThroughMorphism μ (R ≫ S)) : False := by
  have hτ := hμ.2.1
  have hτ0 := hμ.1
  have hFF : ∀ i i', i ≠ i' → ¬∃ g, (F i).2 ≫ g = (F i').2 := fun i i' hii' hg ↦ by
    have := eq_of_bLe_irr (hFi i) (hFi i') hg
    fin_cases i <;> fin_cases i' <;> simp_all
  have hFμ : ∀ i, ¬FactorsThroughMorphism μ (F i).2 :=
    fun i ↦ not_factorsThrough_irr hτ hτ0 hμ.2.2.1 (hFi i)
  have hρF : ∀ i, ¬∃ g, Z.ρ p ≫ g = (F i).2 :=
    fun i ↦ not_comp_eq_irr (hFi i) (Z.ρ_not_isIso p) (hFρ i)
  have hρμ : ∀ j ≤ d, ¬FactorsThroughMorphism μ (Z.ρ (p + j)) :=
    fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.ρ_ne _) (hnρ j hj)
  have hσμ : ∀ j < d, ¬FactorsThroughMorphism μ (Z.σ (p + j)) :=
    fun j hj ↦ not_factorsThrough_of_not_isLong hμ (Z.σ_ne _) (hnσ j hj)
  have hR'μ : ¬FactorsThroughMorphism μ R' :=
    not_ftm_left hμ (by rw [hR']; exact Z.ρ_ne _) (by rw [hR']; exact hnρ d le_rfl)
  have hiR' : ¬IsIso R' := fun h ↦ Z.peak₂ (p + d) ⟨R ≫ inv R', by
    rw [← hR', Category.assoc, IsIso.inv_hom_id_assoc, hRS]⟩
  cases d with
  | zero =>
    have hfρ : ∀ i, ¬∃ g, (F i).2 ≫ g = R' := fun i ⟨g, hg⟩ ↦
      hFρ i ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
    have hfρs : ∀ i, ¬∃ g, (F i).2 ≫ g = R' ≫ S := fun i ↦ by rw [hR']; exact hFρ i
    have hrf : ∀ i, ¬∃ g, R' ≫ g = (F i).2 := fun i ⟨g, hg⟩ ↦ by
      rcases (hFi i).2.2 _ R' g hg.symm with h | h
      · exact hiR' h
      · exact hFρ i ⟨inv g ≫ S, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hR']; rfl⟩
    refine B.not_d5 hmin hL hR μ hτ hτ0 (F 0).2 (F 1).2 R' R S (hFμ 0) (hFμ 1) hR'μ hμR hμS
      (by rw [hR']; exact hρμ 0 le_rfl) hμRS (hFi 0).2.1 (hFi 1).2.1 hiR'
      hiR hiS (hFF 0 1 (by decide)) (hFF 1 0 (by decide)) (hfρ 0) (hfρs 0) (hfρ 1) (hfρs 1)
      (hrf 0) (hrf 1) ?_ ?_
    · rintro ⟨g, hg⟩
      exact Z.peak₂ (p + 0) ⟨g, by rw [← hR', ← Category.assoc, hg, hRS]⟩
    · rintro ⟨g, hg⟩
      exact Z.peak₁ (p + 0) ⟨g, by rw [← hRS, ← Category.assoc, hg, hR']⟩
  | succ d =>
    by_cases hstop2 : ∃ g, R' ≫ g = Z.σ (p + d)
    · obtain ⟨S'', hS''⟩ := hstop2
      refine B.lemma5a_propagation hmin hL hR hμ Z p (d + 1) (fun j hj ↦ hnρ j (by omega))
        (fun j hj ↦ hnσ j (by omega)) F hFi hF01 hFρ d (by omega) R' S'' S hS'' hiR' ?_ hiS
        (not_ftm_left hμ (by rw [hS'']; exact Z.σ_ne _) (by rw [hS'']; exact hnσ d (by omega)))
        (not_ftm_right hμ (by rw [hS'']; exact Z.σ_ne _) (by rw [hS'']; exact hnσ d (by omega)))
        hμS (by rw [hR']; exact hρμ (d + 1) le_rfl) ?_ ?_
      · intro h
        exact Z.valley₁ (p + d) ⟨inv S'' ≫ S, by
          rw [← hS'', Category.assoc, IsIso.hom_inv_id_assoc, hR']; rfl⟩
      · rintro ⟨g, hg⟩
        exact Z.valley₁ (p + d) ⟨g, by rw [← hS'', Category.assoc, hg, hR']; rfl⟩
      · rintro ⟨g, hg⟩
        exact Z.valley₂ (p + d) ⟨g, by
          show Z.ρ (p + (d + 1)) ≫ g = _
          rw [← hR', Category.assoc, hg, hS'']⟩
    · refine B.not_zigzag_arm2 hmin hL hR μ hτ hτ0 Z p d F R' R S
        (fun j hj ↦ hρμ j (by omega)) (fun j hj ↦ hσμ j (by omega)) hFμ hR'μ hμR hμS
        (by rw [hR']; exact hρμ (d + 1) le_rfl) hμRS
        (fun i ↦ (hFi i).2.1) hiR' hiR hiS hFF hFρ hρF ?_ hstop2 ?_ ?_ ?_
      · rintro ⟨g, hg⟩
        exact Z.valley₁ (p + d) ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
      · rw [hR']
        exact Z.valley₁ (p + d)
      · rintro ⟨g, hg⟩
        exact Z.peak₂ (p + (d + 1)) ⟨g, by rw [← hR', ← Category.assoc, hg, hRS]⟩
      · rintro ⟨g, hg⟩
        exact Z.peak₁ (p + (d + 1)) ⟨g, by rw [← hRS, ← Category.assoc, hg, hR']⟩

end MulBasis

end RayQuiver

end LargeIndecomposable
