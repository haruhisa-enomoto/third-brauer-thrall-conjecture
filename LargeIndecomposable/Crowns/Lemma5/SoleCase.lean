module

public import LargeIndecomposable.Crowns.Lemma5.CaseB
public import LargeIndecomposable.Crowns.Basic.Lemma4c
public import LargeIndecomposable.RayCategories.Opposite.OpAxioms

/-!
# BO13a Lemma 5 a) when the next long morphism is the quotient morphism

If the next long morphism `τ = ρ (p+L+1)` is itself the morphism we quotient
by, the top state of the propagation cannot use the whole rest of a contour
path of `τ`. Following BO13a, take a prefix `v₁` of a contour path through
which `σ (p+L)` factors, maximal (realized here by induction on the length
of the rest `v₂`); Lemma 4 c) shows `v₂` has length at least two, and the
state uses `v₂` without its last arrow (`RayQuiver.MulBasis.lemma5a_top`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A nonzero morphism does not divide a proper prefix of itself. -/
lemma not_ftm_prefix {x y z : P} {τ : x ⟶ z} (hτ0 : τ ≠ 0) {R : x ⟶ y} {Q : y ⟶ z}
    (hQ : ¬IsIso Q) (h : R ≫ Q = τ) : ¬FactorsThroughMorphism τ R := by
  rintro ⟨a, b, hab⟩
  have h2 : τ = a ≫ τ ≫ (b ≫ Q) := by
    calc τ = R ≫ Q := h.symm
      _ = (a ≫ τ ≫ b) ≫ Q := by rw [hab]
      _ = a ≫ τ ≫ (b ≫ Q) := by simp
  obtain ⟨-, hbQ⟩ := IsRayCategory.eq_id_of_two_sided τ hτ0 a _ h2
  have hb0 : b ≠ 0 := fun h0 ↦ IsRayCategory.id_ne_zero z (by rw [← hbQ, h0, zero_comp])
  have hi : IsIso (b ≫ Q) := by rw [hbQ]; infer_instance
  have := isIso_of_isIso_comp b Q hb0 hi
  exact hQ (IsIso.of_isIso_comp_left b Q)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **BO13a Lemma 5 a), the top state when `τ` is the quotient morphism.** -/
theorem lemma5a_top
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (Z : ZChain P) (p L : ℕ) (hτ : IsLong (Z.ρ (p + L + 1)))
    (hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j ≤ L, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    (hle : ∃ (φ : Z.x (p + L + 1) ⟶ Z.x (p + L + 1)) (ψ : Z.z (p + L) ⟶ Z.z (p + L + 1)),
      φ ≫ Z.σ (p + L) ≫ ψ = Z.ρ (p + L + 1)) :
    ∀ (n : ℕ) {w : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (p + L + 1))) w)
      (v₂ : Quiver.Path w (RayVert.mk (Z.z (p + L + 1)))), v₂.length = n → 0 < v₁.length →
      pathVal v₁ ≫ pathVal v₂ = Z.ρ (p + L + 1) →
      ∀ S : w.out ⟶ Z.z (p + L), pathVal v₁ ≫ S = Z.σ (p + L) → False := by
  obtain ⟨φ, ψ, hφψ⟩ := hle
  have hτ0 := hτ.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w v₁ v₂ hn hv₁ hval S hS
  obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c hQ hR (Z.valley₁ (p + L)) (pathVal v₁) (pathVal v₂)
    S hval hS φ ψ (by rw [← Category.assoc] at hφψ ⊢; simpa using hφψ) hτ0
  cases v₂ with
  | nil =>
    have hi : IsIso (d₁ ≫ d₂) := by rw [hd]; exact IsIso.id _
    have hd0 : d₁ ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero _ (by
      have := hd; rw [h, zero_comp] at this; exact this.symm)
    exact hd₁ (isIso_of_isIso_comp d₁ d₂ hd0 hi)
  | cons u' u =>
    rename_i w'
    cases u' with
    | nil =>
      have hu := u.2
      have : pathVal ((Quiver.Path.nil : Quiver.Path w w).cons u) = u.1 := Category.id_comp _
      rw [this] at hd
      rcases hu.2.2 _ d₁ d₂ hd.symm with h | h
      · exact hd₁ h
      · exact hd₂ h
    | cons u'' u₀ =>
      set T := pathVal (u''.cons u₀) with hT
      have hval' : pathVal v₁ ≫ T ≫ u.1 = Z.ρ (p + L + 1) := by
        rw [← hval]; rfl
      have hiR : ¬IsIso (pathVal v₁) := not_isIso_pathVal v₁ hv₁
      have hiT : ¬IsIso T := not_isIso_pathVal _ (by simp)
      have hiu : ¬IsIso u.1 := u.2.2.1
      have hRT : ¬FactorsThroughMorphism (Z.ρ (p + L + 1)) (pathVal v₁ ≫ T) :=
        not_ftm_prefix hτ0 hiu (by rw [Category.assoc]; exact hval')
      refine B.lemma5a_propagation hmin hL hR hτ Z p (L + 1) (fun j hj ↦ hnρ j (by omega))
        (fun j hj ↦ hnσ j (by omega)) F hFi hF01 hFρ L (by omega) (pathVal v₁) S T hS hiR ?_ hiT
        (not_ftm_prefix hτ0 (by
          intro hi
          exact not_isIso_pathVal (u''.cons u₀ |>.cons u) (by simp) hi) hval)
        (not_ftm_right hτ (by rw [hS]; exact Z.σ_ne _) (by rw [hS]; exact hnσ L le_rfl))
        (fun h ↦ hRT (FactorsThroughMorphism.comp_left h _)) hRT ?_ ?_
      · intro h
        exact Z.valley₁ (p + L) ⟨inv S ≫ T ≫ u.1, by
          rw [← hS, Category.assoc, IsIso.hom_inv_id_assoc, hval']⟩
      · rintro ⟨g, hg⟩
        exact Z.valley₁ (p + L) ⟨g ≫ u.1, by
          rw [← hS, Category.assoc, ← Category.assoc S, hg, hval']⟩
      · rintro ⟨g, hg⟩
        refine ih 1 (by simp only [Quiver.Path.length_cons] at hn; omega) (v₁.comp (u''.cons u₀))
          u.toPath rfl (by simp only [Quiver.Path.length_comp]; omega)
          ?_ g ?_
        · rw [pathVal_comp, pathVal_toPath, Category.assoc]
          exact hval'
        · rw [pathVal_comp, Category.assoc]
          change pathVal v₁ ≫ T ≫ g = _
          rw [hg, hS]

end MulBasis

end RayQuiver

end LargeIndecomposable

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P]

/-- A nonzero morphism does not divide a proper suffix of itself. -/
lemma not_ftm_suffix {x y z : P} {τ : x ⟶ z} (hτ0 : τ ≠ 0) {Q : x ⟶ y} {R : y ⟶ z}
    (hQ : ¬IsIso Q) (h : Q ≫ R = τ) : ¬FactorsThroughMorphism τ R := by
  rintro ⟨a, b, hab⟩
  have h2 : τ = (Q ≫ a) ≫ τ ≫ b := by
    calc τ = Q ≫ R := h.symm
      _ = Q ≫ (a ≫ τ ≫ b) := by rw [hab]
      _ = (Q ≫ a) ≫ τ ≫ b := by simp
  obtain ⟨hQa, -⟩ := IsRayCategory.eq_id_of_two_sided τ hτ0 _ b h2
  have hQ0 : Q ≠ 0 := fun h0 ↦ IsRayCategory.id_ne_zero x (by rw [← hQa, h0, zero_comp])
  have hi : IsIso (Q ≫ a) := by rw [hQa]; infer_instance
  exact hQ (isIso_of_isIso_comp Q a hQ0 hi)

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- The propagation entered at a source state with an arbitrary in-leaf `v`. -/
theorem lemma5a_stateB'
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} {μ : a ⟶ b} (hμ : IsLong μ)
    (Z : ZChain P) (p d : ℕ)
    (hnρ : ∀ j ≤ d, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j < d, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    {M X : P} (R' : Z.x (p + d) ⟶ M) (v : X ⟶ M) (S : M ⟶ Z.z (p + d))
    (hR' : R' ≫ S = Z.ρ (p + d)) (hiv : ¬IsIso v) (hiS : ¬IsIso S)
    (hμv : ¬FactorsThroughMorphism μ v) (hμS : ¬FactorsThroughMorphism μ S)
    (hμvS : ¬FactorsThroughMorphism μ (v ≫ S))
    (hrv : ¬∃ g, g ≫ R' = v) (hvr : ¬∃ g, g ≫ v = R') : False := by
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
  have hiR' : ¬IsIso R' := fun h ↦ hrv ⟨v ≫ inv R', by simp⟩
  cases d with
  | zero =>
    have hfρ : ∀ i, ¬∃ g, (F i).2 ≫ g = R' := fun i ⟨g, hg⟩ ↦
      hFρ i ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
    have hfρs : ∀ i, ¬∃ g, (F i).2 ≫ g = R' ≫ S := fun i ↦ by rw [hR']; exact hFρ i
    have hrf : ∀ i, ¬∃ g, R' ≫ g = (F i).2 := fun i ⟨g, hg⟩ ↦ by
      rcases (hFi i).2.2 _ R' g hg.symm with h | h
      · exact hiR' h
      · exact hFρ i ⟨inv g ≫ S, by rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hR']; rfl⟩
    exact B.not_d5 hmin hL hR μ hτ hτ0 (F 0).2 (F 1).2 R' v S (hFμ 0) (hFμ 1) hR'μ hμv hμS
      (by rw [hR']; exact hρμ 0 le_rfl) hμvS (hFi 0).2.1 (hFi 1).2.1 hiR'
      hiv hiS (hFF 0 1 (by decide)) (hFF 1 0 (by decide)) (hfρ 0) (hfρs 0) (hfρ 1) (hfρs 1)
      (hrf 0) (hrf 1) hrv hvr
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
    · refine B.not_zigzag_arm2 hmin hL hR μ hτ hτ0 Z p d F R' v S
        (fun j hj ↦ hρμ j (by omega)) (fun j hj ↦ hσμ j (by omega)) hFμ hR'μ hμv hμS
        (by rw [hR']; exact hρμ (d + 1) le_rfl) hμvS
        (fun i ↦ (hFi i).2.1) hiR' hiv hiS hFF hFρ hρF ?_ hstop2 ?_ hrv hvr
      · rintro ⟨g, hg⟩
        exact Z.valley₁ (p + d) ⟨g ≫ S, by rw [← Category.assoc, hg, hR']; rfl⟩
      · rw [hR']
        exact Z.valley₁ (p + d)

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
/-- **BO13a Lemma 5 a), case `τ = σᵢ` with `τ` the quotient morphism.** Here
`ρ (p+L)` factors through a suffix of a contour path of `τ`; induction on the
length of the prefix (dual Lemma 4 c) excludes prefixes of length ≤ 1). -/
theorem lemma5a_topB
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (Z : ZChain P) (p L : ℕ) (hτ : IsLong (Z.σ (p + L)))
    (hnρ : ∀ j ≤ L, ¬IsLong (Z.ρ (p + j))) (hnσ : ∀ j < L, ¬IsLong (Z.σ (p + j)))
    (F : Fin 2 → BMor (Z.x p)) (hFi : ∀ i, IsIrreducible (F i).2) (hF01 : F 0 ≠ F 1)
    (hFρ : ∀ i, ¬∃ g, (F i).2 ≫ g = Z.ρ p)
    (hle : ∃ (ψ : Z.x (p + L + 1) ⟶ Z.x (p + L)) (φ : Z.z (p + L) ⟶ Z.z (p + L)),
      ψ ≫ Z.ρ (p + L) ≫ φ = Z.σ (p + L)) :
    ∀ (n : ℕ) {w : RayVert P} (v₁ : Quiver.Path (RayVert.mk (Z.x (p + L + 1))) w)
      (v₂ : Quiver.Path w (RayVert.mk (Z.z (p + L)))), v₁.length = n → 0 < v₂.length →
      pathVal v₁ ≫ pathVal v₂ = Z.σ (p + L) →
      ∀ R' : Z.x (p + L) ⟶ w.out, R' ≫ pathVal v₂ = Z.ρ (p + L) → False := by
  obtain ⟨ψ, φ, hψφ⟩ := hle
  have hτ0 := hτ.1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w v₁ v₂ hn hv₂ hval R' hR'
  obtain ⟨m', d₁, d₂, hd, hd₁, hd₂⟩ := lemma4c_dual hQ hL (Z.peak₂ (p + L)) (pathVal v₂)
    (pathVal v₁) R' hval hR' φ ψ hψφ hτ0
  have hiS : ¬IsIso (pathVal v₂) := not_isIso_pathVal v₂ hv₂
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- prefixes of length `0` or `1` are excluded by Lemma 4 c)
    interval_cases n
    · cases v₁ with
      | nil =>
        have hi : IsIso (d₁ ≫ d₂) := by rw [hd]; exact IsIso.id _
        have hd0 : d₁ ≠ 0 := fun h ↦ IsRayCategory.id_ne_zero _ (by
          have := hd; rw [h, zero_comp] at this; exact this.symm)
        exact hd₁ (isIso_of_isIso_comp d₁ d₂ hd0 hi)
      | cons q e => simp at hn
    · obtain ⟨c, a₀, q, hq, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ v₁ hn
      cases q with
      | cons q' e' => simp at hq
      | nil =>
        have : pathVal (a₀.toPath.comp Quiver.Path.nil) = a₀.1 := by
          simp [pathVal_toPath]
        rw [this] at hd
        rcases a₀.2.2.2 _ d₁ d₂ hd.symm with h | h
        · exact hd₁ h
        · exact hd₂ h
  · obtain ⟨c, a₀, q, hq, rfl⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ v₁
      (n := n - 1) (by omega)
    set v := pathVal q with hv
    have hval' : a₀.1 ≫ v ≫ pathVal v₂ = Z.σ (p + L) := by
      rw [← hval, pathVal_comp, pathVal_toPath, Category.assoc]
    have hiv : ¬IsIso v := not_isIso_pathVal q (by omega)
    have hia : ¬IsIso a₀.1 := a₀.2.2.1
    have hvS : ¬FactorsThroughMorphism (Z.σ (p + L)) (v ≫ pathVal v₂) :=
      not_ftm_suffix hτ0 hia hval'
    refine B.lemma5a_stateB' hmin hL hR hτ Z p L hnρ hnσ F hFi hF01 hFρ R' v (pathVal v₂) hR' hiv
      hiS (fun h ↦ hvS (FactorsThroughMorphism.comp_right h _))
      (not_ftm_suffix hτ0 (by
        intro hi
        exact not_isIso_pathVal (a₀.toPath.comp q) (by simp) hi) hval) hvS ?_ ?_
    · rintro ⟨g, hg⟩
      exact Z.peak₂ (p + L) ⟨a₀.1 ≫ g, by rw [Category.assoc, hR'.symm, ← Category.assoc g, hg,
        hval']⟩
    · rintro ⟨g, hg⟩
      refine ih 1 (by omega) a₀.toPath (q.comp v₂) rfl (by simp only [Quiver.Path.length_comp]; omega)
        ?_ g ?_
      · rw [pathVal_comp, pathVal_toPath]
        exact hval'
      · rw [pathVal_comp, ← Category.assoc, hg, hR']

end MulBasis

end RayQuiver

end LargeIndecomposable
