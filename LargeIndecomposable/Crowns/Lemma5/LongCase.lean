module

public import LargeIndecomposable.Crowns.Lemma5.DualNeighbour

/-!
# BO13a Lemma 5 a) for a long `ρ`

Reading a crown backwards (`Crown.rev`) exchanges the roles of the `ρ`'s and
the `σ`'s. From `lemma5a_mk` and `lemma5a_last_mk` we get: if `ρ (t+1)` is
long, then `σ t` factors through a first arrow of any contour of `ρ (t+1)`
(`MulBasis.lemma5a_rho_first`); if `ρ t` is long, then `σ t` factors through
a last arrow (`MulBasis.lemma5a_rho_last`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat LargeIndecomposable

universe u

namespace RayCat

lemma idx_revA (n T : ℕ) (hn : 0 < n) :
    2 * n * (2 * (n * (2 * T + 1) - T) + 1 + 1) + 1 - (2 * (n * (2 * T + 1) - T) + 1) =
      2 * T + 2 * n * (2 * (n * (2 * T + 1) - T) + 2 - (2 * T + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = n * (2 * T + 1) := ⟨_, rfl⟩
  rw [← hN]
  have hle : 2 * T + 1 ≤ N := hN ▸ Nat.le_mul_of_pos_left _ hn
  generalize hK : 2 * (N - T) + 2 - (2 * T + 1) = K
  have e : 2 * (N - T) + 1 + 1 = K + (2 * T + 1) := by omega
  have key : 2 * n * (K + (2 * T + 1)) = 2 * n * K + 2 * N := by rw [mul_add, hN]; ring
  rw [e, key]
  omega

lemma idx_revB (n T : ℕ) (hn : 0 < n) :
    2 * n * (2 * (n * (2 * T + 1) - T) + 1) + 1 - 2 * (n * (2 * T + 1) - T) =
      2 * T + 1 + 2 * n * (2 * (n * (2 * T + 1) - T) + 1 - (2 * T + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = n * (2 * T + 1) := ⟨_, rfl⟩
  rw [← hN]
  have hle : 2 * T + 1 ≤ N := hN ▸ Nat.le_mul_of_pos_left _ hn
  generalize hK : 2 * (N - T) + 1 - (2 * T + 1) = K
  have e : 2 * (N - T) + 1 = K + (2 * T + 1) := by omega
  have key : 2 * n * (K + (2 * T + 1)) = 2 * n * K + 2 * N := by rw [mul_add, hN]; ring
  rw [e, key]
  omega

lemma idx_revC (n t : ℕ) (hn : 0 < n) :
    2 * n * (2 * (n * (2 * (t + 1) + 1) - (t + 1) + 1) + 1) + 1 -
        2 * (n * (2 * (t + 1) + 1) - (t + 1) + 1) =
      2 * t + 1 + 2 * n * (2 * (n * (2 * (t + 1) + 1) - (t + 1)) + 3 - (2 * (t + 1) + 1)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = n * (2 * (t + 1) + 1) := ⟨_, rfl⟩
  rw [← hN]
  have hle : 2 * (t + 1) + 1 ≤ N := hN ▸ Nat.le_mul_of_pos_left _ hn
  generalize hK : 2 * (N - (t + 1)) + 3 - (2 * (t + 1) + 1) = K
  have e : 2 * (N - (t + 1) + 1) + 1 = K + (2 * (t + 1) + 1) := by omega
  have key : 2 * n * (K + (2 * (t + 1) + 1)) = 2 * n * K + 2 * N := by rw [mul_add, hN]; ring
  have hK1 : 1 ≤ K := by omega
  have hnK : 2 ≤ 2 * n * K := by nlinarith
  rw [e, key]
  omega

end RayCat

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- `lemma5a_last` with the chain morphisms given by `RayMor` equations. -/
theorem lemma5a_last_mk
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (s : ℕ) {X Y X' : P} {σ : X ⟶ Y} {ρ : X' ⟶ Y}
    (hσe : (⟨_, _, C.toZChain.σ s⟩ : RayMor P) = ⟨X, Y, σ⟩)
    (hρe : (⟨_, _, C.toZChain.ρ s⟩ : RayMor P) = ⟨X', Y, ρ⟩) (hσ : IsLong σ)
    {a₁ b₁ : RayVert P} (α : a₁ ⟶ RayVert.mk Y) (β : b₁ ⟶ RayVert.mk Y)
    (v' : Quiver.Path (RayVert.mk X) a₁) (w' : Quiver.Path (RayVert.mk X) b₁)
    (hv : pathVal (v'.cons α) = σ) (hw : pathVal (w'.cons β) = σ)
    (hni : ¬Interlaced (v'.cons α) (w'.cons β))
    (hα : ¬∃ g, g ≫ α.1 = ρ) (hβ : ¬∃ g, g ≫ β.1 = ρ) : False := by
  cases hσe
  cases hρe
  exact B.lemma5a_last hmin hL hR hQ hcont C s hσ α β v' w' hv hw hni hα hβ

include B in
/-- **BO13a Lemma 5 a) for a long `ρ t`**: `σ t` factors through a last arrow
of any contour of `ρ t`. -/
theorem lemma5a_rho_last
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (t : ℕ) (hρ : IsLong (C.toZChain.ρ t)) {a₁ b₁ : RayVert P}
    (α : a₁ ⟶ RayVert.mk (C.toZChain.z t)) (β : b₁ ⟶ RayVert.mk (C.toZChain.z t))
    (v' : Quiver.Path (RayVert.mk (C.toZChain.x t)) a₁)
    (w' : Quiver.Path (RayVert.mk (C.toZChain.x t)) b₁)
    (hv : pathVal (v'.cons α) = C.toZChain.ρ t) (hw : pathVal (w'.cons β) = C.toZChain.ρ t)
    (hni : ¬Interlaced (v'.cons α) (w'.cons β))
    (hα : ¬∃ g, g ≫ α.1 = C.toZChain.σ t) (hβ : ¬∃ g, g ≫ β.1 = C.toZChain.σ t) : False := by
  have hn := C.hn
  set t' := C.n * (2 * t + 1) - t with ht'
  have eσ : (⟨_, _, C.rev.toZChain.σ t'⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ t⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    change C.f (2 * C.n * (2 * t' + 1 + 1) + 1 - (2 * t' + 1)) = _
    rw [ht', idx_revA C.n t hn, C.f_add_mul]
  have eρ : (⟨_, _, C.rev.toZChain.ρ t'⟩ : RayMor P) = ⟨_, _, C.toZChain.σ t⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    change C.f (2 * C.n * (2 * t' + 1) + 1 - 2 * t') = _
    rw [ht', idx_revB C.n t hn, C.f_add_mul]
  exact B.lemma5a_last_mk hmin hL hR hQ hcont C.rev t' eσ eρ hρ α β v' w' hv hw hni hα hβ

include B in
/-- **BO13a Lemma 5 a) for a long `ρ (t+1)`**: `σ t` factors through a first
arrow of any contour of `ρ (t+1)`. -/
theorem lemma5a_rho_first
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) (hQ : OneSidedCyclic P)
    (hcont : ∀ {a b : P} (μ : a ⟶ b), IsLong μ → ¬NotInContour μ)
    (C : Crown P) (t : ℕ) (hρ : IsLong (C.toZChain.ρ (t + 1))) {a₁ b₁ : RayVert P}
    (α : RayVert.mk (C.toZChain.x (t + 1)) ⟶ a₁) (β : RayVert.mk (C.toZChain.x (t + 1)) ⟶ b₁)
    (v' : Quiver.Path a₁ (RayVert.mk (C.toZChain.z (t + 1))))
    (w' : Quiver.Path b₁ (RayVert.mk (C.toZChain.z (t + 1))))
    (hv : pathVal (α.toPath.comp v') = C.toZChain.ρ (t + 1))
    (hw : pathVal (β.toPath.comp w') = C.toZChain.ρ (t + 1))
    (hni : ¬Interlaced (α.toPath.comp v') (β.toPath.comp w'))
    (hα : ¬∃ g, α.1 ≫ g = C.toZChain.σ t) (hβ : ¬∃ g, β.1 ≫ g = C.toZChain.σ t) : False := by
  have hn := C.hn
  set t' := C.n * (2 * (t + 1) + 1) - (t + 1) with ht'
  have eσ : (⟨_, _, C.rev.toZChain.σ t'⟩ : RayMor P) = ⟨_, _, C.toZChain.ρ (t + 1)⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    change C.f (2 * C.n * (2 * t' + 1 + 1) + 1 - (2 * t' + 1)) = _
    rw [ht', idx_revA C.n (t + 1) hn, C.f_add_mul]
  have eρ : (⟨_, _, C.rev.toZChain.ρ (t' + 1)⟩ : RayMor P) = ⟨_, _, C.toZChain.σ t⟩ := by
    rw [Crown.toZChain_σ, Crown.toZChain_ρ]
    change C.f (2 * C.n * (2 * (t' + 1) + 1) + 1 - 2 * (t' + 1)) = _
    rw [ht', idx_revC C.n t hn, C.f_add_mul]
  have hnext : ∃ j, IsLong (C.rev.toZChain.σ (t' + 1 + j)) := by
    refine ⟨C.n - 1, ?_⟩
    have h := Crown.isLong_σ_add C.rev t' (isLong_of_rayMor_eq eσ.symm hρ)
    rwa [show t' + 1 + (C.n - 1) = t' + C.rev.n by change _ = t' + C.n; omega]
  exact B.lemma5a_mk hmin hL hR hQ hcont C.rev.toZChain t' eσ eρ hρ hnext α β v' w' hv hw hni
    hα hβ

end MulBasis

end RayQuiver

end LargeIndecomposable
