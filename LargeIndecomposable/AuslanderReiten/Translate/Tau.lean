module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.RightAlmostSplit

/-!
# The Auslander–Reiten translate and the Auslander–Reiten formula

For a free presentation `Aⁿ¹ → Aⁿ⁰ → Z → 0` with matrix `F`, the translate is `τ_P Z = ker ν F`,
where `ν F : DAⁿ¹ → DAⁿ⁰` is the Nakayama transform. For every module `W`,
`Hom_A(W, τ_P Z) ≅ D(Wⁿ¹ / F Wⁿ⁰)` (`homTauEquiv`), via the Nakayama isomorphism `θ`. When the
presentation is a projective resolution (`Aⁿ¹ → Aⁿ⁰` injective), `Wⁿ¹ / F Wⁿ⁰` is `Ext¹(Z, W)`, so
this is the Auslander–Reiten formula `D Ext¹(Z, W) ≅ Hom(W, τZ)` for `pd Z ≤ 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The translate `τ_P Z = ker ν F` of a presentation matrix. -/
abbrev tauK {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) : Submodule A (Fin n₁ → DA k A) :=
  LinearMap.ker (nu (k := k) F)

variable {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

lemma theta_add {n : ℕ} (φ ψ : W →ₗ[A] (Fin n → DA k A)) : theta (φ + ψ) = theta φ + theta ψ := by
  ext w
  simp [Finset.sum_add_distrib]

lemma theta_zero {n : ℕ} : theta (0 : W →ₗ[A] (Fin n → DA k A)) = 0 := by
  ext w
  simp [DA.ev_zero]

/-- The functionals on `Wⁿ¹` killed by the relations, from maps into `τ_P Z`. -/
def homTauFun {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) (φ : W →ₗ[A] tauK (k := k) F) :
    LinearMap.ker (relMapLin (k := k) (W := W) F).dualMap :=
  ⟨theta ((tauK F).subtype ∘ₗ φ), by
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w ↦ ?_
    rw [LinearMap.dualMap_apply]
    change theta ((tauK F).subtype ∘ₗ φ) (relMap F w) = 0
    rw [← theta_nu_comp]
    have : nu F ∘ₗ ((tauK (k := k) F).subtype ∘ₗ φ) = 0 := by
      ext x : 1
      exact (φ x).2
    rw [this, theta_zero]
    rfl⟩

/-- Maps into `τ_P Z` from functionals on `Wⁿ¹` killed by the relations. -/
def homTauInv {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A)
    (l : LinearMap.ker (relMapLin (k := k) (W := W) F).dualMap) : W →ₗ[A] tauK (k := k) F :=
  LinearMap.codRestrict _ (thetaInv A (l : Module.Dual k (Fin n₁ → W))) fun x ↦ by
    have h : nu F ∘ₗ thetaInv A (l : Module.Dual k (Fin n₁ → W)) = 0 := by
      apply theta_injective
      refine LinearMap.ext fun w ↦ ?_
      rw [theta_nu_comp, theta_thetaInv, theta_zero]
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 l.2) w
      rw [LinearMap.dualMap_apply] at this
      exact this
    exact LinearMap.congr_fun h x

/-- **The Auslander–Reiten formula** (presentation form): `Hom_A(W, τ_P Z)` is in bijection with
the functionals on `Wⁿ¹` killed by the relations, i.e. with `D(Wⁿ¹ / F Wⁿ⁰)`. -/
def homTauEquiv {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) :
    (W →ₗ[A] tauK (k := k) F) ≃ LinearMap.ker (relMapLin (k := k) (W := W) F).dualMap where
  toFun := homTauFun F
  invFun := homTauInv F
  left_inv φ := by
    apply LinearMap.ext; intro x
    apply Subtype.ext
    change thetaInv A (theta ((tauK F).subtype ∘ₗ φ)) x = ((tauK F).subtype ∘ₗ φ) x
    rw [thetaInv_theta]
  right_inv l := by
    apply Subtype.ext
    change theta ((tauK F).subtype ∘ₗ homTauInv F l) = l
    exact theta_thetaInv (l : Module.Dual k (Fin n₁ → W))

lemma homTauFun_add {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) (φ ψ : W →ₗ[A] tauK (k := k) F) :
    homTauFun F (φ + ψ) = homTauFun F φ + homTauFun F ψ := by
  apply Subtype.ext
  change theta ((tauK F).subtype ∘ₗ (φ + ψ)) = theta _ + theta _
  rw [LinearMap.comp_add, theta_add]

lemma homTauFun_smul {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) (c : k)
    (φ : W →ₗ[A] tauK (k := k) F) : homTauFun F (c • φ) = c • homTauFun F φ := by
  apply Subtype.ext
  refine LinearMap.ext fun w ↦ ?_
  change ∑ j, (((c • φ) (w j) : Fin n₁ → DA k A) j).ev 1 = c * ∑ j, ((φ (w j) : Fin n₁ → DA k A) j).ev 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearMap.smul_apply]
  change ((c • (φ (w j) : Fin n₁ → DA k A)) j).ev 1 = _
  rw [Pi.smul_apply, DA.ev_smul]

/-- **The Auslander–Reiten formula**, `k`-linearly. -/
def homTauLEquiv {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) :
    (W →ₗ[A] tauK (k := k) F) ≃ₗ[k] LinearMap.ker (relMapLin (k := k) (W := W) F).dualMap :=
  { homTauEquiv F with
    map_add' := homTauFun_add F
    map_smul' := homTauFun_smul F }

/-- **Dimension form**: `dim Hom(W, τ_P Z) = dim Wⁿ¹ - dim F Wⁿ⁰`. -/
theorem finrank_hom_tauK [FiniteDimensional k W] {n₀ n₁ : ℕ} (F : Fin n₁ → Fin n₀ → A) :
    finrank k (W →ₗ[A] tauK (k := k) F) + finrank k (LinearMap.range (relMapLin (k := k) (W := W) F))
      = finrank k (Fin n₁ → W) := by
  rw [(homTauLEquiv F).finrank_eq, LinearMap.ker_dualMap_eq_dualAnnihilator_range, add_comm]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

end LargeIndecomposable.AR
