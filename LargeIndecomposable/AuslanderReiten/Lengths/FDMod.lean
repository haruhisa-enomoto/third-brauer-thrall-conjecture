module

public import LargeIndecomposable.AuslanderReiten.Lengths.HaradaSai

/-!
# The category of finite-dimensional modules; the Harada–Sai lemma

`FDMod k A`: `A`-modules that are finite-dimensional over `k`, with `A`-linear maps.

`haradaSai`: in a chain `X₀ → X₁ → ⋯ → X_m` of indecomposables of dimension `≤ b` whose
maps are not bijective, the composite is zero once `m ≥ 2ᵇ − 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]

/-- A finite-dimensional `A`-module. -/
structure FDMod where
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isModuleK : Module k carrier]
  [isScalarTower : IsScalarTower k A carrier]
  [isFD : FiniteDimensional k carrier]

attribute [instance] FDMod.isAddCommGroup FDMod.isModule FDMod.isModuleK FDMod.isScalarTower
  FDMod.isFD

namespace FDMod

variable {k A}

instance : CoeSort (FDMod k A) (Type u) := ⟨FDMod.carrier⟩

instance : Category (FDMod k A) where
  Hom X Y := X →ₗ[A] Y
  id X := LinearMap.id
  comp f g := g ∘ₗ f

lemma comp_def {X Y Z : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (show Y →ₗ[A] Z from g) ∘ₗ (show X →ₗ[A] Y from f) := rfl

lemma id_def (X : FDMod k A) : 𝟙 X = (LinearMap.id : X →ₗ[A] X) := rfl

/-- The underlying linear map. -/
def lin {X Y : FDMod k A} (f : X ⟶ Y) : X →ₗ[A] Y := f

@[simp] lemma lin_comp {X Y Z : FDMod k A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lin (f ≫ g) = lin g ∘ₗ lin f := rfl

@[simp] lemma lin_id (X : FDMod k A) : lin (𝟙 X) = LinearMap.id := rfl

end FDMod

variable {k A}

/-- **The Harada–Sai lemma.** -/
theorem haradaSai {b m : ℕ} (F : ComposableArrows (FDMod k A) m)
    (hind : ∀ i, IsIndecMod A (F.obj i)) (hdim : ∀ i, finrank k (F.obj i) ≤ b)
    (hnb : ∀ (i : ℕ) (hi : i + 1 ≤ m),
      ¬Function.Bijective (FDMod.lin (F.map' i (i + 1) (by omega) hi)))
    (hm : 2 ^ b - 1 ≤ m) : FDMod.lin (F.map' 0 m (by omega) le_rfl) = 0 := by
  -- the rank of a composite of `2ⁿ - 1` maps is at most `b - n`
  have claim : ∀ n ≤ b, ∀ i j (hij : i ≤ j) (hjm : j ≤ m), j = i + (2 ^ n - 1) →
      rk k (FDMod.lin (F.map' i j hij hjm)) ≤ b - n := by
    intro n
    induction n with
    | zero =>
      intro _ i j hij hjm hj
      simp only [pow_zero, Nat.sub_self, add_zero] at hj
      subst hj
      rw [F.map'_self _ hjm, FDMod.lin_id]
      unfold rk
      rw [LinearMap.range_id, Submodule.restrictScalars_top, finrank_top]
      exact hdim _
    | succ n ih =>
      intro hn i j hij hjm hj
      have h1 := Nat.one_le_two_pow (n := n)
      have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      set p := i + (2 ^ n - 1) with hp
      obtain rfl : j = p + 1 + (2 ^ n - 1) := by omega
      rw [F.map'_comp i p _ (by omega) (by omega) hjm,
        F.map'_comp p (p + 1) _ (by omega) (by omega) hjm]
      simp only [FDMod.lin_comp]
      have hstep := haradaSai_step (k := k) (hind _) (hind _)
        (FDMod.lin (F.map' i p (by omega) (by omega)))
        (FDMod.lin (F.map' p (p + 1) (by omega) (by omega)))
        (FDMod.lin (F.map' (p + 1) (p + 1 + (2 ^ n - 1)) (by omega) hjm))
        (hnb p (by omega)) (c := b - n) (by omega)
        (ih (by omega) i p (by omega) (by omega) rfl)
        (ih (by omega) (p + 1) _ (by omega) hjm rfl)
      exact (by omega : ∀ x, x < b - n → x ≤ b - (n + 1)) _ hstep
  have h0 := claim b le_rfl 0 (2 ^ b - 1) (by omega) hm (by omega)
  rw [Nat.sub_self, Nat.le_zero] at h0
  have hz : FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm) = 0 := by
    unfold rk at h0
    have := Submodule.finrank_eq_zero.1 h0
    ext x
    have hx : FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm) x ∈
        (LinearMap.range (FDMod.lin (F.map' 0 (2 ^ b - 1) (by omega) hm))).restrictScalars k :=
      LinearMap.mem_range_self _ x
    rw [this] at hx
    rw [LinearMap.zero_apply]
    exact (Submodule.mem_bot k).1 hx
  rw [F.map'_comp 0 (2 ^ b - 1) m (by omega) hm le_rfl, FDMod.lin_comp, hz,
    LinearMap.comp_zero]

end LargeIndecomposable.AR
