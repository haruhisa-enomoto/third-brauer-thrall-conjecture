module

public import LargeIndecomposable.AuslanderReiten.Lengths.FDMod

/-!
# Nonsplit extensions have smaller endomorphism rings

For a nonsplit short exact sequence `0 → L → M → N → 0`,
`dim End M < dim End (L ⊕ N)`, stated as
`dim End M + 1 ≤ dim End L + dim End N + dim Hom(L, N) + dim Hom(N, L)`
(`finrank_end_lt`; ASS VIII.2.8). The proof uses the left exactness of `Hom` in both variables;
the identity of `L` does not extend to `M`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {L M N : Type u} [AddCommGroup L] [Module A L] [Module k L] [IsScalarTower k A L]
  [FiniteDimensional k L]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] [FiniteDimensional k M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] [FiniteDimensional k N]

omit [FiniteDimensional k L] [FiniteDimensional k M] in
/-- `A`-linear maps as `k`-linear maps. -/
lemma restrictScalars_injective' :
    Function.Injective (LinearMap.restrictScalarsₗ k A L M k) :=
  fun f g h ↦ LinearMap.ext fun x ↦ LinearMap.congr_fun h x

instance finiteDimensional_hom : FiniteDimensional k (L →ₗ[A] M) :=
  Module.Finite.of_injective _ (restrictScalars_injective' (k := k) (A := A) (L := L) (M := M))

variable (k) in
/-- Postcomposition with an `A`-linear map. -/
def postcomp {X : Type u} [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
    (g : M →ₗ[A] N) : (X →ₗ[A] M) →ₗ[k] (X →ₗ[A] N) where
  toFun φ := g ∘ₗ φ
  map_add' φ ψ := LinearMap.comp_add _ _ _
  map_smul' c φ := LinearMap.ext fun x ↦ by simp

variable (k) in
/-- Precomposition with an `A`-linear map. -/
def precomp {Y : Type u} [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y]
    (f : L →ₗ[A] M) : (M →ₗ[A] Y) →ₗ[k] (L →ₗ[A] Y) where
  toFun ψ := ψ ∘ₗ f
  map_add' φ ψ := LinearMap.add_comp _ _ _
  map_smul' c φ := LinearMap.ext fun x ↦ by simp

/-- Maps vanishing on `L` factor through `N`. -/
lemma exists_factor {Y : Type u} [AddCommGroup Y] [Module A Y]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hg : Function.Surjective g)
    (hex : LinearMap.range f = LinearMap.ker g) (ψ : M →ₗ[A] Y) (hψ : ψ ∘ₗ f = 0) :
    ∃ ψ' : N →ₗ[A] Y, ψ' ∘ₗ g = ψ := by
  have hle : LinearMap.ker g ≤ LinearMap.ker ψ := by
    rw [← hex]
    rintro _ ⟨l, rfl⟩
    exact LinearMap.congr_fun hψ l
  refine ⟨(LinearMap.ker g).liftQ ψ hle ∘ₗ (g.quotKerEquivOfSurjective hg).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun m ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have : (g.quotKerEquivOfSurjective hg).symm (g m) = Submodule.Quotient.mk m := by
    apply (g.quotKerEquivOfSurjective hg).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [this]
  rfl

/-- Maps into `M` killed by `g` factor through `L`. -/
lemma exists_lift {X : Type u} [AddCommGroup X] [Module A X]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f)
    (hex : LinearMap.range f = LinearMap.ker g) (φ : X →ₗ[A] M) (hφ : g ∘ₗ φ = 0) :
    ∃ φ' : X →ₗ[A] L, f ∘ₗ φ' = φ := by
  have hmem : ∀ x, φ x ∈ LinearMap.range f := fun x ↦ by
    rw [hex]; exact LinearMap.congr_fun hφ x
  refine ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ φ.codRestrict _ hmem, ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have := congrArg Subtype.val
    ((LinearEquiv.ofInjective f hf).apply_symm_apply (φ.codRestrict _ hmem x))
  rw [LinearEquiv.ofInjective_apply] at this
  exact this

/-- **ASS VIII.2.8**: a nonsplit extension has a smaller endomorphism ring. -/
theorem finrank_end_lt (f : L →ₗ[A] M) (g : M →ₗ[A] N) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : LinearMap.range f = LinearMap.ker g)
    (hns : ¬∃ r : M →ₗ[A] L, r ∘ₗ f = LinearMap.id) :
    finrank k (M →ₗ[A] M) + 1 ≤ finrank k (L →ₗ[A] L) + finrank k (N →ₗ[A] N) +
      finrank k (L →ₗ[A] N) + finrank k (N →ₗ[A] L) := by
  -- `0 → Hom(M, L) → Hom(M, M) → Hom(M, N)`
  have h1 : finrank k (M →ₗ[A] M) ≤ finrank k (M →ₗ[A] L) + finrank k (M →ₗ[A] N) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (postcomp k (X := M) g)
    have hker : LinearMap.ker (postcomp k (X := M) g) ≤ LinearMap.range (postcomp k (X := M) f) := by
      intro φ hφ
      obtain ⟨φ', hφ'⟩ := exists_lift f g hf hex φ hφ
      exact ⟨φ', hφ'⟩
    have := Submodule.finrank_mono hker
    have := LinearMap.finrank_range_le (postcomp k (X := M) f)
    have := Submodule.finrank_le (LinearMap.range (postcomp k (X := M) g))
    omega
  -- `0 → Hom(N, L) → Hom(M, L) → Hom(L, L)`, not onto
  have h2 : finrank k (M →ₗ[A] L) + 1 ≤ finrank k (N →ₗ[A] L) + finrank k (L →ₗ[A] L) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (precomp k (Y := L) f)
    have hker : LinearMap.ker (precomp k (Y := L) f) ≤ LinearMap.range (precomp k (Y := L) g) := by
      intro ψ hψ
      obtain ⟨ψ', hψ'⟩ := exists_factor f g hg hex ψ hψ
      exact ⟨ψ', hψ'⟩
    have hlt : LinearMap.range (precomp k (Y := L) f) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop ↦ hns ?_
      have : (LinearMap.id : L →ₗ[A] L) ∈ LinearMap.range (precomp k (Y := L) f) := by
        rw [htop]; trivial
      obtain ⟨r, hr⟩ := this
      exact ⟨r, hr⟩
    have := Submodule.finrank_lt hlt.ne
    have := Submodule.finrank_mono hker
    have := LinearMap.finrank_range_le (precomp k (Y := L) g)
    omega
  -- `0 → Hom(N, N) → Hom(M, N) → Hom(L, N)`
  have h3 : finrank k (M →ₗ[A] N) ≤ finrank k (N →ₗ[A] N) + finrank k (L →ₗ[A] N) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (precomp k (Y := N) f)
    have hker : LinearMap.ker (precomp k (Y := N) f) ≤ LinearMap.range (precomp k (Y := N) g) := by
      intro ψ hψ
      obtain ⟨ψ', hψ'⟩ := exists_factor f g hg hex ψ hψ
      exact ⟨ψ', hψ'⟩
    have := Submodule.finrank_mono hker
    have := LinearMap.finrank_range_le (precomp k (Y := N) g)
    have := Submodule.finrank_le (LinearMap.range (precomp k (Y := N) f))
    omega
  omega

end LargeIndecomposable.AR
