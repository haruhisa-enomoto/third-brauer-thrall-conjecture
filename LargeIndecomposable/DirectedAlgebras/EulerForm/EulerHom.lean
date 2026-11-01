module

public import LargeIndecomposable.Modules.Homological.Ext
public import LargeIndecomposable.DirectedAlgebras.Directing.Cartan

/-!
# Hom minus Ext for presentations of projective dimension one

For a free presentation `Aⁿ¹ → Aⁿ⁰ → Z → 0` with free relation rows, maps `Z → W` are the tuples
in `Wⁿ⁰` killed by the relations (`homEvalEquiv`), and `Ext¹(Z, W) = Wⁿ¹ / F Wⁿ⁰`. Hence
`dim Hom(Z, W) - dim Ext¹(Z, W) = (n₀ - n₁) dim W` (`finrank_hom_sub_ext1`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {Z : Type u} [AddCommGroup Z] [Module A Z]
variable {W : Type u} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]

/-- Evaluation at the generators. -/
def FreePres.evalGen (P : FreePres A Z) : (Z →ₗ[A] W) →ₗ[k] (Fin P.n₀ → W) where
  toFun v j := v (P.z j)
  map_add' v v' := rfl
  map_smul' c v := rfl

lemma FreePres.range_evalGen (P : FreePres A Z) :
    LinearMap.range (P.evalGen (k := k) (W := W)) = LinearMap.ker (relMapLin (k := k) (W := W) P.F) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact P.relMap_hom v
  · intro hw
    obtain ⟨v, hv⟩ := P.lift w hw
    exact ⟨v, funext hv⟩

lemma FreePres.evalGen_injective (P : FreePres A Z) :
    Function.Injective (P.evalGen (k := k) (W := W)) := fun v v' h ↦
  P.hom_ext fun j ↦ congrFun h j

/-- **`dim Hom(Z, W) - dim Ext¹(Z, W) = (n₀ - n₁) dim W`.** -/
theorem finrank_hom_sub_ext1 [FiniteDimensional k W] (P : FreePres A Z) (hF : P.Free) :
    (finrank k (Z →ₗ[A] W) : ℤ) - finrank k (Ext1 (k := k) W P) =
      ((P.n₀ : ℤ) - P.n₁) * finrank k W := by
  have h1 : finrank k (Z →ₗ[A] W) = finrank k (LinearMap.ker (relMapLin (k := k) (W := W) P.F)) := by
    rw [← P.range_evalGen, LinearMap.finrank_range_of_inj P.evalGen_injective]
  have h2 := LinearMap.finrank_range_add_finrank_ker (relMapLin (k := k) (W := W) P.F)
  have h3 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (relMapLin (k := k) (W := W) P.F))
  rw [(P.ext1EquivCoker hF).finrank_eq]
  have e0 : finrank k (Fin P.n₀ → W) = P.n₀ * finrank k W := by
    rw [Module.finrank_pi_fintype]; simp
  have e1 : finrank k (Fin P.n₁ → W) = P.n₁ * finrank k W := by
    rw [Module.finrank_pi_fintype]; simp
  rw [e0] at h2
  rw [e1] at h3
  have : (finrank k ((Fin P.n₁ → W) ⧸ LinearMap.range (relMapLin (k := k) (W := W) P.F)) : ℤ) =
      P.n₁ * finrank k W - finrank k (LinearMap.range (relMapLin (k := k) (W := W) P.F)) := by
    have h3' : ((finrank k ((Fin P.n₁ → W) ⧸ LinearMap.range (relMapLin (k := k) (W := W) P.F)) +
        finrank k (LinearMap.range (relMapLin (k := k) (W := W) P.F)) : ℕ) : ℤ) =
        ((P.n₁ * finrank k W : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at h3'
    linarith
  rw [this, h1]
  have h2' : ((P.n₀ * finrank k W : ℕ) : ℤ) =
      finrank k (LinearMap.range (relMapLin (k := k) (W := W) P.F)) +
        finrank k (LinearMap.ker (relMapLin (k := k) (W := W) P.F)) := by exact_mod_cast h2.symm
  push_cast at h2'
  linarith

end LargeIndecomposable.AR
