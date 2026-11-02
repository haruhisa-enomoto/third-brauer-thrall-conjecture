module

public import LargeIndecomposable.DirectedAlgebras.Directing.DirData

/-!
# Modules over directed algebras

Bricks are indecomposable (`isIndecMod_of_brick`). The projective `P(x) = A e_x` of a live point
is a nonzero brick (`DirData.projIndNT`). The support of a module is the set of points `y` with
`e_y M ≠ 0` (`DirData.Supp`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **Bricks are indecomposable.** -/
theorem isIndecMod_of_brick {M : FDMod k A}
    (h : ∀ φ : M ⟶ M, ∃ c : k, FDMod.lin φ = c • LinearMap.id) : IsIndecMod A M := by
  intro U V hUV
  let π : M →ₗ[A] M := U.subtype ∘ₗ Submodule.projectionOnto U V hUV
  obtain ⟨c, hc⟩ := h (FDMod.ofLin π)
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hπu : π u = u := by
    change ((Submodule.projectionOnto U V hUV u : U) : M) = u
    rw [Submodule.projectionOnto_apply_of_mem_left hUV hu]
  have hc1 : c = 1 := by
    have : π u = (c • LinearMap.id : M →ₗ[A] M) u := LinearMap.congr_fun hc u
    rw [hπu, LinearMap.smul_apply, LinearMap.id_apply] at this
    have h2 : (1 - c) • u = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact (sub_eq_zero.1 h3).symm
    · exact absurd h3 hu0
  rw [eq_bot_iff]
  intro v hv
  have hπv : π v = 0 := by
    change ((Submodule.projectionOnto U V hUV v : U) : M) = 0
    rw [Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩, Submodule.coe_zero]
  have : π v = (c • LinearMap.id : M →ₗ[A] M) v := LinearMap.congr_fun hc v
  rw [hπv, hc1, one_smul, LinearMap.id_apply] at this
  rw [← this]
  exact Submodule.zero_mem _

namespace DirData

variable [FiniteDimensional k A] (D : DirData k A)

/-- **Vertex projectives are nonzero bricks.** -/
theorem projIndNT (x : D.ι) (hx : x ∈ D.T) : IndNT (projE (k := k) (D.idem x)) := by
  refine ⟨isIndecMod_of_brick (projE_brick (D.idem x) (D.local_ x)), ?_⟩
  exact ⟨⟨⟨D.e x, e_mem (D.idem x)⟩, 0, fun h ↦ D.ne x hx (congrArg Subtype.val h)⟩⟩

/-- The support of a module. -/
def Supp (M : FDMod k A) : Set D.ι := {y | ∃ m : M, D.e y • m ≠ 0}

end DirData

end LargeIndecomposable.AR
