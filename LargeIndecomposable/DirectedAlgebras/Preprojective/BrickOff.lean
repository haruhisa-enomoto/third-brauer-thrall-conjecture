module

public import LargeIndecomposable.DirectedAlgebras.Preprojective.CriticalAbstract

/-!
# Roots off a point are bricks

Let `D` be a directed algebra with a sincere directing module whose indecomposables killed by
any `e_i` are rigid (`RigidOff`). A module of minimal endomorphism dimension with dimension
vector `x ≥ 0`, `x_a = 0`, is rigid (`rigid_of_minEnd`), so `dim End ≤ ⟨x, x⟩`
(`hom_le_euler`). Hence a root off a point is the dimension vector of a module with
one-dimensional endomorphism algebra (`exists_brick_off`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

namespace DirData

variable {D : DirData k A} {U : FDMod k A}

/-- **A root off a point is the dimension vector of a brick.** -/
theorem exists_brick_off (hT : ∀ x, x ∈ D.T) (hU : Directing U) (hs : Sincere D U)
    (hR : RigidOff D) (a : D.ι) (x : D.ι → ℤ) (hx : Forms.UnitForm.Pos x) (hxa : x a = 0)
    (h1 : euler D x x = 1) :
    ∃ V : FDMod k A, dimZ D V = x ∧ finrank k (V →ₗ[A] V) = 1 := by
  obtain ⟨V, hV, hmin⟩ := exists_minEnd (k := k) (D := D) hT (fun i ↦ (x i).toNat)
  have hVx : dimZ D V = x := by
    rw [hV]
    funext i
    exact Int.toNat_of_nonneg (hx.1 i)
  have hVa : dimZ D V a = 0 := by rw [hVx, hxa]
  have hrig := rigid_of_minEnd hR hVa hmin
  have hle := hom_le_euler (D := D) hT hU hs hrig
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx.2 (funext h)
  have hnt : Nontrivial V := nontrivial_of_dimZ (i := i) (by rwa [hVx])
  have hpos := finrank_end_pos hnt
  rw [hVx, h1] at hle
  exact ⟨V, hVx, by omega⟩


end DirData

end LargeIndecomposable.AR
