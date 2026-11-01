module

public import LargeIndecomposable.Quivers.Representations.ExtCount

/-!
# The Euler characteristic of the cocycle complex

For a family `F` of relations and representations `X`, `Y` killed by it, the complex
`⊕ᵢ Hom(Xᵢ, Yᵢ) → ⊕_α Hom(X_{s α}, Y_{t α}) → ⊕_r Hom(X_{s r}, Y_{t r})` (coboundaries, then
relation blocks) has cohomology `Hom(X, Y)`, `H¹` (cocycles modulo coboundaries) and `H²` (the
cokernel of the block map). Its Euler characteristic is the bilinear form of `F`
(`euler_cocycle_complex`):
`dim Hom - dim H¹ + dim H² = Σᵢ xᵢ yᵢ - Σ_α x_{s α} y_{t α} + Σ_r x_{s r} y_{t r}`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.FinQuiver.Ext

open Module

universe u

variable {k : Type u} [Field k] {D : FinQuiver} {X Y : Rep k D} (F : RelFam D k)
variable [∀ i, FiniteDimensional k (X.obj i)] [∀ i, FiniteDimensional k (Y.obj i)]

/-- The dimension of `H¹`: cocycles modulo coboundaries. -/
def dimH1 : ℤ :=
  finrank k (cocycles F (X := X) (Y := Y)) - finrank k (LinearMap.range (cobL (X := X) (Y := Y)))

/-- The dimension of `H²`: the cokernel of the block map. -/
def dimH2 : ℤ :=
  (∑ r, finrank k (X.obj (F.s r)) * finrank k (Y.obj (F.t r)) : ℕ) -
    finrank k (LinearMap.range (blocksL F (X := X) (Y := Y)))

/-- **The Euler characteristic of the cocycle complex is the bilinear form of `F`.** -/
theorem euler_cocycle_complex :
    (finrank k (LinearMap.ker (cobL (X := X) (Y := Y))) : ℤ) - dimH1 F (X := X) (Y := Y) +
        dimH2 F (X := X) (Y := Y) =
      (∑ i, finrank k (X.obj i) * finrank k (Y.obj i) : ℕ) -
        (∑ α : D.A, finrank k (X.obj (D.src α)) * finrank k (Y.obj (D.tgt α)) : ℕ) +
        (∑ r, finrank k (X.obj (F.s r)) * finrank k (Y.obj (F.t r)) : ℕ) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (blocksL F (X := X) (Y := Y))
  have h2 := LinearMap.finrank_range_add_finrank_ker (cobL (X := X) (Y := Y))
  have hdata : finrank k (Data X Y) =
      ∑ α : D.A, finrank k (X.obj (D.src α)) * finrank k (Y.obj (D.tgt α)) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  have hdom : finrank k (∀ i, X.obj i →ₗ[k] Y.obj i) =
      ∑ i, finrank k (X.obj i) * finrank k (Y.obj i) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  unfold dimH1 dimH2 cocycles
  rw [← hdata, ← hdom]
  push_cast
  omega

/-- The block map is onto exactly when `H²` vanishes. -/
lemma dimH2_eq_zero_iff :
    dimH2 F (X := X) (Y := Y) = 0 ↔ Function.Surjective (blocksL F (X := X) (Y := Y)) := by
  have hcod : finrank k (∀ r : Fin F.m, X.obj (F.s r) →ₗ[k] Y.obj (F.t r)) =
      ∑ r, finrank k (X.obj (F.s r)) * finrank k (Y.obj (F.t r)) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_linearMap]
  unfold dimH2
  rw [← LinearMap.range_eq_top, ← hcod]
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    omega
  · intro h
    rw [h, finrank_top]
    simp

end LargeIndecomposable.FinQuiver.Ext
