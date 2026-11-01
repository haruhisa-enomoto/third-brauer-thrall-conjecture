module

public import LargeIndecomposable.Modules.KrullSchmidt.Fitting

/-!
# Decompositions from orthogonal idempotents

A finite family of orthogonal idempotent endomorphisms summing to the identity, with nonzero
indecomposable images, gives a decomposition (`Decomp.ofIdem`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- **A decomposition from orthogonal idempotents.** -/
def Decomp.ofIdem {E : FDMod k A} {ι : Type u} [Fintype ι] (π : ι → (E →ₗ[A] E))
    (hidem : ∀ i x, π i (π i x) = π i x) (horth : ∀ i j, i ≠ j → ∀ x, π j (π i x) = 0)
    (hsum : ∀ x, ∑ i, π i x = x)
    (hind : ∀ i, IsIndecMod A (LinearMap.range (π i)))
    (hnt : ∀ i, Nontrivial (LinearMap.range (π i))) : Decomp E where
  ι := ι
  obj i := FDMod.ofSub (LinearMap.range (π i))
  indec := hind
  nt := hnt
  inc i := show LinearMap.range (π i) →ₗ[A] E from (LinearMap.range (π i)).subtype
  proj i := show E →ₗ[A] LinearMap.range (π i) from
    LinearMap.codRestrict _ (π i) fun x ↦ LinearMap.mem_range_self _ x
  sum_id := by
    apply LinearMap.ext; intro x
    rw [LinearMap.sum_apply]
    exact hsum x
  retr i := by
    apply LinearMap.ext; rintro ⟨_, ⟨x, rfl⟩⟩
    apply Subtype.ext
    exact hidem i x
  orth i j h := by
    apply LinearMap.ext; rintro ⟨_, ⟨x, rfl⟩⟩
    apply Subtype.ext
    exact horth i j h x

end LargeIndecomposable.AR
