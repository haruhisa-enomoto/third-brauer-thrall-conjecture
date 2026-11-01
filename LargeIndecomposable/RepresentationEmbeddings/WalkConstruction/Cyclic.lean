module

public import LargeIndecomposable.RepresentationEmbeddings.WalkConstruction.Monomial

/-!
# The hereditary case `Ã_n`

The path algebra of the cycle quiver `D_w` (a cycle with at least one source,
type `Ã_{n+1}`) with the identity presentation is monomial band data: there
are no relations, and the identity walk is primitive because the labels of
its arrows are pairwise distinct (`Walk.cyclicBand`). So Construction 3.9
gives a controlled embedding for these algebras.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open FinQuiver

universe u

namespace Walk

variable (k : Type u) [Field k]

lemma primitive_id (n : ℕ) (ε : Fin n → Bool) :
    Primitive (FinQuiver.Hom.id (cycleQuiver n ε)) (cycleCoords n ε) := by
  intro τ hτ
  refine ⟨0, fun h ↦ hτ ?_⟩
  have h1 := congrArg Prod.fst h
  change (cycleCoords n ε).eix.symm (0 + τ) = (cycleCoords n ε).eix.symm 0 at h1
  simpa using (cycleCoords n ε).eix.symm.injective h1

/-- The path algebra of a cycle with a source is monomial band data. -/
def cyclicBand (n : ℕ) (ε : Fin n → Bool) :
    MonomialBand k ((cycleQuiver n ε).PathAlgebra k) where
  n := n
  ε := ε
  Q := cycleQuiver n ε
  p := FinQuiver.Hom.id _
  locInj := ⟨fun _ _ _ h ↦ h, fun _ _ _ h ↦ h⟩
  primitive := primitive_id n ε
  π := AlgHom.id k _
  surj := Function.surjective_id
  P := ∅
  ker_le z hz := by
    rw [show z = 0 from hz]
    exact Submodule.zero_mem _
  band _ _ _ _ := Set.notMem_empty _

end Walk

end LargeIndecomposable
