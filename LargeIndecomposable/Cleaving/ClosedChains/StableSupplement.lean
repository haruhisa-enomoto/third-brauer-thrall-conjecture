module

public import LargeIndecomposable.Cleaving.ClosedChains.StableClosedZigzag
public import LargeIndecomposable.Cleaving.ClosedChains.SupplementRetraction

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {C : Type x} [Category.{u} C] [Preadditive C] [Linear k C]
variable [HasWellDefinedBGRSRayProduct C]
variable [HasFiniteRayPathDepth (BGRSRayCategory C)]

open LargeIndecomposable.ClosedZigzag

/-- Exact compiled boundary for the BGRS 3.7(b) cleavage using its actual
stable path representatives.  All enriched naturality and linear-algebra
choices are discharged.  The only supplied source statement is precisely
the supplement nonmembership proved in 3.7: each path generator is outside
the sum of its endpoint-Jacobson layer and all forbidden cross composites. -/
def stableChainHomBifunctorRetractionOfSupplements
    (t : RayClosedChain (C := BGRSRayCategory C))
    (residue : ∀ X : LinearPathCategory.Category k
        (Vertex (t.length - 1))ᵒᵖ,
      End ((stableChainRepresentativeLinearFunctor (k := k) t).obj X) →ₐ[k] k)
    (residue_zero : ∀
      (X : LinearPathCategory.Category k (Vertex (t.length - 1))ᵒᵖ)
      (a : End ((stableChainRepresentativeLinearFunctor (k := k) t).obj X)),
      residue X a = 0 ↔
        a ∈ Ring.jacobson
          (End ((stableChainRepresentativeLinearFunctor (k := k) t).obj X)))
    (separated : ∀
      {X Y : LinearPathCategory.Category k (Vertex (t.length - 1))ᵒᵖ}
      (p : Quiver.Path (LinearPathCategory.vertex Y)
        (LinearPathCategory.vertex X)),
      (stableChainRepresentativeLinearFunctor (k := k) t).map
          (LinearPathCategory.pathHom p) ∉
        pathSupplementObstruction (k := k)
          (stableChainRepresentativeLinearFunctor (k := k) t) p) :
    HomBifunctorRetraction (k := k)
      (stableChainRepresentativeLinearFunctor (k := k) t) := by
  have hn : 2 ≤ t.length - 1 := by
    have := t.length_ge_three
    omega
  let h : ClosedZigzagSupplementData (k := k) (t.length - 1) hn
      (stableChainRepresentativeLinearFunctor (k := k) t) :=
    { residue := residue
      residue_zero := residue_zero
      separated := separated }
  exact h.homBifunctorRetraction

end LargeIndecomposable.ClosedZigzagTransfer
