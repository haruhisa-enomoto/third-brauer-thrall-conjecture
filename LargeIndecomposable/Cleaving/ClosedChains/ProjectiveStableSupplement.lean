module

public import LargeIndecomposable.Cleaving.ClosedChains.StableSupplement
public import LargeIndecomposable.RayCategories.Distributive.SplitBasicRayCategory

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace LargeIndecomposable.ClosedZigzagTransfer

universe u x

variable {k : Type u} [Field k]
variable {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

open LargeIndecomposable.ClosedZigzag

/-- Concrete split-basic projective specialization of the exact stable
supplement boundary.  The canonical primitive-projective residue discharges
all endpoint equations, so supplement separation is literally the sole
remaining callback. -/
def projectiveStableChainHomBifunctorRetractionOfSupplements
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    [HasWellDefinedBGRSRayProduct S.ProjectiveCategory]
    [HasFiniteRayPathDepth (BGRSRayCategory S.ProjectiveCategory)]
    (t : RayClosedChain
      (C := BGRSRayCategory S.ProjectiveCategory))
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
  apply stableChainHomBifunctorRetractionOfSupplements t
    (fun X ↦ S.projectiveEndResidue
      ((stableChainRepresentativeLinearFunctor (k := k) t).obj X))
  · intro X a
    rw [S.projectiveEndResidue_eq_zero_iff_val_mem_jacobson]
    rw [← S.projectiveEnd_mem_jacobson_iff_val_mem_jacobson]
  · exact separated

end LargeIndecomposable.ClosedZigzagTransfer
