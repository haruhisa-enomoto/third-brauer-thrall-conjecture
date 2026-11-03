module

public import LargeIndecomposable.Coverings.UniversalCover.PieceKills
public import LargeIndecomposable.Coverings.Pieces.PairKills

/-!
# Covering data from a convex piece of the universal cover

If `A ≅ k(P)` for a finite ray category `P` whose fundamental group is
torsion-free (free, by Bongartz's Theorem 2), a Kronecker pair on a finite
convex piece `S` of the universal cover whose two generating modules respect
the relations of the cover gives covering data with a Kronecker pair for `A`
(`RayCat.pairCoveringData`). This reduces alternative (2′) of Theorem 3.10 to
a statement about `P̃`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits FinQuiver Covering

universe u

namespace RayCat

open Cover RayQuiver

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] {x₀ : P}

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-- Covering data with a Kronecker pair from a convex piece of the universal
cover. -/
def pairCoveringData (e : Linearization P k ≃ₐ[k] A)
    (htf : ∀ g : Pi1 x₀, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (S : Finset (Cover x₀)) (hS : Convex (S : Set (Cover x₀)))
    (K : KroneckerPair k (pieceQuiver S))
    (supp : ∀ i, Nontrivial (K.P.obj i) ∨ Nontrivial (K.Q₀.obj i))
    (h₁ : RespectsCover (K.functor.obj (Kron.Sminus k)))
    (h₂ : RespectsCover (K.functor.obj (P1K k))) : PairCoveringData k A :=
  PairCoveringData.mk' (pieceQuiver S) (quiver P) (pieceProj S) (pieceProj_locInj S)
    (coverPieceData S htf) K supp ((e : Linearization P k →ₐ[k] A).comp (linPres P k))
    (e.surjective.comp (linPres_surjective P k))
    (fun z hz ↦ pdAct_eq_zero_of_linPres hS h₁ z (e.injective (by simpa using hz)))
    (fun z hz ↦ pdAct_eq_zero_of_linPres hS h₂ z (e.injective (by simpa using hz)))

end RayCat

end LargeIndecomposable
