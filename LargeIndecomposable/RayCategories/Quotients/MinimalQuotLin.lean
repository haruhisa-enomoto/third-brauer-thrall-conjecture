module

public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisQuot
public import LargeIndecomposable.MultiplicativeBases.Twisted.MulBasisStd
public import LargeIndecomposable.Crowns.Basic.CrownReduction
public import LargeIndecomposable.RepresentationType.MinimalInfinite.Minimal
public import LargeIndecomposable.Cleaving.Functors.ThinCleaving
public import LargeIndecomposable.Cleaving.Functors.PathCatCleaving

/-!
# Proper residue categories are representation-finite

Let `A` be minimal representation-infinite with a twisted multiplicative basis
over a ray category `P` with cancellation. For a nonzero non-invertible `τ`,
`A/⟨τ⟩` is representation-finite, so `P/τ` has bounded chains; by Roiter's
theorem the twist of the quotient basis is exact, hence `A/⟨τ⟩ ≅ k(P/τ)`, and
the linearization `k(P/τ)` is representation-finite
(`RayQuiver.MulBasis.isRepresentationFinite_res`). In the language of BO13a,
`P` is a minimal representation-infinite ray category; cleaving functors into
`P/τ` can be used with the untwisted basis of `k(P/τ)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits RayCat

universe u

namespace RayQuiver

namespace MulBasis

variable {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] [Fintype P]
  [DecidableEq P] [LargeIndecomposable.IsFiniteRayCategory P] {k : Type u} [Field k] [Infinite k]
  {A : Type u} [Ring A] [Algebra k A] (B : MulBasis k P A)

include B in
/-- **`k(P/τ)` is representation-finite** for every nonzero non-invertible `τ`. -/
theorem isRepresentationFinite_res
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) :
    letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
    letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
    letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
    letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
    Statement.IsRepresentationFinite (Linearization (RayCat.Res τ) k) := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hfin := hmin _ (ideal_ne_bot (B := B) hτ0)
  have hCB := B.chainBounded_res hτ hfin
  obtain ⟨a', ha⟩ := ContourFn.exact_of_chainBounded (Additive kˣ) _ (RayCat.Res τ)
    (leftCancel_quotient _ hL) (rightCancel_quotient _ hR) hCB le_rfl (B.quot τ hτ).contourFn
  obtain ⟨e⟩ := (B.quot τ hτ).nonempty_algEquiv ha
  exact isRepresentationFinite_of_ringEquiv e.symm.toRingEquiv hfin

include B in
/-- **No representation-infinite thin cleaving diagram in `P/τ`.** -/
theorem not_thin_cleaving_res
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {V : Type} [Fintype V] [DecidableEq V] {T : ThinData V}
    (hD : ¬Statement.IsRepresentationFinite (Linearization (ThinCat T) k))
    (D : ThinFunctorData T (RayCat.Res τ)) (Ar : ThinArrows T)
    (hc : letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
      D.Cleaves Ar) : False := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hfin := B.isRepresentationFinite_res hmin hL hR τ hτ hτ0
  refine hD (isRepresentationFinite_of_cleaving (B := linMulBasis k (RayCat.Res τ))
    (F := D.functor) (D.isCleaving hc (leftCancel_quotient _ hL) (rightCancel_quotient _ hR))
    (fun _ _ _ ↦ rfl) hfin)

include B in
/-- **No representation-infinite path-category cleaving diagram in `P/τ`.** -/
theorem not_pathCat_cleaving_res
    (hmin : ∀ I : TwoSidedIdeal A, I ≠ ⊥ → Statement.IsRepresentationFinite (A ⧸ I.asIdeal))
    (hL : LeftCancel P) (hR : RightCancel P) {a b : P} (τ : a ⟶ b) (hτ : ¬IsIso τ)
    (hτ0 : τ ≠ 0) {Q : Type} [Quiver.{0} Q] [Fintype Q] [DecidableEq Q]
    [∀ a b : Q, Finite (a ⟶ b)] [Fact (LargeIndecomposable.Foundations.Quiver.IsAcyclic Q)]
    (hD : ¬Statement.IsRepresentationFinite (Linearization (PathCat Q) k))
    (F : PathCat Q ⥤ RayCat.Res τ) [F.PreservesZeroMorphisms] (hc : PathCat.ArrowCleaving F) :
    False := by
  letI := LargeIndecomposable.rayResidueCategory_isFiniteRayCategory τ hτ
  letI : IsRayCategory (RayCat.Res τ) := isRayCategory_of_finiteRayCategory
  letI : Fintype (RayCat.Res τ) := Fintype.ofFinite _
  letI : DecidableEq (RayCat.Res τ) := Classical.decEq _
  have hfin := B.isRepresentationFinite_res hmin hL hR τ hτ hτ0
  refine hD (isRepresentationFinite_of_cleaving (B := linMulBasis k (RayCat.Res τ)) (F := F)
    (PathCat.isCleaving_of_arrows hc (leftCancel_quotient _ hL) (rightCancel_quotient _ hR))
    (fun _ _ _ ↦ rfl) hfin)

end MulBasis

end RayQuiver

end LargeIndecomposable
