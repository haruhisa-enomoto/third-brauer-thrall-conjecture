module

public import LargeIndecomposable.BongartzTheorem.SimplyConnectedCover.CoverAcyclic
public import LargeIndecomposable.Coverings.UniversalCover.LocalSC
public import LargeIndecomposable.Coverings.UniversalCover.CoverCountable

/-!
# Local simple connectivity of the universal cover

For a finite connected chain-bounded ray category with cancellation, every cocycle on a finite
convex set of the universal cover is a coboundary there (`coverLocalSC_of_chainBounded`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.RayCat

open CategoryTheory Limits Cover

/-- Local simple connectivity of the cover. -/
def CoverLocalSC {P : Type} [Category.{0} P] [HasZeroMorphisms P] [IsRayCategory P] (x₀ : P) :
    Prop :=
  ∀ D : Set (Cover x₀), D.Finite → ConvexR D → ∀ c : ArrowWeight (Cover x₀),
    IsCocycleOn D c → IsCoboundaryOn D c

/-- **Local simple connectivity for chain-bounded categories.** -/
theorem coverLocalSC_of_chainBounded (hS : SimplyConnectedStageStep) (P : Type) [Category.{0} P]
    [HasZeroMorphisms P] [IsRayCategory P] [Finite P] [Fintype P] [DecidableEq P]
    (hL : LeftCancel P) (hR : RightCancel P) (hCB : ChainBounded P)
    (hcon : IsConnected (FundGroupoid P)) (x₀ : P) : CoverLocalSC x₀ := by
  letI := isFiniteRayCategory0_of_ray (C := P)
  have hfree : IsFreeGroup (End (vtx x₀)) := isFreeGroup_end_fund _ P hL hR hCB hcon le_rfl _
  have hℓ : ∀ y : P, Nonempty (vtx x₀ ⟶ vtx y) := fun y ↦
    nonempty_hom_of_preconnected_groupoid _ _
  obtain ⟨H, _, _, φ, hLF⟩ := exists_loopFree_gcover x₀ hfree fun y ↦ (hℓ y).some
  letI := isFiniteRayCategory0_of_ray (C := GCover (volt (fun y ↦ (hℓ y).some) φ))
  have hgood := coverGood_of_stage hS _ (GCover (volt (fun y ↦ (hℓ y).some) φ))
    (leftCancel_gcover hL) (rightCancel_gcover hR) (chainBounded_gcover hCB) hLF le_rfl ⟨x₀, 1⟩
  have hcf := cycleFree_of_gcover hgood.1
  have hint := intervalFinite_of_gcover hgood.2
  intro D hD hDc c hc
  exact isCoboundaryOn_of_global (leftCancel_cover hL) (rightCancel_cover hR)
    (chainBounded_cover hCB) hint (fun x p ↦ hcf _ p) (fun c hc ↦ isCoboundary_cover c hc)
    hD hDc c hc

end LargeIndecomposable.RayCat
