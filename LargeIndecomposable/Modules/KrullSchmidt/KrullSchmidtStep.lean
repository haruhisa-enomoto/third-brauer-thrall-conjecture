module

public import LargeIndecomposable.DirectedAlgebras.Directing.Predecessor

/-!
# A Krull–Schmidt step

A nonzero indecomposable split summand of a direct sum of indecomposables is isomorphic to one of
the summands (`iso_summand_of_splitMono`). Consequently the source of an irreducible map into a
nonzero indecomposable `Z` is isomorphic to a summand of the chosen minimal right almost split map
into `Z` (`IsIrr.iso_chosenMin`), so irreducible predecessors are predecessors in `PredC`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- `X` and `Y` are isomorphic. -/
def IsoM (X Y : FDMod k A) : Prop := ∃ g : X ⟶ Y, Function.Bijective (FDMod.lin g)

/-- **Krull–Schmidt step.** -/
theorem iso_summand_of_splitMono {X E : FDMod k A} (hX : IndNT X) (d : Decomp E) (f : X ⟶ E)
    (r : E ⟶ X) (hfr : f ≫ r = 𝟙 X) : ∃ i, IsoM X (d.obj i) := by
  classical
  haveI := hX.2
  haveI := hX.1.isLocalRing (k := k)
  have hsum : (1 : Module.End A X) =
      ∑ i, (FDMod.lin r ∘ₗ FDMod.lin (d.inc i)) ∘ₗ (FDMod.lin (d.proj i) ∘ₗ FDMod.lin f) := by
    have h1 : (1 : Module.End A X) = FDMod.lin r ∘ₗ LinearMap.id ∘ₗ FDMod.lin f := (congrArg FDMod.lin hfr).symm
    rw [h1, ← d.sum_id]
    ext x
    simp [map_sum]
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one)
  obtain ⟨w, hw1, hw2⟩ := isUnit_iff_exists.1 hi
  -- `proj_i ∘ f` is split mono with retraction `w ∘ r ∘ inc_i`
  let g : X ⟶ d.obj i := (FDMod.ofLin (FDMod.lin (d.proj i) ∘ₗ FDMod.lin f))
  let ρ : d.obj i ⟶ X := (FDMod.ofLin (w ∘ₗ FDMod.lin r ∘ₗ FDMod.lin (d.inc i)))
  have hρg : FDMod.lin ρ ∘ₗ FDMod.lin g = LinearMap.id := by
    have : w * ((FDMod.lin r ∘ₗ FDMod.lin (d.inc i)) ∘ₗ (FDMod.lin (d.proj i) ∘ₗ FDMod.lin f)) = 1 :=
      hw2
    exact this
  have hρ := bijective_of_split (d.indec i) hX.2 ρ g hρg
  refine ⟨i, g, ?_⟩
  have hg : Function.LeftInverse (FDMod.lin ρ) (FDMod.lin g) := fun x ↦ LinearMap.congr_fun hρg x
  refine ⟨hg.injective, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hρ.2 (FDMod.lin ρ y)
  exact ⟨FDMod.lin ρ y, hρ.1 (by rw [hg])⟩

/-- **Sources of irreducible maps are summands of the minimal right almost split map.** -/
theorem IsIrr.iso_chosenMin [FiniteDimensional k A] {X Z : FDMod k A} (hX : IndNT X)
    (hZ : IndNT Z) {f : X ⟶ Z} (hf : IsIrr f) : ∃ i, IsoM X ((chosenMin Z hZ).d.obj i) := by
  obtain ⟨v, -, r, hr⟩ := hf.factor_rightAS (chosenMin Z hZ).hg
  exact iso_summand_of_splitMono hX _ v r hr

end LargeIndecomposable.AR
