module

public import LargeIndecomposable.AuslanderReiten.AlmostSplit.Projective
public import LargeIndecomposable.AuslanderReiten.Lengths.FDMod

/-!
# Right almost split maps in `FDMod k A`

`IsRightAS g`: `g : E ⟶ Z` is not a split epimorphism, and every map into `Z` that is
not a split epimorphism factors through `g`. Over a finite-dimensional algebra, every
object with local endomorphism ring has one (`FDMod.exists_rightAS`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable.AR

open CategoryTheory Module

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

instance [FiniteDimensional k A] : FiniteDimensional k (DA k A) :=
  inferInstanceAs (FiniteDimensional k (A →ₗ[k] k))

/-- `g` is right almost split. -/
def IsRightAS {E Z : FDMod k A} (g : E ⟶ Z) : Prop :=
  (¬∃ s : Z ⟶ E, s ≫ g = 𝟙 Z) ∧
    ∀ (W : FDMod k A) (u : W ⟶ Z), (¬∃ s : Z ⟶ W, s ≫ u = 𝟙 Z) → ∃ v : W ⟶ E, v ≫ g = u

/-- An `A`-submodule of a finite-dimensional module, as an object. -/
abbrev FDMod.ofSub {P : FDMod k A} (U : Submodule A P) : FDMod k A where
  carrier := U
  isFD := inferInstanceAs (FiniteDimensional k (U.restrictScalars k))

/-- A submodule of `Z × V` with `V` finite-dimensional, as an object. -/
abbrev FDMod.ofSubProd (Z : FDMod k A) (V : Type u) [AddCommGroup V] [Module A V] [Module k V]
    [IsScalarTower k A V] [FiniteDimensional k V] (U : Submodule A (Z × V)) : FDMod k A where
  carrier := U
  isFD := inferInstanceAs (FiniteDimensional k (U.restrictScalars k))

/-- **Every object with local endomorphism ring has a right almost split map.** -/
theorem FDMod.exists_rightAS [FiniteDimensional k A] (Z : FDMod k A)
    [IsLocalRing (Module.End A Z)] : ∃ (E : FDMod k A) (g : E ⟶ Z), IsRightAS g := by
  by_cases hZ : IsFreeSummand A Z
  · obtain ⟨U, hU1, hU2⟩ := exists_rightAlmostSplit_of_freeSummand.{u, u, u, u} (k := k) hZ
    refine ⟨FDMod.ofSub U, FDMod.ofLin U.subtype,
      fun ⟨s, hs⟩ ↦ hU1 ⟨FDMod.lin s, (FDMod.comp_eq_id_iff _ _).1 hs⟩, fun W v hv ↦ ?_⟩
    obtain ⟨t, ht⟩ := hU2 W (FDMod.lin v) fun ⟨s, hs⟩ ↦
      hv ⟨FDMod.ofLin s, (FDMod.comp_eq_id_iff _ _).2 hs⟩
    exact ⟨FDMod.ofLin t, (FDMod.comp_eq_iff _ _ _).2 ht⟩
  · obtain ⟨P⟩ := FreePres.exists k A Z
    obtain ⟨E, hE1, hE2⟩ := exists_rightAlmostSplit.{u, u, u, u} (k := k) hZ P
    refine ⟨FDMod.ofSubProd Z (Fin P.n₁ → DA k A) E, FDMod.ofLin (LinearMap.fst A Z _ ∘ₗ E.subtype),
      fun ⟨s, hs⟩ ↦ hE1 ⟨FDMod.lin s, (FDMod.comp_eq_id_iff _ _).1 hs⟩, fun W v hv ↦ ?_⟩
    obtain ⟨t, ht⟩ := hE2 W (FDMod.lin v) fun ⟨s, hs⟩ ↦
      hv ⟨FDMod.ofLin s, (FDMod.comp_eq_id_iff _ _).2 hs⟩
    exact ⟨FDMod.ofLin t, (FDMod.comp_eq_iff _ _ _).2 ht⟩

end LargeIndecomposable.AR
