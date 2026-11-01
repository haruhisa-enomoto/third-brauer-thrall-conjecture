module

public import LargeIndecomposable.RayCategories.Basic.Residue
public import LargeIndecomposable.RepresentationType.DistributiveIdeals.FiniteIdeals
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteDistributiveHom
public import LargeIndecomposable.RayCategories.Basic.Basic

/-!
# The ray category of a distributive algebra

For split basic data of a finite-dimensional algebra `B` with distributive
ideal lattice over an infinite field, the ported BGRS theory gives the
distributive hom structure of the category of indecomposable projectives, and
the BGRS ray category satisfies the finite-ray-category axioms
(`SplitBasicData.isFiniteRayCategory`; Gabriel–Roiter 13.4). The input is that
the ideal lattice is finite (`finite_twoSidedIdeal_of_isDistribIdeals`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace LargeIndecomposable

open CategoryTheory Limits in
lemma rpow_eq_pow {C : Type*} [Category C] [HasZeroMorphisms C] {x : C} (e : End x) :
    ∀ n, rpow (show x ⟶ x from e) n = (show x ⟶ x from e ^ n)
  | 0 => rfl
  | n + 1 => by
    rw [rpow_succ, rpow_eq_pow e n, pow_succ']
    rfl

open CategoryTheory Limits in
/-- A finite ray category in the sense of the ported theory satisfies our axioms. -/
theorem isRayCategory_of_finiteRayCategory {C : Type*} [Category C] [HasZeroMorphisms C] [Finite C]
    [LargeIndecomposable.IsFiniteRayCategory0 C] : IsRayCategory C where
  skeletal _ _ h := LargeIndecomposable.IsFiniteRayCategory0.skeletal h
  finite_out _ := Set.toFinite _
  finite_in _ := Set.toFinite _
  finite_hom := LargeIndecomposable.IsFiniteRayCategory0.hom_finite
  id_ne_zero := LargeIndecomposable.IsFiniteRayCategory0.id_ne_zero
  nil x e he := by
    obtain ⟨n, -, hn⟩ := LargeIndecomposable.IsFiniteRayCategory0.endomorphism_nilpotent
      (show End x from e) he
    exact ⟨n, (rpow_eq_pow (show End x from e) n).trans hn⟩

namespace SplitBasicData

universe u v w

variable {k : Type u} [Field k] [Infinite k] {B : Type v} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {ι : Type w} [Fintype ι] [DecidableEq ι] (S : SplitBasicData k B ι)

/-- The distributive hom structure of a distributive algebra. -/
theorem distribHomStructure (hd : IsDistribIdeals B) :
    LargeIndecomposable.HasBGRSDistributiveHomStructure k S.toIdempotents.ProjectiveCategory := by
  have : Finite (TwoSidedIdeal B) := finite_twoSidedIdeal_of_isDistribIdeals k hd
  exact LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.bgrsDistributiveHomStructureOfComparable
    S.toIdempotents fun U V hU hV ↦
      LargeIndecomposable.SplitBasicIdempotents.ProjectiveCategory.finiteIdeal_homSubbimodule_comparable S.toIdempotents U V hU hV

/-- The BGRS ray category of a distributive algebra is a finite ray category. -/
theorem isFiniteRayCategory (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    LargeIndecomposable.IsFiniteRayCategory S.toIdempotents.RayCategory := by
  let _ := S.distribHomStructure hd
  infer_instance

/-- The ray category of a distributive algebra satisfies the ray axioms used here. -/
theorem isRayCategory (hd : IsDistribIdeals B) :
    letI := S.distribHomStructure hd
    IsRayCategory S.toIdempotents.RayCategory := by
  let _ := S.distribHomStructure hd
  have := S.isFiniteRayCategory hd
  exact isRayCategory_of_finiteRayCategory

end SplitBasicData

end LargeIndecomposable
