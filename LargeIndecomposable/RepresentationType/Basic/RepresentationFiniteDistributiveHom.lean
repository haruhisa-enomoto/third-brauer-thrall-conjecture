module

public import LargeIndecomposable.RayCategories.Distributive.FiniteIdealHomChain
public import LargeIndecomposable.RayCategories.Distributive.KupischCyclicity
public import LargeIndecomposable.RepresentationType.Basic.RepresentationFiniteIdeals

@[expose] public section

/-!
# Representation-finiteness and distributive primitive-projective Hom spaces

A representation-finite finite-dimensional algebra has only finitely many
two-sided ideals.  Over an infinite field, the pencil argument makes every
pair of endpoint-stable primitive-projective Hom subspaces comparable.
Kupisch cyclicity then supplies transit or cotransit for every morphism, giving
the complete BGRS distributive-Hom package.
-/

set_option autoImplicit false
noncomputable section

namespace LargeIndecomposable.SplitBasicIdempotents

universe u v x

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]
variable {ι : Type x} [Fintype ι] [DecidableEq ι]

/-- Representation-finiteness over an infinite field supplies the complete
BGRS distributive-Hom package on the chosen primitive projectives. -/
theorem ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
    [Module.Finite k A] [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (hA : LargeIndecomposable.IsRepresentationFinite k A) :
    LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory := by
  letI : Finite (TwoSidedIdeal A) := hA.finite_twoSidedIdeal
  exact bgrsDistributiveHomStructureOfComparable S
    (fun U V hU hV ↦
      finiteIdeal_homSubbimodule_comparable S U V hU hV)

/-- The BGRS ray category attached to a representation-finite split-basic
algebra over an infinite field satisfies every finite-ray-category axiom. -/
theorem RayCategory.isFiniteRayCategory_of_isRepresentationFinite
    [Module.Finite k A] [Infinite k]
    (S : LargeIndecomposable.SplitBasicIdempotents
      (k := k) (A := A) (ι := ι))
    (hA : LargeIndecomposable.IsRepresentationFinite k A) :
    (letI : LargeIndecomposable.HasBGRSDistributiveHomStructure
        k S.ProjectiveCategory :=
      ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
        S hA
    LargeIndecomposable.IsFiniteRayCategory S.RayCategory) := by
  letI : LargeIndecomposable.HasBGRSDistributiveHomStructure
      k S.ProjectiveCategory :=
    ProjectiveCategory.bgrsDistributiveHomStructure_of_isRepresentationFinite
      S hA
  infer_instance

end LargeIndecomposable.SplitBasicIdempotents
